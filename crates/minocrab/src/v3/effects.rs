//! THE EFFECT CHOKE POINT: the one place the ambient guard is read, and the
//! only route to the raw emitters whose meaning depends on it.
//!
//! A ZKIR circuit has no control flow. `c.when(g, |c| body)` runs the body
//! unconditionally and relies on every EFFECT emitted inside it — a witness
//! read, a public-transcript read, an Impact op, a check — consulting the
//! guard stack. Before this module that consultation was made method by
//! method: `witness` did, `witness_guarded` did not; `assert` did,
//! `assert_eq` / `assert_bits` / `assert_boolean` did not;
//! `public_transcript_input_guarded` was fixed to, one commit after the AA
//! manager port found it. Each was a cell in a table nothing checked, and
//! each miss is invisible to a differential on an honest preimage — the
//! guard only matters on the path that was not taken.
//!
//! Now there is one table entry. [`EffectGuard`] is the resolved guard; its
//! field is private to this module, so the only way to obtain one is
//! [`Circuit3::effect_guard`], which is the only reader of the ambient
//! stack. Every `emit_*` below demands one. The parent module therefore has
//! no spelling of "emit an effect under a guard that skipped the scope": a
//! public entry point either resolves through `effect_guard` or it cannot
//! call an emitter at all. A test at the bottom pins the other half — that
//! the parent reaches none of the raw builder emitters directly.
//!
//! Semantics per effect, all compactc's own lowering for `if`:
//!
//! - READS (`private_input`, `public_input`) carry the guard as the
//!   instruction's own operand: false ⇒ the type's default, transcript not
//!   consumed.
//! - IMPACT carries it as its guard operand.
//! - CHECKS have no guard operand in ZKIR, so the guard selects the value
//!   checked: `assert(x)` becomes `assert(select(g, x, 1))`;
//!   `constrain_bits(w, k)` becomes `constrain_bits(select(g, w, 0), k)`,
//!   likewise `constrain_to_boolean`; `constrain_eq(a, b)` — which has no
//!   value to select — becomes `test_eq` + a guarded `assert`, the shape
//!   compactc emits for `assert(a == b)` inside a branch. Straight-line
//!   circuits (no ambient guard) emit exactly what they did before: the
//!   direct instruction, no select.

use minocrab_ir::v3::{Arg, IrType, Val};
use minocrab_ir::Fr;

use super::{AssertMessage, Circuit3, DeferredImpact, ImpactElem};

/// A guard RESOLVED against the ambient scope — `None` for straight-line
/// code, otherwise the conjunction of the scope and whatever explicit guard
/// the caller passed.
///
/// The field is private to this module on purpose: only
/// [`Circuit3::effect_guard`] builds one, so holding an `EffectGuard` is
/// proof the ambient stack was consulted.
#[derive(Clone, Copy)]
pub(super) struct EffectGuard(Option<Arg>);

impl Circuit3 {
    /// The effective ambient guard, if any. Private to this module: the
    /// parent constructs scopes (push/pop) but never READS the stack —
    /// reading it is what an effect does, and effects come through here.
    fn ambient(&self) -> Option<Val> {
        self.guards.last().copied()
    }

    /// Resolve the guard an effect will carry: the ambient scope conjoined
    /// with `explicit`, if the caller passed one.
    ///
    /// The straight-line immediate `1` YIELDS to the ambient guard, which
    /// is what makes a plain method call inside [`Circuit3::when`] pick the
    /// scope up for free. An explicit non-trivial guard inside a scope is
    /// conjoined with it — correct, but it costs a `cond_select` per call,
    /// so the plain form is the one to use inside a scope. Outside any
    /// scope the explicit guard passes through untouched, so straight-line
    /// callers are byte-for-byte what they were.
    pub(super) fn effect_guard(&mut self, explicit: Option<Arg>) -> EffectGuard {
        // A NAMED constant 1 (`c.constant(1)`, the `one` every straight-line
        // port threads the way compactc does) is the immediate 1: it yields
        // to the ambient scope exactly as the literal does, instead of
        // costing a `cond_select(ambient, one, 0)` that conjoins nothing.
        let explicit = match explicit {
            Some(Arg::Val(v)) if self.b.immediate_of(v) == Some(Fr::from(1u64)) => {
                Some(Arg::Imm(Fr::from(1u64)))
            }
            other => other,
        };
        EffectGuard(match (self.ambient(), explicit) {
            (None, explicit) => explicit,
            (Some(ambient), None) => Some(Arg::Val(ambient)),
            (Some(ambient), Some(Arg::Imm(imm))) if imm == Fr::from(1u64) => {
                Some(Arg::Val(ambient))
            }
            // A constant guard OTHER than 1 is either always-off or
            // nonsense; `ambient && imm` is still the honest answer.
            (Some(ambient), Some(explicit)) => Some(Arg::Val(self.b.cond_select(
                ambient,
                explicit,
                Fr::from(0u64),
            ))),
        })
    }

    /// The value a CHECK sees: `w` itself in straight-line code, else
    /// `select(guard, w, off)` so the check holds trivially where the guard
    /// is false. `off` is whatever satisfies the check (1 for an assert, 0
    /// for a range or boolean constraint).
    fn checked_value(&mut self, guard: EffectGuard, w: Val, off: u64) -> Val {
        match guard.0 {
            None => w,
            Some(Arg::Imm(imm)) if imm == Fr::from(1u64) => w,
            Some(g) => self.b.cond_select(g, w, Fr::from(off)),
        }
    }

    // --- scopes ------------------------------------------------------------------------------

    /// Enter a scope: push `cond` conjoined with the current top. NESTING is
    /// Compact's `&&` — the inner scope's guard is `select(outer, inner, 0)`,
    /// computed ONCE on entry rather than per operation, which is exactly
    /// the shape compactc emits for `if (a && b)`.
    pub(super) fn push_guard(&mut self, cond: Val) {
        let effective = match self.ambient() {
            Some(outer) => self.b.cond_select(outer, cond, Fr::from(0u64)),
            None => cond,
        };
        self.guards.push(effective);
    }

    pub(super) fn pop_guard(&mut self) {
        self.guards.pop();
    }

    // --- deferred emission: the hooks ------------------------------------------------

    /// Queue `ops` for emission after the body, under the ambient guard AS
    /// IT IS NOW. The one other reader of the ambient stack besides
    /// [`Circuit3::effect_guard`], and for the same reason: attachment is
    /// where the hook's guard is decided, and the scope that decides it is
    /// gone by the time the hook is emitted.
    #[track_caller]
    pub(super) fn defer_impact(&mut self, ops: Vec<Vec<ImpactElem>>) {
        self.refuse_on_chain_in_private_scope("a hook (`c.then`)");
        let guard = self.ambient();
        self.deferred.push(DeferredImpact { guard, ops });
    }

    /// Emit every attached program in attachment order, each under the
    /// guard captured when it was attached. Called by [`Circuit3::finish`]
    /// (and by `entry`, right after the body, so the disclosure record
    /// lists the hooks' operands before the outputs). Must run OUTSIDE any
    /// scope: the captured guard already carries the scope.
    pub fn flush_deferred(&mut self) {
        assert!(
            self.guards.is_empty(),
            "hooks are flushed after the body, outside every `when` scope"
        );
        let deferred = std::mem::take(&mut self.deferred);
        for DeferredImpact { guard, ops } in deferred {
            let guard = EffectGuard(guard.map(Arg::Val));
            for op in &ops {
                let args = self.impact_args(op);
                self.emit_impact(guard, &args);
            }
        }
    }

    // --- the raw emitters, one each ------------------------------------------------------

    /// A READ under the constant-true guard is an unguarded read: `guard:
    /// null`, which is what compactc emits for the witnesses of a
    /// straight-line cross-contract call (its ops carry the `0x01`, its
    /// reads carry nothing). Same meaning, and the byte compactc chose.
    fn read_guard(guard: EffectGuard) -> Option<Arg> {
        match guard.0 {
            Some(Arg::Imm(imm)) if imm == Fr::from(1u64) => None,
            g => g,
        }
    }

    pub(super) fn emit_private_input(&mut self, ty: IrType, guard: EffectGuard) -> Val {
        self.witnesses += 1;
        self.b.private_input(ty, Self::read_guard(guard))
    }

    /// The one build-time refusal of this module: an ON-CHAIN effect inside
    /// [`Circuit3::when_private`]. Whether an Impact op or a public read ran
    /// is visible on chain, so the private condition would be disclosed by
    /// it; compactc's own rule, and the last rung of the rejection ladder
    /// here because the scope is dynamic (recorded in notes/contract-api.org
    /// §"Panics that could NOT become compile errors").
    #[track_caller]
    fn refuse_on_chain_in_private_scope(&self, what: &str) {
        if self.private_scopes > 0 {
            panic!(
                "{what} inside `when_private`: whether it ran is visible on chain, so the \
                 private condition would be disclosed. Either disclose the condition first \
                 (`let cond = cond.disclose_as::<L>(c);`, with `L` in the circuit's \
                 `Discloses<(..)>`) and use `when`, or move the effect out of the private \
                 scope — a `when_private` body may only witness and check."
            );
        }
    }

    #[track_caller]
    pub(super) fn emit_public_input(&mut self, ty: IrType, guard: EffectGuard) -> Val {
        self.refuse_on_chain_in_private_scope("a public-transcript read");
        self.b.public_input(ty, Self::read_guard(guard))
    }

    #[track_caller]
    pub(super) fn emit_impact(&mut self, guard: EffectGuard, inputs: &[Arg]) {
        self.refuse_on_chain_in_private_scope("an Impact op");
        self.b
            .impact(guard.0.unwrap_or(Arg::Imm(Fr::from(1u64))), inputs);
    }

    /// `assert`, with its optional message recorded at the index of the
    /// `Assert` itself — AFTER the guard's select is emitted, which is what
    /// lets the simulator find the message by the failing instruction's
    /// index. Recording it before the select left every message inside a
    /// scope pointing one instruction early.
    pub(super) fn emit_assert(&mut self, cond: Val, message: Option<&str>, guard: EffectGuard) {
        let cond = self.checked_value(guard, cond, 1);
        if let Some(message) = message {
            self.assert_messages.push(AssertMessage {
                instruction: self.b.len(),
                message: message.to_string(),
            });
        }
        self.b.assert(cond);
    }

    pub(super) fn emit_constrain_eq(&mut self, a: Arg, b: Arg, guard: EffectGuard) {
        match guard.0 {
            None => self.b.constrain_eq(a, b),
            Some(Arg::Imm(imm)) if imm == Fr::from(1u64) => self.b.constrain_eq(a, b),
            Some(_) => {
                let eq = self.b.test_eq(a, b);
                self.emit_assert(eq, None, guard);
            }
        }
    }

    /// The value a RANGE check (bits / boolean) sees — [`checked_value`]
    /// with `off = 0`, except for one case where no select is needed: `w`
    /// is itself a transcript read carrying this very guard. Such a read is
    /// zero where the guard is off, so the bare constraint is already total;
    /// this is compactc's shape for a guarded read (bare bit constraints
    /// behind a guarded witness — [`Builder3::is_read_guarded_by`]), kept
    /// so the port lineage stays instruction-identical to it. Any other
    /// value — a sum, a decoded limb, a read under a DIFFERENT guard — gets
    /// the select, because nothing says it is in range on the path not
    /// taken.
    ///
    /// [`checked_value`]: Circuit3::checked_value
    /// [`Builder3::is_read_guarded_by`]: minocrab_ir::v3::Builder3::is_read_guarded_by
    fn range_checked_value(&mut self, guard: EffectGuard, w: Val) -> Val {
        if let Some(Arg::Val(g)) = guard.0 {
            if self.b.is_read_guarded_by(w, g) {
                return w;
            }
        }
        self.checked_value(guard, w, 0)
    }

    /// Both range emitters RETURN THE WIRE THEY CONSTRAINED. In straight-line
    /// code that is `w`; inside a scope it is `select(guard, w, 0)` — and
    /// that selected wire is the value the branch computes, in compactc's
    /// own semantics (every value inside `if` is the selected one, and what
    /// the branch does next consumes it). A checked constructor that hands
    /// the ORIGINAL wire downstream would carry a value the check does not
    /// cover on the path not taken — which is exactly what the taint lint
    /// caught when this was first written the other way: the merged coin's
    /// value fed its commitment hash unbounded off-path.
    pub(super) fn emit_constrain_bits(&mut self, w: Val, bits: u32, guard: EffectGuard) -> Val {
        let w = self.range_checked_value(guard, w);
        self.b.constrain_bits(w, bits);
        w
    }

    pub(super) fn emit_constrain_boolean(&mut self, w: Val, guard: EffectGuard) -> Val {
        let w = self.range_checked_value(guard, w);
        self.b.constrain_to_boolean(w);
        w
    }
}

#[cfg(test)]
mod tests {
    /// The other half of the choke point: the parent module never calls a
    /// raw effect emitter on the builder. `EffectGuard`'s private field
    /// makes an emitter unreachable WITHOUT the scope; this makes the raw
    /// builder call — which has no guard parameter to forget — unreachable
    /// from the surface at all. Textual, like the repo's escape-hatch greps,
    /// and for the same reason: the builder's emitters are public API one
    /// layer down, so a type cannot hide them from a sibling method.
    #[test]
    fn the_parent_module_reaches_no_raw_effect_emitter() {
        const RAW: &[&str] = &[
            "self.b.private_input(",
            "self.b.public_input(",
            "self.b.impact(",
            "self.b.assert(",
            "self.b.constrain_eq(",
            "self.b.constrain_bits(",
            "self.b.constrain_to_boolean(",
            "self.guards.",
        ];
        let parent = include_str!("../v3.rs");
        let leaked: Vec<&str> = RAW
            .iter()
            .copied()
            .filter(|raw| parent.contains(raw))
            .collect();
        assert!(
            leaked.is_empty(),
            "v3.rs reaches a raw effect emitter directly: {leaked:?}\n  \
             every effect goes through an `emit_*` in v3/effects.rs, which \
             takes the `EffectGuard` that `effect_guard` resolves"
        );
    }
}
