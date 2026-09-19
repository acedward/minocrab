//! LEDGER HOOKS (M42, notes/hooks-design.org): the write program as a typed
//! value.
//!
//! Inline is the read set; the hook is the write program. Everything a
//! circuit does to the ledger inline is a `popeq` read (an assumption the
//! landing validates, which can go stale) or a plain write of circuit
//! values. Everything BLIND — a read-modify-write the ledger performs
//! itself, a copy from one slot to another, a branch on what a slot holds
//! — lives here, on [`Hook`], and nowhere inline: a hook runs after the
//! whole body on whatever the ledger holds at landing, cannot go stale,
//! and cannot tell the circuit anything.
//!
//! A [`Hook`] is a closed program over the ledger, built by chaining
//! methods and attached with `c.then(hook)` ([`Circuit3::then`]). It is
//! emitted after the body whatever the position of the `then` call;
//! several hooks run in attachment order; a hook attached inside
//! [`Circuit3::when`] captures that guard at attachment and is absent from
//! the transcript where the guard is off. The builder has no `popeq`
//! method, so a hook is BLIND by construction.
//!
//! ```ignore
//! fn stamp(k: Handle<Public>) -> Hook {
//!     Hook::new()
//!         .add(&B.nonce, 1u64)                // idxp; push 1; add; insc
//!         .copy(&B.nonce, &B.nonce_at, k)      // the snapshot
//!         .copy(&B.seen, &B.seen_at, k)
//! }
//! ```
//!
//! | method | on chain | fails the transaction when |
//! |---|---|---|
//! | [`add`](Hook::add), [`sub`](Hook::sub), [`max`](Hook::max), [`min`](Hook::min), [`and`](Hook::and), [`or`](Hook::or) | read-modify-write, no popeq | overflow, underflow |
//! | [`write`](Hook::write), [`insert`](Hook::insert), [`remove`](Hook::remove) | the plain writes, as effects | never (remove of an absent key is a no-op) |
//! | [`copy`](Hook::copy), [`copy_cell`](Hook::copy_cell), [`move_entry`](Hook::move_entry) | slot to slot, the circuit never sees the value | absent source (`move_entry`) |
//! | [`if_absent`](Hook::if_absent), [`if_below`](Hook::if_below), [`if_unset`](Hook::if_unset) | `branch` over the arm, skip computed | inside the arm only |
//! | [`then`](Hook::then) | concatenation | as its parts |
//!
//! # What the types enforce
//!
//! - Hook arguments are PUBLIC: a value enters a hook through
//!   [`HookValue`], which every [`LedgerRepr`] type is, and `LedgerRepr` is
//!   implemented for `Public` leaves only. A private wire has no way in —
//!   disclose it first:
//!
//! ```compile_fail
//! # use minocrab::v3::{Circuit3, FieldT};
//! # use minocrab::Private;
//! # use minocrab_std::v3::{Hook, LedgerCell, Uint};
//! # let mut c = Circuit3::new();
//! const N: LedgerCell<Uint<64, minocrab::Public>> = LedgerCell::at(0);
//! let d: Uint<64, Private> = Uint::from_field_unchecked(c.arg::<FieldT>("d"));
//! // error[E0277]: the trait bound `Uint<64, Private>: HookValue<Uint<64, Public>>` is not satisfied
//! c.then(Hook::new().add(&N, d));
//! ```
//!
//! - Cell arithmetic only on the widths the VM decodes ([`CellArith`]:
//!   `Uint<8|16|32|64, Public>`), booleans only on `Bool<Public>` cells,
//!   [`copy`](Hook::copy) only into a map of the cell's value type,
//!   [`insert`](Hook::insert) only of the map's value type — the handle
//!   types say so.
//! - A slot-to-slot copy reaches back over the destination's walk with one
//!   `dup`, whose operand is a nibble. The destination path is bounded at
//!   the type ([`Reachable`]): a declared slot or one at most four `at_key`
//!   steps deep, since a declared path may itself be three elements. Past
//!   that is a missing impl:
//!
//! ```compile_fail
//! # use minocrab::v3::Circuit3;
//! # use minocrab::Public;
//! # use minocrab_std::v3::{Hook, LedgerCell, LedgerMap, Uint};
//! # let mut c = Circuit3::new();
//! type U = Uint<64, Public>;
//! const N: LedgerCell<U> = LedgerCell::at(0);
//! const DEEP: LedgerMap<U, LedgerMap<U, LedgerMap<U, LedgerMap<U, LedgerMap<U, LedgerMap<U, U>>>>>> = LedgerMap::at(1);
//! let k = Uint::<64, Public>::from_field_unchecked(c.constant(1u64));
//! let five = DEEP.at_key(&mut c, &k).at_key(&mut c, &k).at_key(&mut c, &k).at_key(&mut c, &k).at_key(&mut c, &k);
//! // error[E0277]: the trait bound `KeyPath<5>: Reachable` is not satisfied
//! c.then(Hook::new().copy(&N, &five, k));
//! ```
//!
//! - Both arms of a branch are hooks (`FnOnce(Hook) -> Hook`), so a branch
//!   leaves the stack as it found it, and the skip count is the arm's
//!   length, computed at lowering — never hand-counted.
//!
//! What is NOT a type: the paths' lengths. A declared field path is one to
//! three elements at runtime, so the stack shapes under each method are
//! checked by the ledger crate's op builders (an `insc` or `dup` operand
//! past its nibble is a build-time assert there), not by a type-level
//! stack. Recorded in the note as the deviation from the design's
//! `Program<In, Out>` sketch.
//!
//! Runtime, value-dependent, fails the transaction and nothing earlier: an
//! absent source, overflow, underflow, gas.
//!
//! The gate is Midnight's on-chain VM (`tests/v3_hook.rs`): every method
//! run through the executor against a seeded state, including each failure
//! row above, plus attachment order, guard capture and the after-the-body
//! rule.

use minocrab::v3::{Circuit3, Deferred, ImpactElem};
use minocrab::{Fr, Public};
use minocrab_ledger::{
    branch, cell_add_at, cell_and_at, cell_copy_at, cell_max_at, cell_min_at, cell_or_at,
    cell_snapshot_into_map_at, cell_sub_at, cell_write_at, dup, idx_path, lt, map_insert_at,
    map_move_entry_at, map_remove_at, member, neg, push_cell, ImpactOp, LedgerValue,
};

use super::ledger::{FieldPath, KeyPath, LedgerCell, LedgerMap, LedgerPath, LedgerRepr};
use super::{Bool, Uint};

/// A value a hook pushes: a public ledger value, or a native literal that
/// becomes an inline immediate.
///
/// Every [`LedgerRepr`] type is one (they are all `Public`). `u64` stands
/// for any `Uint<BITS, Public>` cell value and `bool` for a `Bool<Public>`,
/// so `.add(&B.nonce, 1u64)` needs no wire. Nothing else is: a private wire
/// is not a `LedgerRepr`, and an `Assumed` read (M42 B) is not either until
/// `.stale()` names the assumption.
pub trait HookValue<T> {
    /// The value as the ledger takes it.
    fn hook_value(self, c: &mut Circuit3) -> LedgerValue;
}

impl<T: LedgerRepr> HookValue<T> for T {
    fn hook_value(self, c: &mut Circuit3) -> LedgerValue {
        self.ledger_value(c)
    }
}

impl<const BITS: u32> HookValue<Uint<BITS, Public>> for u64 {
    fn hook_value(self, _c: &mut Circuit3) -> LedgerValue {
        assert!(
            BITS >= 64 || self < (1u64 << BITS),
            "a literal {self} does not fit a Uint<{BITS}> cell"
        );
        LedgerValue::new(
            <Uint<BITS, Public> as LedgerRepr>::atoms(),
            vec![ImpactElem::Imm(Fr::from(self))],
        )
    }
}

impl HookValue<Bool<Public>> for bool {
    fn hook_value(self, _c: &mut Circuit3) -> LedgerValue {
        LedgerValue::new(
            <Bool<Public> as LedgerRepr>::atoms(),
            vec![ImpactElem::Imm(Fr::from(u64::from(self)))],
        )
    }
}

/// A value already lowered by a caller that has `c` in hand — the
/// [`Primitive`](super::blind::Primitive) impls build their hooks inside a
/// circuit and can hand the limbs over directly. Crate-private: the typed
/// check on `T` is the caller's.
pub(crate) struct Lowered(pub(crate) LedgerValue);

impl<T> HookValue<T> for Lowered {
    fn hook_value(self, _c: &mut Circuit3) -> LedgerValue {
        self.0
    }
}

/// The cell types the VM's `add` / `sub` / `lt` decode: it reads the cell
/// as a `u64` (onchain-vm `vm.rs`), so `Uint<8|16|32|64, Public>` and no
/// wider. A missing impl on anything else.
#[diagnostic::on_unimplemented(
    message = "hook arithmetic runs on `Uint<8|16|32|64, Public>` cells only",
    note = "the VM decodes the cell as a u64; a wider cell is not a number to it"
)]
pub trait CellArith: LedgerRepr {}
impl CellArith for Uint<8, Public> {}
impl CellArith for Uint<16, Public> {}
impl CellArith for Uint<32, Public> {}
impl CellArith for Uint<64, Public> {}

/// A map path a slot-to-slot copy can reach back over: the reach is
/// `2·len(path) + 1` and the `dup` operand is a nibble, so `len ≤ 7`; a
/// declared path is up to three elements, leaving four `at_key` steps.
/// [`KeyPath<5>`] and deeper have no impl.
#[diagnostic::on_unimplemented(
    message = "a copy into a map this deep reaches past the `dup` nibble",
    label = "at most four `at_key` steps for a copy destination",
    note = "`dup 2·len(m)+1` is how the copy reaches the state after walking to \
            the map; a nibble holds 15, and a declared field path may already \
            be three elements"
)]
pub trait Reachable: LedgerPath {}
impl Reachable for FieldPath {}
impl Reachable for KeyPath<1> {}
impl Reachable for KeyPath<2> {}
impl Reachable for KeyPath<3> {}
impl Reachable for KeyPath<4> {}

/// One step of a hook, lowered when the hook is attached: the values it
/// captured become limbs then, and the circuit is at hand for the reprs
/// that need it.
type Step = Box<dyn FnOnce(&mut Circuit3) -> Vec<ImpactOp>>;

/// The write program: a chain of blind ledger operations, attached with
/// [`Circuit3::then`]. See the module docs.
#[must_use = "a hook does nothing until it is attached with `c.then(hook)`"]
#[derive(Default)]
pub struct Hook {
    steps: Vec<Step>,
}

impl Hook {
    /// The empty program.
    pub fn new() -> Self {
        Hook::default()
    }

    fn step(mut self, step: impl FnOnce(&mut Circuit3) -> Vec<ImpactOp> + 'static) -> Self {
        self.steps.push(Box::new(step));
        self
    }

    /// Lower to Impact ops, in program order. What [`Circuit3::then`] does
    /// at attachment; public so a test can compare a hook with the explicit
    /// op list it claims to be.
    pub fn into_ops(self, c: &mut Circuit3) -> Vec<ImpactOp> {
        self.steps.into_iter().flat_map(|step| step(c)).collect()
    }

    // ---- the read-modify-writes ------------------------------------------------------

    /// `cell += delta`, blind; overflow fails the transaction.
    pub fn add<T: CellArith>(self, cell: &LedgerCell<T>, delta: impl HookValue<T> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_add_at(&path, &delta.hook_value(c)))
    }

    /// `cell −= delta`, blind; underflow fails the transaction.
    pub fn sub<T: CellArith>(self, cell: &LedgerCell<T>, delta: impl HookValue<T> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_sub_at(&path, &delta.hook_value(c)))
    }

    /// `cell = max(cell, delta)`, blind.
    pub fn max<T: CellArith>(self, cell: &LedgerCell<T>, delta: impl HookValue<T> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_max_at(&path, &delta.hook_value(c)))
    }

    /// `cell = min(cell, delta)`, blind.
    pub fn min<T: CellArith>(self, cell: &LedgerCell<T>, delta: impl HookValue<T> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_min_at(&path, &delta.hook_value(c)))
    }

    /// `cell = cell && delta`, blind.
    pub fn and(self, cell: &LedgerCell<Bool<Public>>, delta: impl HookValue<Bool<Public>> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_and_at(&path, &delta.hook_value(c)))
    }

    /// `cell = cell || delta`, blind.
    pub fn or(self, cell: &LedgerCell<Bool<Public>>, delta: impl HookValue<Bool<Public>> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_or_at(&path, &delta.hook_value(c)))
    }

    // ---- the plain writes, as effects ---------------------------------------------------

    /// `cell = value`.
    pub fn write<T: LedgerRepr>(self, cell: &LedgerCell<T>, value: impl HookValue<T> + 'static) -> Self {
        let path = cell.ledger_path();
        self.step(move |c| cell_write_at(&path, &value.hook_value(c)))
    }

    /// `map[key] = value`.
    pub fn insert<K: LedgerRepr, V: LedgerRepr, P: LedgerPath>(
        self,
        map: &LedgerMap<K, V, P>,
        key: impl HookValue<K> + 'static,
        value: impl HookValue<V> + 'static,
    ) -> Self {
        let path = map.ledger_path();
        self.step(move |c| {
            let key = key.hook_value(c);
            let value = value.hook_value(c);
            map_insert_at(&path, &key, &value)
        })
    }

    /// `map.remove(key)`; a no-op on an absent key.
    pub fn remove<K: LedgerRepr, V, P: LedgerPath>(
        self,
        map: &LedgerMap<K, V, P>,
        key: impl HookValue<K> + 'static,
    ) -> Self {
        let path = map.ledger_path();
        self.step(move |c| map_remove_at(&path, &key.hook_value(c)))
    }

    // ---- slot to slot ---------------------------------------------------------------------

    /// `map[key] = cell` — THE SNAPSHOT: the value goes from the cell to the
    /// entry with the circuit never learning it (`idxp m; push key; dup
    /// 2·len(m)+1; idx cell; ins 1; insc len(m)`).
    pub fn copy<T: LedgerRepr, K: LedgerRepr, P: Reachable>(
        self,
        cell: &LedgerCell<T>,
        map: &LedgerMap<K, T, P>,
        key: impl HookValue<K> + 'static,
    ) -> Self {
        let cell = cell.ledger_path();
        let map = map.ledger_path();
        self.step(move |c| cell_snapshot_into_map_at(&cell, &map, &key.hook_value(c)))
    }

    /// `dst = src`, cell to cell, blind.
    pub fn copy_cell<T: LedgerRepr>(self, src: &LedgerCell<T>, dst: &LedgerCell<T>) -> Self {
        let src = src.ledger_path();
        let dst = dst.ledger_path();
        self.step(move |_c| cell_copy_at(&src, &dst))
    }

    /// `map[to] = map[from]; map.remove(from)`, blind; an absent `from`
    /// fails the transaction (see `map_move_entry_at` for the presence
    /// check the VM needs).
    pub fn move_entry<K: LedgerRepr, V: LedgerRepr, P: Reachable>(
        self,
        map: &LedgerMap<K, V, P>,
        from: impl HookValue<K> + 'static,
        to: impl HookValue<K> + 'static,
    ) -> Self {
        let path = map.ledger_path();
        self.step(move |c| {
            let from = from.hook_value(c);
            let to = to.hook_value(c);
            map_move_entry_at(&path, &from, &to)
        })
    }

    // ---- the branches ----------------------------------------------------------------------

    /// A `branch` over `arm`: `<test>; branch len(arm); <arm>`, the test
    /// leaving TRUE on the stack when the arm is to be SKIPPED.
    fn branch_over(
        self,
        test: impl FnOnce(&mut Circuit3) -> Vec<ImpactOp> + 'static,
        arm: impl FnOnce(Hook) -> Hook,
    ) -> Self {
        let arm = arm(Hook::new());
        self.step(move |c| {
            let arm = arm.into_ops(c);
            let skip = u32::try_from(arm.len()).expect("an arm shorter than u32::MAX ops");
            let mut ops = test(c);
            ops.push(branch(skip));
            ops.extend(arm);
            ops
        })
    }

    /// Run `arm` only if `map` has no entry at `key`: `dup 0; idx m; push
    /// key; member; branch len(arm); <arm>`.
    pub fn if_absent<K: LedgerRepr, V, P: LedgerPath>(
        self,
        map: &LedgerMap<K, V, P>,
        key: impl HookValue<K> + 'static,
        arm: impl FnOnce(Hook) -> Hook,
    ) -> Self {
        let path = map.ledger_path();
        self.branch_over(
            move |c| {
                vec![
                    dup(0),
                    idx_path(false, false, &path),
                    push_cell(false, &key.hook_value(c)),
                    member(),
                ]
            },
            arm,
        )
    }

    /// Run `arm` only if `cell < bound`: `dup 0; idx cell; push bound; lt;
    /// neg; branch len(arm); <arm>`.
    pub fn if_below<T: CellArith>(
        self,
        cell: &LedgerCell<T>,
        bound: impl HookValue<T> + 'static,
        arm: impl FnOnce(Hook) -> Hook,
    ) -> Self {
        let path = cell.ledger_path();
        self.branch_over(
            move |c| {
                vec![
                    dup(0),
                    idx_path(false, false, &path),
                    push_cell(false, &bound.hook_value(c)),
                    lt(),
                    neg(),
                ]
            },
            arm,
        )
    }

    /// Run `arm` only if the `flag` cell is false: `dup 0; idx flag; branch
    /// len(arm); <arm>`. A first-write is `if_unset(flag, |h|
    /// h.write(cell, v).write(flag, true))`.
    pub fn if_unset(self, flag: &LedgerCell<Bool<Public>>, arm: impl FnOnce(Hook) -> Hook) -> Self {
        let path = flag.ledger_path();
        self.branch_over(move |_c| vec![dup(0), idx_path(false, false, &path)], arm)
    }

    // ---- composition ------------------------------------------------------------------------

    /// This program, then `other`.
    pub fn then(mut self, other: Hook) -> Self {
        self.steps.extend(other.steps);
        self
    }
}

impl Deferred for Hook {
    fn lower(self, c: &mut Circuit3) -> Vec<Vec<ImpactElem>> {
        self.into_ops(c).into_iter().map(|op| op.0).collect()
    }
}
