//! Typed disclosure declarations: what a circuit is allowed to make public,
//! stated in its signature and checked by a generated test.
//!
//! [`Circuit3::disclose`](super::Circuit3::disclose) is the audit point —
//! every value leaving the private domain passes through it and names itself
//! — but the name is a free string at one call site, and nothing says what
//! the circuit as a whole reveals. This layer adds the missing half
//! (notes/contract-api.org §Disclosure declaration):
//!
//! ```ignore
//! label!(RequestId = "request id");
//! label!(RequestRecord = "request record");
//!
//! #[circuit]
//! pub fn deposit(c: &mut Circuit3, ..) -> Discloses<(DepositorCommitment, RequestId, RequestRecord)> {
//!     ..
//!     let request_id = request_id.disclose_as::<RequestId>(c);
//!     ..
//!     Discloses::of(())
//! }
//! ```
//!
//! The enforcement is split, deliberately:
//!
//! - rustc checks the SYMBOLS. A label is a type, so a typo or a rename is a
//!   compile error at both the declaration and the call site, and the two
//!   share one definition.
//! - a GENERATED TEST checks the SET. `#[circuit]` emits a `#[test]` that
//!   builds the circuit and compares the declared labels against the ones it
//!   actually disclosed, failing with the fix spelled out
//!   ([`assert_declared_disclosures`]). Full static enforcement would need a
//!   label set threaded through `&mut Circuit3` as type state — rejected as
//!   baroque; a plain test failure that names the label and the edit is
//!   worth more than a type error nobody can read.
//!
//! A circuit FAMILY parameterized by a Rust value has no attribute to
//! generate that test from — `#[circuit]` makes a nullary constructor, so
//! such a family is built through `entry()` by hand. It declares exactly the
//! same way (the closure's return type is the declaration; `entry` takes any
//! zero-slot [`CircuitOut`](../../../minocrab_std/v3/trait.CircuitOut.html)),
//! and its test is the expansion's own body written out once per
//! instantiation:
//!
//! ```ignore
//! type DepositDisclosures = Discloses<(Amount, Recipient)>;
//!
//! fn base_with_emits(emits: usize) -> Compiled3 {
//!     entry(|c, args: DepositArgs| -> DepositDisclosures { ..; Discloses::of(()) })
//! }
//!
//! #[test]
//! fn the_declared_disclosures_are_the_ones_the_family_makes() {
//!     for emits in [0, 1, 2, 4] {
//!         assert_declared_disclosures::<DepositDisclosures>(
//!             &format!("base_with_emits({emits})"), &base_with_emits(emits));
//!     }
//! }
//! ```
//!
//! The alias is what makes the entry point and the test the SAME declaration
//! — the attribute gets that for free by copying the return type's tokens.
//! (An alias is deliberately NOT accepted in a `#[circuit]` signature, where
//! the declaration has to be legible where the arguments are.)
//!
//! Labels are per LOGICAL VALUE, not per wire: `b32.disclose_as::<L>(c)`
//! discloses both limbs under the single symbol `L`, where the hand-written
//! circuits wrote `"… (hi)"` and `"… (lo)"`. One record, one label, one
//! entry in the declaration (see [`Disclosure3`](super::Disclosure3)).
//!
//! [`Discloses<D, R>`](Discloses) is a real zero-sized wrapper around the
//! circuit's return value, not a macro rewrite of the signature: `D` is the
//! declaration, `R` the value (`()` for Compact's `[]` circuits, which is
//! why it is the default). Being a real type, it costs nothing — its
//! `CircuitOut` impl (in minocrab-std, where that trait lives) is `R`'s —
//! and rust-analyzer sees a normal generic type rather than something a
//! macro invented.
//!
//! Placement: here rather than in minocrab-std, because a disclosure is a
//! frontend concept and every crate that discloses needs the vocabulary —
//! `minocrab_ledger::contract_call` discloses a cross-contract call's
//! entry-point hash and commitment, and those labels have to be nameable in
//! the CALLER's declaration. minocrab-std adds the [`Disclose`] impls for
//! its own value types.

use std::collections::BTreeSet;
use std::marker::PhantomData;

use super::{Circuit3, Compiled3, IrTy, Wire3};
use crate::{DisclosureKind, Private, Public};

// ---- labels -----------------------------------------------------------------

/// One disclosure label: a zero-sized type whose whole content is the string
/// the record carries. Written with [`label!`](crate::label), or by hand — the macro
/// generates nothing that could not be typed out.
pub trait DisclosureLabel: 'static {
    /// What the disclosure record (and the simulator's report) calls it.
    const LABEL: &'static str;
}

/// Declare disclosure labels — one zero-sized type each, with its
/// [`DisclosureLabel`] and [`LabelSet`] impls.
///
/// ```ignore
/// label!(RequestId = "request id");
///
/// label! {
///     /// The depositor's identity commitment, the key the record is filed under.
///     pub DepositorCommitment = "depositor identity commitment";
///     pub RequestRecord = "request record";
/// }
/// ```
#[macro_export]
macro_rules! label {
    ($($(#[$meta:meta])* $vis:vis $name:ident = $text:literal);* $(;)?) => {$(
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        $vis struct $name;

        impl $crate::v3::DisclosureLabel for $name {
            const LABEL: &'static str = $text;
        }

        impl $crate::v3::LabelSet for $name {
            fn push_labels(labels: &mut ::std::vec::Vec<&'static str>) {
                labels.push($text);
            }
        }
    )*};
}

/// A set of labels: the `D` of a [`Discloses<D, R>`](Discloses) declaration
/// — one label, a tuple of them, or `()` for a circuit that discloses
/// nothing.
///
/// Implemented for tuples up to sixteen labels here, and for each label type
/// by [`label!`](crate::label). There is no blanket `impl<L: DisclosureLabel> LabelSet for
/// L`: it would overlap the tuple impls (nothing stops a downstream crate
/// implementing `DisclosureLabel` for a tuple of its own types), which is
/// why the macro emits the impl per label instead.
pub trait LabelSet {
    /// Push every label's string, in declaration order.
    fn push_labels(labels: &mut Vec<&'static str>);

    /// The declared labels as a set — duplicates are meaningless here, since
    /// a label names a value, not an occurrence.
    fn labels() -> BTreeSet<&'static str> {
        let mut labels = Vec::new();
        Self::push_labels(&mut labels);
        labels.into_iter().collect()
    }
}

/// A circuit that discloses nothing — a positive statement, checked like any
/// other.
impl LabelSet for () {
    fn push_labels(_labels: &mut Vec<&'static str>) {}
}

macro_rules! label_set_tuples {
    ($(($($param:ident),+)),* $(,)?) => {$(
        impl<$($param: LabelSet),+> LabelSet for ($($param,)+) {
            fn push_labels(labels: &mut Vec<&'static str>) {
                $($param::push_labels(labels);)+
            }
        }
    )*};
}

label_set_tuples! {
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
    (A, B, C, D, E, F, G, H, I),
    (A, B, C, D, E, F, G, H, I, J),
    (A, B, C, D, E, F, G, H, I, J, K),
    (A, B, C, D, E, F, G, H, I, J, K, L),
    (A, B, C, D, E, F, G, H, I, J, K, L, M),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
}

// ---- disclose_as ------------------------------------------------------------

/// A private value that can be disclosed under a label type, fanning out to
/// every wire it is made of.
///
/// The value is the receiver rather than an argument of a `Circuit3` method
/// (`value.disclose_as::<L>(c)`, not `c.disclose_as::<L>(value)`) for a hard
/// Rust reason: a circuit method would need two type parameters — the label
/// and the value — and a turbofish must supply all of a function's type
/// arguments or none (E0107), so the design's `c.disclose_as::<RequestId>(v)`
/// is only spellable as `c.disclose_as::<RequestId, _>(v)`. Putting the
/// label on a method of the value leaves exactly one parameter to name.
#[diagnostic::on_unimplemented(
    message = "`{Self}` has nothing to disclose",
    label = "not a private value",
    note = "`disclose_as` is the private→public gate, so it is implemented at \
            `Private` only: bare wires here, every typed leaf in \
            minocrab-std's `v3::disclose`. A value that is already `Public` \
            has crossed the gate and needs no call; a RECORD type has no impl \
            by design — disclose the fields that actually leave, so the \
            disclosure record names them one by one"
)]
pub trait Disclose: Sized {
    /// The same shape with public wires.
    type Public;

    /// Disclose this value under the label type `L` — one record covering
    /// every wire, named `L::LABEL`.
    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Self::Public;
}

/// A bare wire of any value type — the curve point `initialize` discloses
/// included.
impl<T: IrTy> Disclose for Wire3<T, Private> {
    type Public = Wire3<T, Public>;

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Wire3<T, Public> {
        c.disclose_as::<L, T>(self)
    }
}

/// A run-time-long list of a value's wires (an event record's limbs): still
/// one record.
impl<T: IrTy> Disclose for Vec<Wire3<T, Private>> {
    type Public = Vec<Wire3<T, Public>>;

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Vec<Wire3<T, Public>> {
        c.disclose_slice_as::<L, _>(&self)
    }
}

/// An array: every element under the one label, in order — a bounded
/// vector's slots (`minocrab_std::v3::Bounded`).
impl<T: Disclose, const N: usize> Disclose for [T; N] {
    type Public = [T::Public; N];

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Self::Public {
        let mut out = Vec::with_capacity(N);
        for element in self {
            out.push(element.disclose_as::<L>(c));
        }
        match <[T::Public; N]>::try_from(out) {
            Ok(array) => array,
            Err(_) => unreachable!("one disclosure per element"),
        }
    }
}

// ---- the declaration --------------------------------------------------------

/// A circuit's return type: `D` is the set of labels it discloses, `R` the
/// value it returns (`()` for Compact's `[]` circuits).
///
/// Zero cost — `D` is phantom and the `CircuitOut` impl (minocrab-std,
/// where that trait lives) is `R`'s, so
/// declaring changes no instruction, no argument slot and no output slot.
pub struct Discloses<D, R = ()> {
    value: R,
    _labels: PhantomData<fn() -> D>,
}

impl<D, R> Discloses<D, R> {
    /// The circuit's return value, under this declaration.
    pub fn of(value: R) -> Self {
        Discloses { value, _labels: PhantomData }
    }

    /// The returned value, declaration dropped.
    pub fn into_inner(self) -> R {
        self.value
    }
}

/// The declared label set of a circuit, recovered from its return type by
/// the generated test.
pub trait Declared {
    fn declared() -> BTreeSet<&'static str>;
}

impl<D: LabelSet, R> Declared for Discloses<D, R> {
    fn declared() -> BTreeSet<&'static str> {
        D::labels()
    }
}

/// What a built circuit actually disclosed: the labels of its
/// [`DisclosureKind::Disclosed`] records.
///
/// Only that kind. `Output` records are the return value, whose disclosure
/// the type system already enforces (`CircuitOut` exists only for public
/// values), and `Statement` records are the ledger writes an already-public
/// value feeds — neither is a private value crossing the gate, which is what
/// a declaration is about.
pub fn disclosed_labels(compiled: &Compiled3) -> BTreeSet<&str> {
    compiled
        .disclosures
        .iter()
        .filter(|d| d.kind == DisclosureKind::Disclosed)
        .map(|d| d.label.as_str())
        .collect()
}

/// The labels disclosed under a BARE STRING (`c.disclose(w, "…")`), which
/// no declaration accepts — see [`DisclosureKind::DisclosedUntyped`].
pub fn untyped_labels(compiled: &Compiled3) -> BTreeSet<&str> {
    compiled
        .disclosures
        .iter()
        .filter(|d| d.kind == DisclosureKind::DisclosedUntyped)
        .map(|d| d.label.as_str())
        .collect()
}

/// A label names a VALUE TYPE, not a record: one `disclose_as::<Coin>` on a
/// qualified coin records its fields and its Merkle index separately, and an
/// `Either` recipient records both arms, all under the one label. So the
/// declaration is a SET of labels by design, and "the same label twice" is
/// the normal shape of a compound value — not a second value slipping out.
/// (A first draft rejected duplicates; twelve corpus circuits said otherwise.)
/// What the set cannot distinguish is a bare `c.disclose(w, "coin")` from the
/// typed path — that is closed by kind, not by counting: see
/// [`DisclosureKind`] and the bare-label report in the assertions below.
/// Assert that a circuit with NO `Discloses<..>` declaration disclosed
/// nothing — the test `#[circuit]` generates for such a circuit, so that a
/// missing declaration is a statement ("this circuit makes no private value
/// public") and not an opt-out. A `c.disclose` in an undeclared circuit
/// fails here with the labels it would have to declare.
pub fn assert_discloses_nothing(circuit: &str, compiled: &Compiled3) {
    let mut actual = disclosed_labels(compiled);
    actual.extend(untyped_labels(compiled));
    assert!(
        actual.is_empty(),
        "{circuit}: declares no disclosures (its return type is not `Discloses<..>`) but \
         disclosed {} label(s): {actual:?}\n  fix: declare them — `-> Discloses<({})>` \
         with a `label!` type per label — so the circuit's audit surface names every \
         private value it makes public. A missing declaration means \"discloses nothing\", \
         and this test is what makes that true.",
        actual.len(),
        actual
            .iter()
            .map(|l| format!("/* {l:?} */ L"))
            .collect::<Vec<_>>()
            .join(", ")
    );
}

/// Assert that a circuit disclosed exactly what its `Discloses<..>`
/// declaration says — the body of the test `#[circuit]` generates, and the
/// one an `entry()`-built family calls by hand, once per instantiation (see
/// the module docs). It is public for that second reason: the attribute
/// generates nothing here that could not be typed out.
///
/// The failure message is part of the design (notes/contract-api.org): it
/// names the circuit, both differences, and the edit that fixes each one. A
/// mismatch is never a type error; it is this, and it has to be readable.
pub fn assert_declared_disclosures<T: Declared>(circuit: &str, compiled: &Compiled3) {
    let declared = T::declared();
    let actual = disclosed_labels(compiled);
    let untyped = untyped_labels(compiled);

    let missing: Vec<&str> = declared
        .iter()
        .copied()
        .filter(|l| !actual.contains(l))
        .collect();
    let extra: Vec<&str> = actual
        .iter()
        .copied()
        .filter(|l| !declared.contains(l))
        .collect();
    if missing.is_empty() && extra.is_empty() && untyped.is_empty() {
        return;
    }

    let mut message = format!(
        "{circuit}: the `Discloses<..>` declaration does not match what the circuit \
         disclosed.\n"
    );
    if !missing.is_empty() {
        message.push_str(&format!(
            "\n  DECLARED BUT NEVER DISCLOSED ({}):\n",
            missing.len()
        ));
        for label in &missing {
            message.push_str(&format!(
                "    {label:?}\n      \
                 fix: disclose that value with `.disclose_as::<L>(c)`, where L is the \
                 label type whose LABEL is {label:?} — or, if the circuit is not \
                 supposed to disclose it any more, drop L from `{circuit}`'s \
                 `-> Discloses<(..)>`.\n"
            ));
        }
    }
    if !extra.is_empty() {
        message.push_str(&format!(
            "\n  DISCLOSED BUT NOT DECLARED ({}):\n",
            extra.len()
        ));
        for label in &extra {
            message.push_str(&format!(
                "    {label:?}\n      \
                 fix: add its label type to `{circuit}`'s `-> Discloses<(..)>`. If the \
                 disclosure is still a bare `c.disclose(w, {label:?})`, give it a label \
                 type first — `label!(SomeName = {label:?});` — and call \
                 `w.disclose_as::<SomeName>(c)`.\n"
            ));
        }
    }
    if !untyped.is_empty() {
        message.push_str(&format!(
            "\n  DISCLOSED WITHOUT A LABEL TYPE ({}):\n",
            untyped.len()
        ));
        for label in &untyped {
            message.push_str(&format!(
                "    {label:?}\n      \
                 fix: a bare `c.disclose(w, {label:?})` satisfies no declaration, even one \
                 whose label spells the same text — give it a label type \
                 (`label!(SomeName = {label:?});`) and call `w.disclose_as::<SomeName>(c)`.\n"
            ));
        }
    }
    message.push_str(&format!(
        "\n  declared ({}): {:?}\n  disclosed ({}): {:?}\n\n\
         The declaration is this circuit's audit surface: every private value it \
         makes public belongs in it.\n",
        declared.len(),
        declared,
        actual.len(),
        actual,
    ));
    panic!("{message}");
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::v3::{DisclosedWire, FieldT, Identifier};

    label!(Alpha = "alpha");
    label!(Beta = "beta");
    label! {
        /// Doc comments and a visibility are accepted, and several labels
        /// may share one invocation.
        pub Gamma = "gamma";
        pub Delta = "delta";
    }

    #[test]
    fn a_label_is_its_string() {
        assert_eq!(Alpha::LABEL, "alpha");
        assert_eq!(Gamma::LABEL, "gamma");
        assert_eq!(<(Alpha, Beta, Delta)>::labels(), ["alpha", "beta", "delta"].into());
        assert_eq!(<()>::labels(), BTreeSet::new());
        assert_eq!(<(Alpha,)>::labels(), ["alpha"].into());
    }

    /// A value's wires are ONE record, and the identifiers it carries are
    /// the disclosed wires' own — which is what makes the report valued.
    #[test]
    fn a_multi_wire_value_gets_one_record() {
        let mut c = Circuit3::new();
        let hi = c.arg::<FieldT>("v_hi");
        let lo = c.arg::<FieldT>("v_lo");
        let [hi, lo] = c.disclose_all_as::<Alpha, _, 2>([hi, lo]);
        c.output(hi, "hi");
        c.output(lo, "lo");
        let compiled = c.finish(false);

        let disclosed: Vec<_> = compiled
            .disclosures
            .iter()
            .filter(|d| d.kind == DisclosureKind::Disclosed)
            .collect();
        assert_eq!(disclosed.len(), 1);
        assert_eq!(disclosed[0].label, "alpha");
        assert_eq!(disclosed[0].values.len(), 2);
        assert_eq!(
            disclosed[0].values,
            vec![
                DisclosedWire::Named(Identifier("%v_hi.0".into())),
                DisclosedWire::Named(Identifier("%v_lo.1".into())),
            ]
        );
        assert_eq!(disclosed_labels(&compiled), ["alpha"].into());
    }

    #[test]
    fn disclosing_emits_no_instruction() {
        let mut c = Circuit3::new();
        let w = c.arg::<FieldT>("w");
        let before = c.instruction_count();
        let _ = w.disclose_as::<Beta>(&mut c);
        let _ = c.disclose_slice_as::<Gamma, _>(&[w, w, w]);
        assert_eq!(c.instruction_count(), before);
    }

    fn declared_vs<T: Declared>(labels: &[&str]) -> String {
        let mut c = Circuit3::new();
        let w = c.arg::<FieldT>("w");
        for label in labels {
            // The known labels disclose TYPED; anything else is the bare
            // string, which is exactly what the untyped category is for.
            match *label {
                "alpha" => drop(w.disclose_as::<Alpha>(&mut c)),
                "beta" => drop(w.disclose_as::<Beta>(&mut c)),
                "gamma" => drop(w.disclose_as::<Gamma>(&mut c)),
                other => drop(c.disclose_slice(other, &[w])),
            }
        }
        let compiled = c.finish(false);
        std::panic::catch_unwind(|| assert_declared_disclosures::<T>("demo", &compiled))
            .err()
            .map(|e| {
                e.downcast_ref::<String>()
                    .cloned()
                    .unwrap_or_else(|| "<non-string panic>".into())
            })
            .unwrap_or_default()
    }

    #[test]
    fn the_matching_set_passes() {
        assert_eq!(declared_vs::<Discloses<(Alpha, Beta)>>(&["beta", "alpha"]), "");
        assert_eq!(declared_vs::<Discloses<()>>(&[]), "");
    }

    /// dmd's proviso: the failure must not be confusing. It names the
    /// circuit, both differences, and the edit for each.
    #[test]
    fn the_failure_names_the_label_and_the_fix() {
        let message = declared_vs::<Discloses<(Alpha, Beta)>>(&["alpha", "gamma"]);
        assert!(message.contains("demo: the `Discloses<..>` declaration"), "{message}");
        assert!(message.contains("DECLARED BUT NEVER DISCLOSED (1)"), "{message}");
        assert!(message.contains("\"beta\""), "{message}");
        assert!(message.contains("disclose that value with `.disclose_as::<L>(c)`"), "{message}");
        assert!(message.contains("DISCLOSED BUT NOT DECLARED (1)"), "{message}");
        assert!(message.contains("\"gamma\""), "{message}");
        assert!(message.contains("label!(SomeName = \"gamma\");"), "{message}");
        assert!(message.contains("add its label type to `demo`'s"), "{message}");
    }

    /// A bare string that spells a declared label satisfies nothing: it is
    /// reported as its own category, and the declared label stays missing.
    #[test]
    fn a_bare_string_never_satisfies_a_declaration() {
        let message = declared_vs::<Discloses<(Alpha,)>>(&["alpha-as-a-bare-string"]);
        assert!(message.contains("DISCLOSED WITHOUT A LABEL TYPE (1)"), "{message}");
        assert!(message.contains("satisfies no declaration"), "{message}");
        assert!(message.contains("DECLARED BUT NEVER DISCLOSED (1)"), "{message}");

        let mut c = Circuit3::new();
        let w = c.arg::<FieldT>("w");
        let _ = c.disclose(w, "alpha");
        let compiled = c.finish(false);
        assert_eq!(disclosed_labels(&compiled), [].into());
        assert_eq!(untyped_labels(&compiled), ["alpha"].into());
    }

    /// Outputs and ledger statements are not disclosures of private values,
    /// and a declaration does not mention them.
    #[test]
    fn only_the_disclosed_kind_counts() {
        let mut c = Circuit3::new();
        let w = c.arg::<FieldT>("w");
        let public = w.disclose_as::<Alpha>(&mut c);
        c.output(public, "an output");
        let compiled = c.finish(false);
        assert_eq!(disclosed_labels(&compiled), ["alpha"].into());
    }
}
