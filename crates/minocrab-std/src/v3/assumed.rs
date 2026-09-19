//! ASSUMED VALUES (M42 B, notes/hooks-design.org, "Stale values must be
//! named"): what an inline ledger read returns.
//!
//! An inline read is a `popeq`: the prover supplies the value as a public
//! input, and the ledger checks at landing that the slot still holds it. So
//! the value is an ASSUMPTION the transaction makes about the state at
//! landing, and a landed transaction that changed the slot makes it stale.
//! [`Assumed<T>`] is that assumption as a type. The PROOF may consume it
//! freely — it derefs to `T`, compares, selects, asserts, and its fields are
//! reachable — because the proof's use of the value is exactly what the
//! `popeq` validates. The LEDGER may not take it back: an `Assumed<T>` has no
//! [`LedgerRepr`](super::LedgerRepr), is not [`Fresh`](super::Fresh) (the
//! bound on every inline write's value) and is not a
//! [`HookValue`](super::HookValue), so writing it to a cell, inserting it
//! into a map, or handing it to a hook does not compile until the programmer
//! writes [`stale`](Assumed::stale) — whose name is the record that the
//! transaction assumes the value it read is still current at landing, which
//! is the contended read-modify-write pattern the blind hooks exist to
//! replace.
//!
//! ```compile_fail
//! # use minocrab::v3::Circuit3;
//! # use minocrab::Public;
//! # use minocrab_std::v3::{LedgerCell, Uint};
//! # let mut c = Circuit3::new();
//! const N: LedgerCell<Uint<64, Public>> = LedgerCell::at(0);
//! const M: LedgerCell<Uint<64, Public>> = LedgerCell::at(1);
//! let n = N.read(&mut c);
//! // error[E0277]: the ledger does not store `Assumed<Uint<64, Public>>`: it is what an inline read returned
//! M.write(&mut c, &n);
//! ```
//!
//! The types track DIRECT read results. A value computed from one — `*n`
//! through the deref, `n.field()`, a hash of it — is a bare wire, and Rust's
//! types do not carry where it came from. The circuit builder does
//! (`Circuit3::refuse_stale`): at the ledger boundary — a hook argument, an
//! inline write's value — it walks the value's provenance and refuses one
//! that descends from a read not acknowledged by `stale`, naming the read.
//! A build-time error, the last rung of the rejection ladder, recorded for
//! dmd's review. Map KEYS are exempt: a key derived from a read (a request
//! id from a nonce) adds no assumption the read's own `popeq` does not
//! already make.
//!
//! What is NOT wrapped: [`kernel::self_address`](super::kernel::self_address)
//! — the contract's own address is a read, but of a value no transaction
//! can change.

use core::ops::Deref;

use minocrab::v3::{Circuit3, FieldT, Select, Val, Wire3};
use minocrab::Visibility;

use super::predicate::{Check, CheckOperand};
use super::{Bool, Vis3};

/// The wires a value is made of, for [`Assumed::stale`] to walk. Every
/// ledger leaf and derived record has it; tuples of them do too.
pub trait ProofWires {
    /// Append this value's wires, in slot order.
    fn push_wires(&self, out: &mut Vec<Val>);
}

macro_rules! tuple_wires {
    ($( ($($t:ident $i:tt),+) ),* $(,)?) => {$(
        impl<$($t: ProofWires),+> ProofWires for ($($t,)+) {
            fn push_wires(&self, out: &mut Vec<Val>) {
                $( self.$i.push_wires(out); )+
            }
        }
    )*};
}

tuple_wires! {
    (A 0, B 1),
    (A 0, B 1, C 2),
    (A 0, B 1, C 2, D 3),
}

impl ProofWires for Wire3<FieldT, minocrab::Public> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        out.push(self.val());
    }
}

impl<T: ProofWires> ProofWires for Assumed<T> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        self.0.push_wires(out)
    }
}

/// A value an inline ledger read returned: what the transaction ASSUMES
/// the slot holds at landing. See the module docs.
#[derive(Clone, Copy, Debug)]
pub struct Assumed<T>(T);

impl<T> Assumed<T> {
    /// Wrap a read's result. For the read implementations; contract code
    /// receives these, it does not make them.
    #[doc(hidden)]
    pub fn of_read(value: T) -> Self {
        Assumed(value)
    }

    /// The value, with the assumption NAMED: the transaction relies on the
    /// slot still holding what was read, and a landed transaction that
    /// changed it fails this one. Every read behind the value is recorded
    /// as acknowledged, so what is computed from it may re-enter the
    /// ledger. Takes `c` because the record lives in the circuit.
    pub fn stale(self, c: &mut Circuit3) -> T
    where
        T: ProofWires,
    {
        let mut wires = Vec::new();
        self.0.push_wires(&mut wires);
        c.acknowledge_stale(&wires);
        self.0
    }

    /// A proof-side transformation that keeps the wrapper: the result is
    /// still an assumption about the ledger.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Assumed<U> {
        Assumed(f(self.0))
    }

    /// The value with the wrapper dropped, for the library's own
    /// compositions (a kernel comparison built from a kernel read). Not
    /// `stale`: it records nothing.
    pub(crate) fn into_inner(self) -> T {
        self.0
    }
}

impl<T> Deref for Assumed<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

/// Selecting between two assumptions is an assumption.
impl<V: Visibility, T: Select<V>> Select<V> for Assumed<T> {
    fn select(c: &mut Circuit3, bit: Wire3<FieldT, V>, taken: Self, fallback: Self) -> Self {
        Assumed(T::select(c, bit, taken.0, fallback.0))
    }
}

/// Comparisons take an assumed operand as they take the value.
impl<T: CheckOperand> CheckOperand for Assumed<T> {
    type Vis = T::Vis;
    const BITS: Option<u32> = T::BITS;
    const MAX: Option<u128> = T::MAX;

    fn literal(&self) -> Option<minocrab::Fr> {
        self.0.literal()
    }

    fn operand(self) -> minocrab::v3::Operand<FieldT, T::Vis> {
        self.0.operand()
    }
}

/// An assumed boolean is a boolean to the proof: `is_true`, `c.when`,
/// `c.assert` all take it.
impl<V: Vis3> From<Assumed<Bool<V>>> for Bool<V> {
    fn from(b: Assumed<Bool<V>>) -> Bool<V> {
        b.0
    }
}

impl<V: Vis3> From<Assumed<Bool<V>>> for Check<V> {
    fn from(b: Assumed<Bool<V>>) -> Check<V> {
        super::predicate::is_true(b.0)
    }
}

impl<V: Vis3> minocrab::v3::GuardCond<V> for Assumed<Bool<V>> {
    fn into_guard(self, c: &mut Circuit3) -> Wire3<FieldT, V> {
        self.0.into_guard(c)
    }
}
