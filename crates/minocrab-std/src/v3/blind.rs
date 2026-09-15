//! BLIND ACCUMULATORS (M40, notes/stream-design.org): the steps the ledger
//! applies ITSELF, with no `popeq` and therefore nothing that can go stale.
//!
//! A ledger read is a fetch plus a `popeq` equality check against the
//! proof's public input, and that check is the only thing a landed
//! transaction can invalidate. A fetch-and-store or a fetch-combine-store
//! has no check: `Counter.increment` (`idxp; addi; insc`) is why concurrent
//! increments never conflict. Impact's real op set (Lt Neg And Or Add Branch
//! Jmp Dup Swap Pop Idx Ins) can do the same for a small algebra, and this
//! module names it:
//!
//! | step | state | identity | ledger spelling |
//! |---|---|---|---|
//! | [`Add`] | `Uint<BITS ≤ 64>` | 0 | `idxp; push Δ; add; insc` |
//! | [`Max`] | `Uint<BITS ≤ 64>` | 0 | `idxp; pushs Δ; dup 1; dup 1; lt; neg; branch 3; swap 0; pop; jmp 1; pop; insc` |
//! | [`Min`] | `Uint<BITS ≤ 64>` | max | the same without the `neg` |
//! | [`And`] | `Bool` | true | `idxp; push Δ; and; insc` |
//! | [`Or`] | `Bool` | false | `idxp; push Δ; or; insc` |
//! | [`Last`] | any | (none) | a cell write |
//! | [`First`] | any | (none) | `dup 0; idx flag; branch k; write value; write flag` |
//!
//! Tuples of primitives are primitives ([`Primitive`] for `(A, B)` up to
//! four components), laid out as ONE CELL PER COMPONENT and one snapshot
//! map per component: Impact addresses whole cell values, not fields of a
//! struct in a cell, so a tuple state cannot share a cell. A component that
//! is not a primitive is a missing impl:
//!
//! ```compile_fail
//! # use minocrab::Public;
//! # use minocrab_std::v3::{blind::{Add, Primitive}, Uint};
//! struct Ema;
//! // error[E0277]: the trait bound `Ema: Primitive<Uint<64, Public>>` is not satisfied
//! fn needs<P: Primitive<S>, S>() {}
//! needs::<(Add, Ema), (Uint<64, Public>, Uint<64, Public>)>();
//! ```
//!
//! Two traits, because two of the seven are not monoids. [`Primitive`] is
//! the LEDGER side: the accumulator's layout, the blind combine, the blind
//! snapshot into a per-key map, and reading the snapshot back. [`Monoid`]
//! adds the CIRCUIT side — an identity and a combine on wires — which
//! `Last` and `First` cannot have (their "identity" is the empty slot, and
//! on the ledger `First` needs a flag cell to say so).
//!
//! No `Mul` and no hash op exist on the ledger, so a running product or a
//! hash chain is monoidal on paper and not blind-combinable; a
//! non-monoidal step (a moving average, threshold-replace) is a
//! [`super::stream::Fold`] behind the popeq read instead.
//!
//! Nothing here is expressible in Compact, so there is no compactc
//! differential; the gate is Midnight's on-chain VM
//! (`tests/v3_blind.rs` runs each transcript on a seeded state and reads
//! the cells back).

use minocrab::v3::Circuit3;
use minocrab::Public;
use minocrab_ledger::{
    cell_add_at, cell_and_at, cell_max_at, cell_min_at, cell_or_at, cell_write_at,
    cell_write_first_at, emit,
};

use super::ledger::{LedgerCell, LedgerMap, LedgerRepr};
use super::{Bool, Uint};

/// A step the LEDGER executes: an accumulator laid out as one or more cells,
/// combined with a public delta and copied into a per-key snapshot map
/// without the circuit ever reading it.
///
/// `S` is the state type as the circuit sees it (a leaf, or a tuple of
/// leaves for a tuple step); [`Self::Acc`] and [`Self::Snapshot`] are the
/// ledger handles that hold it, one field per component.
pub trait Primitive<S>: Sized {
    /// Ledger fields the accumulator occupies.
    const ACC_FIELDS: usize;
    /// Ledger fields the snapshot maps occupy (one per component).
    const SNAPSHOT_FIELDS: usize;
    /// The accumulator handle(s).
    type Acc;
    /// The per-key snapshot map(s), keyed by `K`.
    type Snapshot<K>;

    /// The accumulator's handles from flat field `start` of a block of
    /// `total` fields — what a nested ledger struct's constructor calls.
    fn acc_at_block(total: usize, start: usize) -> Self::Acc;
    /// The snapshot maps' handles, likewise.
    fn snapshot_at_block<K>(total: usize, start: usize) -> Self::Snapshot<K>;

    /// `acc ⊕= delta`, blind: no public input, nothing to go stale.
    fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &S);
    /// `snapshot[key] = acc`, blind, one copy per component.
    fn snapshot<K: LedgerRepr>(c: &mut Circuit3, acc: &Self::Acc, snapshot: &Self::Snapshot<K>, key: &K);
    /// `snapshot[key]`, a STABLE read: the entry is written once, at the
    /// snapshot, and never changes, so its `popeq` cannot go stale.
    fn lookup<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) -> S;
    /// Remove `snapshot[key]` in every component.
    fn remove<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K);
    /// [`Self::lookup`] then [`Self::remove`].
    fn take<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) -> S {
        let value = Self::lookup(c, snapshot, key);
        Self::remove(c, snapshot, key);
        value
    }
}

/// The CIRCUIT side of a primitive that is a monoid: an identity and a
/// combine on wires, agreeing with the ledger's. What a batch of deltas
/// folds under in-circuit, and what a tuple step is componentwise.
pub trait Monoid<S>: Primitive<S> {
    /// The identity: `combine(identity, x) == x`.
    fn identity(c: &mut Circuit3) -> S;
    /// `a ⊕ b` on wires. UNCHECKED where the ledger's is checked: `Add`
    /// emits one `add` and no range check, as compactc's `+` does not, so a
    /// sum that would overflow the width is the caller's to bound; the
    /// ledger's blind `add` fails the transaction instead.
    fn combine(c: &mut Circuit3, a: S, b: S) -> S;
}

/// `acc += Δ` on a `Uint` cell.
#[derive(Clone, Copy, Debug, Default)]
pub struct Add;
/// `acc = max(acc, Δ)` on a `Uint` cell.
#[derive(Clone, Copy, Debug, Default)]
pub struct Max;
/// `acc = min(acc, Δ)` on a `Uint` cell.
#[derive(Clone, Copy, Debug, Default)]
pub struct Min;
/// `acc = acc && Δ` on a `Boolean` cell.
#[derive(Clone, Copy, Debug, Default)]
pub struct And;
/// `acc = acc || Δ` on a `Boolean` cell.
#[derive(Clone, Copy, Debug, Default)]
pub struct Or;
/// `acc = Δ`: a plain overwrite, the last delta wins. Any stored type.
#[derive(Clone, Copy, Debug, Default)]
pub struct Last;
/// `acc = Δ` only if nothing has been written yet: the first delta wins.
/// Two cells on the ledger — the value and a written flag.
#[derive(Clone, Copy, Debug, Default)]
pub struct First;

/// The one-cell layout every scalar step but [`First`] has.
macro_rules! one_cell {
    ($S:ty) => {
        const ACC_FIELDS: usize = 1;
        const SNAPSHOT_FIELDS: usize = 1;
        type Acc = LedgerCell<$S>;
        type Snapshot<K> = LedgerMap<K, $S>;

        fn acc_at_block(total: usize, start: usize) -> Self::Acc {
            LedgerCell::at_block(total, start)
        }

        fn snapshot_at_block<K>(total: usize, start: usize) -> Self::Snapshot<K> {
            LedgerMap::at_block(total, start)
        }

        fn snapshot<K: LedgerRepr>(
            c: &mut Circuit3,
            acc: &Self::Acc,
            snapshot: &Self::Snapshot<K>,
            key: &K,
        ) {
            acc.snapshot_into(c, snapshot, key)
        }

        fn lookup<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) -> $S {
            snapshot.lookup(c, key)
        }

        fn remove<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) {
            snapshot.remove(c, key)
        }
    };
}

/// The `Uint` widths the VM's `add` and `lt` handle: they decode the cell
/// as a `u64` (onchain-vm `vm.rs`), so anything wider is a missing impl.
macro_rules! uint_steps {
    ($($bits:literal),*) => {$(
        impl Primitive<Uint<$bits, Public>> for Add {
            one_cell!(Uint<$bits, Public>);

            fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &Uint<$bits, Public>) {
                let delta = delta.ledger_value(c);
                emit(c, &cell_add_at(&acc.ledger_path(), &delta));
            }
        }

        impl Monoid<Uint<$bits, Public>> for Add {
            fn identity(c: &mut Circuit3) -> Uint<$bits, Public> {
                Uint::from_field_unchecked(c.constant(0u64))
            }

            fn combine(c: &mut Circuit3, a: Uint<$bits, Public>, b: Uint<$bits, Public>) -> Uint<$bits, Public> {
                Uint::from_field_unchecked(c.add(a.field(), b.field()))
            }
        }

        impl Primitive<Uint<$bits, Public>> for Max {
            one_cell!(Uint<$bits, Public>);

            fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &Uint<$bits, Public>) {
                let delta = delta.ledger_value(c);
                emit(c, &cell_max_at(&acc.ledger_path(), &delta));
            }
        }

        impl Monoid<Uint<$bits, Public>> for Max {
            fn identity(c: &mut Circuit3) -> Uint<$bits, Public> {
                Uint::from_field_unchecked(c.constant(0u64))
            }

            fn combine(c: &mut Circuit3, a: Uint<$bits, Public>, b: Uint<$bits, Public>) -> Uint<$bits, Public> {
                let a_below = c.less_than(a.field(), b.field(), $bits);
                Uint::from_field_unchecked(c.cond_select(a_below, b.field(), a.field()))
            }
        }

        impl Primitive<Uint<$bits, Public>> for Min {
            one_cell!(Uint<$bits, Public>);

            fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &Uint<$bits, Public>) {
                let delta = delta.ledger_value(c);
                emit(c, &cell_min_at(&acc.ledger_path(), &delta));
            }
        }

        impl Monoid<Uint<$bits, Public>> for Min {
            fn identity(c: &mut Circuit3) -> Uint<$bits, Public> {
                Uint::from_field_unchecked(c.constant(u64::MAX >> (64 - $bits)))
            }

            fn combine(c: &mut Circuit3, a: Uint<$bits, Public>, b: Uint<$bits, Public>) -> Uint<$bits, Public> {
                let a_below = c.less_than(a.field(), b.field(), $bits);
                Uint::from_field_unchecked(c.cond_select(a_below, a.field(), b.field()))
            }
        }
    )*};
}

uint_steps!(8, 16, 32, 64);

impl Primitive<Bool<Public>> for And {
    one_cell!(Bool<Public>);

    fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &Bool<Public>) {
        let delta = delta.ledger_value(c);
        emit(c, &cell_and_at(&acc.ledger_path(), &delta));
    }
}

impl Monoid<Bool<Public>> for And {
    fn identity(c: &mut Circuit3) -> Bool<Public> {
        Bool::from_field_unchecked(c.constant(1u64))
    }

    fn combine(c: &mut Circuit3, a: Bool<Public>, b: Bool<Public>) -> Bool<Public> {
        Bool::from_field_unchecked(c.mul(a.field(), b.field()))
    }
}

impl Primitive<Bool<Public>> for Or {
    one_cell!(Bool<Public>);

    fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &Bool<Public>) {
        let delta = delta.ledger_value(c);
        emit(c, &cell_or_at(&acc.ledger_path(), &delta));
    }
}

impl Monoid<Bool<Public>> for Or {
    fn identity(c: &mut Circuit3) -> Bool<Public> {
        Bool::from_field_unchecked(c.constant(0u64))
    }

    /// `a || b = a + b − a·b`.
    fn combine(c: &mut Circuit3, a: Bool<Public>, b: Bool<Public>) -> Bool<Public> {
        let both = c.mul(a.field(), b.field());
        let sum = c.add(a.field(), b.field());
        let neg = c.neg(both);
        Bool::from_field_unchecked(c.add(sum, neg))
    }
}

impl<S: LedgerRepr> Primitive<S> for Last {
    one_cell!(S);

    fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &S) {
        acc.write(c, delta)
    }
}

/// [`First`]'s two cells: the value, and whether it has been written.
pub struct FirstAcc<S> {
    /// The value, meaningful once `written` is set.
    pub value: LedgerCell<S>,
    /// `true` once the first delta has landed.
    pub written: LedgerCell<Bool<Public>>,
}

impl<S: LedgerRepr> Primitive<S> for First {
    const ACC_FIELDS: usize = 2;
    const SNAPSHOT_FIELDS: usize = 1;
    type Acc = FirstAcc<S>;
    type Snapshot<K> = LedgerMap<K, S>;

    fn acc_at_block(total: usize, start: usize) -> Self::Acc {
        FirstAcc {
            value: LedgerCell::at_block(total, start),
            written: LedgerCell::at_block(total, start + 1),
        }
    }

    fn snapshot_at_block<K>(total: usize, start: usize) -> Self::Snapshot<K> {
        LedgerMap::at_block(total, start)
    }

    fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &S) {
        let delta = delta.ledger_value(c);
        emit(
            c,
            &cell_write_first_at(&acc.value.ledger_path(), &acc.written.ledger_path(), &delta),
        );
    }

    fn snapshot<K: LedgerRepr>(c: &mut Circuit3, acc: &Self::Acc, snapshot: &Self::Snapshot<K>, key: &K) {
        acc.value.snapshot_into(c, snapshot, key)
    }

    fn lookup<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) -> S {
        snapshot.lookup(c, key)
    }

    fn remove<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) {
        snapshot.remove(c, key)
    }
}

/// Tuples: one cell and one snapshot map per component, laid out in order,
/// each op applied componentwise.
macro_rules! tuple_steps {
    ($( ($($p:ident $s:ident $i:tt),+) ),* $(,)?) => {$(
        impl<$($p: Primitive<$s>, $s),+> Primitive<($($s,)+)> for ($($p,)+) {
            const ACC_FIELDS: usize = 0 $(+ $p::ACC_FIELDS)+;
            const SNAPSHOT_FIELDS: usize = 0 $(+ $p::SNAPSHOT_FIELDS)+;
            type Acc = ($($p::Acc,)+);
            type Snapshot<K> = ($($p::Snapshot<K>,)+);

            #[allow(unused_assignments)]
            fn acc_at_block(total: usize, start: usize) -> Self::Acc {
                let mut at = start;
                ($({
                    let acc = $p::acc_at_block(total, at);
                    at += $p::ACC_FIELDS;
                    acc
                },)+)
            }

            #[allow(unused_assignments)]
            fn snapshot_at_block<K>(total: usize, start: usize) -> Self::Snapshot<K> {
                let mut at = start;
                ($({
                    let snapshot = $p::snapshot_at_block::<K>(total, at);
                    at += $p::SNAPSHOT_FIELDS;
                    snapshot
                },)+)
            }

            fn combine_blind(c: &mut Circuit3, acc: &Self::Acc, delta: &($($s,)+)) {
                $( $p::combine_blind(c, &acc.$i, &delta.$i); )+
            }

            fn snapshot<K: LedgerRepr>(c: &mut Circuit3, acc: &Self::Acc, snapshot: &Self::Snapshot<K>, key: &K) {
                $( $p::snapshot(c, &acc.$i, &snapshot.$i, key); )+
            }

            fn lookup<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) -> ($($s,)+) {
                ($( $p::lookup(c, &snapshot.$i, key), )+)
            }

            fn remove<K: LedgerRepr>(c: &mut Circuit3, snapshot: &Self::Snapshot<K>, key: &K) {
                $( $p::remove(c, &snapshot.$i, key); )+
            }
        }

        impl<$($p: Monoid<$s>, $s),+> Monoid<($($s,)+)> for ($($p,)+) {
            fn identity(c: &mut Circuit3) -> ($($s,)+) {
                ($( $p::identity(c), )+)
            }

            fn combine(c: &mut Circuit3, a: ($($s,)+), b: ($($s,)+)) -> ($($s,)+) {
                ($( $p::combine(c, a.$i, b.$i), )+)
            }
        }
    )*};
}

tuple_steps! {
    (A SA 0, B SB 1),
    (A SA 0, B SB 1, C SC 2),
    (A SA 0, B SB 1, C SC 2, D SD 3),
}

// `cell_write_at` is what `Last` is; named here so the table above and the
// import list agree on what this module emits.
#[allow(dead_code)]
const _LAST_IS_A_CELL_WRITE: fn(&[minocrab_ledger::LedgerKey], &minocrab_ledger::LedgerValue) -> Vec<minocrab_ledger::ImpactOp> = cell_write_at;
