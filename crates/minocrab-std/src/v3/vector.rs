//! BOUNDED AND NON-EMPTY VECTORS (M40 C, notes/stream-design.org): a
//! variable-length circuit argument, as a length plus a contiguous prefix.
//!
//! Compact's circuits have only the fixed `Vector<N, T>`; variable length is
//! hand-rolled as a vector plus a length, or a `Maybe` per slot (the
//! corpus's `Vector<5000, Maybe<…>>`), and non-emptiness is only ever a
//! runtime assert. Here:
//!
//! - [`Bounded<T, MAX>`]: `len: Uint<8>` and `[T; MAX]`, the first `len`
//!   slots live, no holes. ONE length limb instead of `MAX` tags; the live
//!   wire for slot `i` is a compare against the constant `i`. The length is
//!   range-checked against `MAX` in-circuit by the argument constraint
//!   table (its primitive type is `Uint<0..MAX + 1>`, so the check is
//!   compactc's own `less_than` + `assert`, or a bit constraint when
//!   `MAX + 1` is a power of two).
//! - [`NonEmpty<T, REST>`]: a structural head plus a `Bounded<T, REST>`
//!   tail, width `REST + 1`. `REST` counts the OPTIONAL slots
//!   (`NonEmpty<K, 3>` holds one to four), because an array of length
//!   `N − 1` is not expressible on stable. The all-empty case is
//!   unexpressible: there is no constructor without a head.
//!
//! ITERATION IS INTERNAL. [`Bounded::fold`] and [`Bounded::for_each`] own
//! the [`Circuit3::when`] guard AND the select on the carried state, so an
//! author never hand-rolls either. A `for` loop cannot do this: it runs its
//! body between `next` calls, so an iterator could push a `when` scope in
//! `next` (the ambient guard) but could not insert the select on state
//! assigned in the body, and a for-loop fold would silently apply dead
//! steps. [`Bounded::iter`] yields `(live, &T)` for PURE wire computations
//! (hashing every slot, digests) — no ledger ops and no carried state
//! without the author's own select — and the witness-side `Vec` has
//! ordinary iteration. The scoped-`next` trick is deliberately not built.
//!
//! The step is evaluated on EVERY slot, dead ones included, and applied by
//! select only where live (a circuit does not branch), so it must be total
//! on the default value: a dead slot's `T` is whatever the witness padded
//! with, and any ledger op inside the step is skipped on chain by the
//! guard. Proof cost is the full `MAX` whatever the length; the ledger
//! applies `len` steps.
//!
//! The witness side pads: [`Bounded::pad`] takes up to `MAX` items and
//! [`NonEmpty::split`] takes one to `REST + 1`, both refusing anything else
//! before a proof is attempted.

use minocrab::v3::{Circuit3, CircuitAbi, Disclose, DisclosureLabel, FieldT, Prim, Select, Wire3};
use minocrab::{AlignmentAtom, Private, Public};

use super::entry::{ArgPath, CircuitArg};
use super::{Bool, Uint, Vis3};

/// Up to `MAX` values of `T`: a length and a contiguous live prefix.
#[derive(Clone, Copy)]
pub struct Bounded<T, const MAX: usize, V: Vis3 = Private> {
    len: Uint<8, V>,
    slots: [T; MAX],
}

impl<T, const MAX: usize, V: Vis3> Bounded<T, MAX, V> {
    /// Assemble from parts already in hand. UNCHECKED: nothing here
    /// constrains `len <= MAX`, which the argument constraint does for a
    /// declared argument. For a value computed in-circuit the caller owns
    /// that invariant.
    pub fn from_parts_unchecked(len: Uint<8, V>, slots: [T; MAX]) -> Self {
        Bounded { len, slots }
    }

    /// The length limb.
    pub fn len(&self) -> Uint<8, V> {
        self.len
    }

    /// Every slot, live or not — for the witness-side view and for pure
    /// computations that pair it with [`Bounded::iter`]'s live bits.
    pub fn slots(&self) -> &[T; MAX] {
        &self.slots
    }

    /// Apply `f` to every slot, live or not: a PURE map (no ledger ops
    /// inside — the guard is not applied here), for reshaping or
    /// disclosing the elements.
    pub fn map<U>(self, c: &mut Circuit3, mut f: impl FnMut(&mut Circuit3, T) -> U) -> Bounded<U, MAX, V> {
        let mut out = Vec::with_capacity(MAX);
        for slot in self.slots {
            out.push(f(c, slot));
        }
        Bounded {
            len: self.len,
            slots: match <[U; MAX]>::try_from(out) {
                Ok(slots) => slots,
                Err(_) => unreachable!("one output per slot"),
            },
        }
    }
}

impl<T, const MAX: usize> Bounded<T, MAX, Private> {
    /// Disclose the LENGTH only, keeping the elements private — what a fold
    /// over private data needs (the guard must be public; whether a slot's
    /// step ran is visible on chain).
    pub fn disclose_len_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Bounded<T, MAX, Public> {
        Bounded {
            len: self.len.disclose_as::<L>(c),
            slots: self.slots,
        }
    }
}

impl<T, const MAX: usize> Bounded<T, MAX, Public> {
    /// Is slot `i` live: `i < len`, one 8-bit compare against the constant.
    pub fn live(&self, c: &mut Circuit3, i: usize) -> Bool<Public> {
        Bool::from_field_unchecked(c.less_than(i as u64, self.len.field(), 8))
    }

    /// THE FOLD: `step` over the live prefix, in order. Each slot's step
    /// runs under `c.when(live, …)`, so its ledger ops are skipped on chain
    /// where the slot is dead, and the carried state is SELECTED — the
    /// step's result where live, the previous state where not — so a dead
    /// step never lands in the state either.
    pub fn fold<S: Clone + Select<Public>>(
        &self,
        c: &mut Circuit3,
        init: S,
        mut step: impl FnMut(&mut Circuit3, S, &T) -> S,
    ) -> S {
        let mut s = init;
        for (i, slot) in self.slots.iter().enumerate() {
            let live = self.live(c, i);
            let prev = s.clone();
            s = c.when(live, |c| step(c, prev, slot)).or(s);
        }
        s
    }

    /// [`Bounded::fold`] without carried state: `body` under the guard, per
    /// live slot.
    pub fn for_each(&self, c: &mut Circuit3, mut body: impl FnMut(&mut Circuit3, &T)) {
        for (i, slot) in self.slots.iter().enumerate() {
            let live = self.live(c, i);
            c.when(live, |c| body(c, slot));
        }
    }

    /// `(live, &slot)` for every slot, for PURE wire computations only:
    /// nothing here is guarded, so a ledger op in the loop body would run
    /// on chain for dead slots too, and state carried across iterations
    /// needs the caller's own select. Use [`Bounded::fold`] for either.
    pub fn iter(&self, c: &mut Circuit3) -> impl Iterator<Item = (Bool<Public>, &T)> {
        let lives: Vec<Bool<Public>> = (0..MAX).map(|i| self.live(c, i)).collect();
        lives.into_iter().zip(self.slots.iter())
    }
}

impl<X: Clone, const MAX: usize> Bounded<X, MAX, Private> {
    /// The WITNESS-SIDE constructor's padding: `items` (at most `MAX` of
    /// them) followed by `default`, and the length. Refuses more than `MAX`
    /// items here, before any proof.
    pub fn pad(items: &[X], default: X) -> (u8, [X; MAX]) {
        assert!(
            items.len() <= MAX,
            "Bounded<_, {MAX}>: {} items do not fit",
            items.len()
        );
        assert!(MAX <= 255, "Bounded's length is a byte");
        let mut slots = Vec::with_capacity(MAX);
        slots.extend_from_slice(items);
        slots.resize(MAX, default);
        match <[X; MAX]>::try_from(slots) {
            Ok(slots) => (items.len() as u8, slots),
            Err(_) => unreachable!("resized to MAX"),
        }
    }
}

impl<T: CircuitAbi, const MAX: usize, V: Vis3> CircuitAbi for Bounded<T, MAX, V> {
    const SLOTS: usize = 1 + MAX * T::SLOTS;

    fn push_atoms(atoms: &mut Vec<AlignmentAtom>) {
        atoms.push(AlignmentAtom::Bytes { length: 1 });
        for _ in 0..MAX {
            T::push_atoms(atoms);
        }
    }

    /// The length's primitive type is `Uint<0..MAX + 1>`: the constraint
    /// table turns that into the range check (`less_than` + `assert`, or a
    /// bit constraint when `MAX + 1` is a power of two).
    fn push_prims(prims: &mut Vec<Prim>) {
        prims.push(Prim::unsigned(MAX as u128));
        for _ in 0..MAX {
            T::push_prims(prims);
        }
    }
}

impl<T: CircuitArg, const MAX: usize> CircuitArg for Bounded<T, MAX, Private> {
    fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
        const {
            assert!(
                MAX <= 255,
                "`Bounded<T, MAX>` needs MAX <= 255: the length is one byte"
            )
        }
        Bounded {
            len: <Uint<8, Private>>::declare(c, &path.field("len")),
            slots: <[T; MAX]>::declare(c, path),
        }
    }

    fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
        slots.push(self.len.field());
        self.slots.push_slots(slots);
    }
}

impl<T: Disclose, const MAX: usize> Disclose for Bounded<T, MAX, Private> {
    type Public = Bounded<T::Public, MAX, Public>;

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Self::Public {
        Bounded {
            len: self.len.disclose_as::<L>(c),
            slots: self.slots.disclose_as::<L>(c),
        }
    }
}

impl<T: Select<Public>, const MAX: usize> Select<Public> for Bounded<T, MAX, Public> {
    fn select(c: &mut Circuit3, bit: Wire3<FieldT, Public>, taken: Self, fallback: Self) -> Self {
        Bounded {
            len: Select::select(c, bit, taken.len, fallback.len),
            slots: Select::select(c, bit, taken.slots, fallback.slots),
        }
    }
}

/// One to `REST + 1` values of `T`: a structural head and a bounded tail.
#[derive(Clone, Copy)]
pub struct NonEmpty<T, const REST: usize, V: Vis3 = Private> {
    head: T,
    tail: Bounded<T, REST, V>,
}

impl<T, const REST: usize, V: Vis3> NonEmpty<T, REST, V> {
    /// Assemble from a head and a tail already in hand.
    pub fn from_parts(head: T, tail: Bounded<T, REST, V>) -> Self {
        NonEmpty { head, tail }
    }

    /// The element that is always there.
    pub fn head(&self) -> &T {
        &self.head
    }

    /// The optional rest.
    pub fn tail(&self) -> &Bounded<T, REST, V> {
        &self.tail
    }

    /// A pure map over head and tail (see [`Bounded::map`]).
    pub fn map<U>(self, c: &mut Circuit3, mut f: impl FnMut(&mut Circuit3, T) -> U) -> NonEmpty<U, REST, V> {
        let head = f(c, self.head);
        NonEmpty {
            head,
            tail: self.tail.map(c, f),
        }
    }
}

impl<T, const REST: usize> NonEmpty<T, REST, Private> {
    /// Disclose the tail's length only (see [`Bounded::disclose_len_as`]).
    pub fn disclose_len_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> NonEmpty<T, REST, Public> {
        NonEmpty {
            head: self.head,
            tail: self.tail.disclose_len_as::<L>(c),
        }
    }
}

impl<T, const REST: usize> NonEmpty<T, REST, Public> {
    /// [`Bounded::fold`] with the head folded FIRST and UNGUARDED: it is
    /// structural, so its step always runs and always lands.
    pub fn fold<S: Clone + Select<Public>>(
        &self,
        c: &mut Circuit3,
        init: S,
        mut step: impl FnMut(&mut Circuit3, S, &T) -> S,
    ) -> S {
        let s = step(c, init, &self.head);
        self.tail.fold(c, s, step)
    }

    /// [`Bounded::for_each`], the head first and unguarded.
    pub fn for_each(&self, c: &mut Circuit3, mut body: impl FnMut(&mut Circuit3, &T)) {
        body(c, &self.head);
        self.tail.for_each(c, body);
    }

    /// `(live, &slot)` for the head (live is the constant `true`) and every
    /// tail slot; pure computations only, as [`Bounded::iter`].
    pub fn iter(&self, c: &mut Circuit3) -> impl Iterator<Item = (Bool<Public>, &T)> {
        let head_live = Bool::from_field_unchecked(c.constant(1u64));
        core::iter::once((head_live, &self.head)).chain(self.tail.iter(c))
    }
}

impl<X: Clone, const REST: usize> NonEmpty<X, REST, Private> {
    /// The WITNESS-SIDE constructor's split: the first item as the head,
    /// the rest padded into the tail. Refuses an empty list and more than
    /// `REST + 1` items here, before any proof — the all-empty case has no
    /// circuit-side spelling at all.
    pub fn split(items: &[X], default: X) -> (X, u8, [X; REST]) {
        let (head, rest) = items
            .split_first()
            .expect("NonEmpty: at least one item");
        let (len, tail) = Bounded::<X, REST, Private>::pad(rest, default);
        (head.clone(), len, tail)
    }
}

impl<T: CircuitAbi, const REST: usize, V: Vis3> CircuitAbi for NonEmpty<T, REST, V> {
    const SLOTS: usize = T::SLOTS + <Bounded<T, REST, V> as CircuitAbi>::SLOTS;

    fn push_atoms(atoms: &mut Vec<AlignmentAtom>) {
        T::push_atoms(atoms);
        <Bounded<T, REST, V>>::push_atoms(atoms);
    }

    fn push_prims(prims: &mut Vec<Prim>) {
        T::push_prims(prims);
        <Bounded<T, REST, V>>::push_prims(prims);
    }
}

impl<T: CircuitArg, const REST: usize> CircuitArg for NonEmpty<T, REST, Private> {
    fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
        NonEmpty {
            head: T::declare(c, &path.field("head")),
            tail: <Bounded<T, REST, Private>>::declare(c, &path.field("tail")),
        }
    }

    fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
        self.head.push_slots(slots);
        self.tail.push_slots(slots);
    }
}

impl<T: Disclose, const REST: usize> Disclose for NonEmpty<T, REST, Private> {
    type Public = NonEmpty<T::Public, REST, Public>;

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Self::Public {
        NonEmpty {
            head: self.head.disclose_as::<L>(c),
            tail: self.tail.disclose_as::<L>(c),
        }
    }
}
