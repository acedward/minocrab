//! THE STREAM (M41, notes/stream-design.org, DECIDED "option one"): insert
//! out of order under your own key, sequence a chosen subset through one
//! shared accumulator, take one element at a time.
//!
//! A [`StreamSpec`] names the key, the body (what only `take` sees), the
//! head (what the step may look at), the state, and the STEP. The step is
//! either
//!
//! - a PRIMITIVE ([`super::blind::Primitive`]: `Add`, `Max`, `Min`, `And`,
//!   `Or`, `Last`, `First`, or a tuple of them): the stream is
//!   [`ContentionFree`] — `insert` sequences ITSELF (blind combine, then
//!   blind snapshot, so the stored state is the post-step value), `take`
//!   reads two stable entries, `combine` is blind, and there is NO
//!   `sequence` circuit; or
//! - [`Serial<F, REST>`] over a [`Fold`] of real code: `insert` is a pure
//!   insert, `sequence(c, keys)` reads the accumulator ONCE (the one
//!   `popeq`, the one contention point: a landed flush stales every other
//!   flush proven against the old state, one step per block worst case),
//!   folds the step under the fold's guard over one to `REST + 1` keys,
//!   stages the post-step state per key, and writes the accumulator once.
//!
//! Insert, take and combine have the same signatures on both; the only
//! author-visible differences are the step type and whether `sequence`
//! exists. The layouts:
//!
//! | step | ledger fields beyond `bodies` |
//! |---|---|
//! | primitive | one accumulator cell and one snapshot map per component |
//! | `Serial<F, REST>` | `heads`, `acc`, `staged` |
//!
//! Two things are compile errors by construction. `sequence` on a
//! primitive stream does not exist:
//!
//! ```compile_fail
//! # use minocrab::v3::Circuit3;
//! # use minocrab::Public;
//! # use minocrab_std::v3::{blind::Add, NonEmpty, Stream, StreamSpec, Uint};
//! struct Count;
//! impl StreamSpec for Count {
//!     type Key = Uint<64, Public>; type Body = Uint<64, Public>; type Head = (); type State = Uint<64, Public>;
//!     type Step = Add;
//!     fn head(_c: &mut Circuit3, _b: &Uint<64, Public>) {}
//!     fn delta(c: &mut Circuit3, _h: &()) -> Uint<64, Public> { Uint::from_field_unchecked(c.constant(1u64)) }
//! }
//! const S: Stream<Count> = Stream::at_block(3, 0);
//! fn flush(c: &mut Circuit3, keys: NonEmpty<Uint<64, Public>, 3, Public>) {
//!     // error[E0599]: no method named `sequence` found
//!     S.sequence(c, keys);
//! }
//! ```
//!
//! And a `Fold` is not a step on its own — it goes through `Serial`, so a
//! type cannot be both a primitive and a fold (they are different
//! traits, and `Serial<Add, 3>` is E0277 because `Add` is not a `Fold`):
//!
//! ```compile_fail
//! # use minocrab::v3::Circuit3;
//! # use minocrab::Public;
//! # use minocrab_std::v3::{Fold, Stream, StreamSpec, Uint};
//! struct Ema;
//! impl Fold<Uint<64, Public>> for Ema {
//!     type Delta = Uint<64, Public>;
//!     fn step(c: &mut Circuit3, s: Uint<64, Public>, d: Uint<64, Public>) -> Uint<64, Public> { d }
//! }
//! struct Fees;
//! impl StreamSpec for Fees {
//!     type Key = Uint<64, Public>; type Body = Uint<64, Public>; type Head = Uint<64, Public>; type State = Uint<64, Public>;
//!     // error[E0277]: the trait bound `Ema: Step<Fees>` is not satisfied — wrap it: `Serial<Ema, 3>`
//!     type Step = Ema;
//!     fn head(_c: &mut Circuit3, b: &Uint<64, Public>) -> Uint<64, Public> { *b }
//!     fn delta(_c: &mut Circuit3, h: &Uint<64, Public>) -> Uint<64, Public> { *h }
//! }
//! ```
//!
//! The stream is a NESTED LEDGER STRUCT: `#[derive(Ledger)]` places it by
//! [`LedgerWidth`] and [`Stream::at_layout`], as it places `Pending` and the
//! other multi-field slots. The handles are built from the block position
//! when a method runs, because the layout is chosen by the step's trait and
//! a trait method cannot run in a `const` constructor.

use core::marker::PhantomData;

use minocrab::v3::{Circuit3, Select};
use minocrab::Public;

use super::assumed::{Assumed, ProofWires};
use super::blind::{Add, And, First, Last, Max, Min, Or, Primitive};
use super::hook::Hook;
use super::ledger::{BlockLayout, LedgerCell, LedgerMap, LedgerRepr, LedgerWidth};
use super::predicate::{is_true, not};
use super::state::{InitialState, StateBuilder};
use super::NonEmpty;

/// What a stream carries and how it steps.
pub trait StreamSpec: Sized {
    /// The key a writer picks — public, since map keys are disclosed.
    type Key: LedgerRepr;
    /// The payload: written at insert, read at take, never by the step.
    type Body: LedgerRepr;
    /// What the step may look at, a projection of the body. `()` when the
    /// step needs nothing from it (a count, a nonce).
    type Head;
    /// The accumulator's value, as the circuit sees it.
    type State;
    /// A primitive, or `Serial<F, REST>`.
    type Step: Step<Self>;

    /// The head of a body, computed in-circuit at insert.
    fn head(c: &mut Circuit3, body: &Self::Body) -> Self::Head;
    /// The step's delta for a head: `1` for a count, the height for a max.
    fn delta(c: &mut Circuit3, head: &Self::Head) -> <Self::Step as Step<Self>>::Delta;
}

/// A step's layout and the three operations every stream has. Implemented
/// for every [`Primitive`] and for [`Serial`]; not for authors.
pub trait Step<P: StreamSpec>: Sized {
    /// What [`StreamSpec::delta`] produces and [`Stream::combine`] takes.
    type Delta;
    /// Ledger fields the step's layout occupies beyond `bodies`.
    const WIDTH: usize;
    /// Whether `insert`, `take` and `combine` embed no read of shared state.
    const CONTENTION_FREE: bool;

    fn insert(s: &Stream<P>, c: &mut Circuit3, key: &P::Key, body: &P::Body);
    fn take(s: &Stream<P>, c: &mut Circuit3, key: &P::Key) -> (Assumed<P::Body>, Assumed<P::State>);
    fn combine(s: &Stream<P>, c: &mut Circuit3, delta: Self::Delta);
    /// The step's fields at deploy (notes/ledger-header.org): every cell at
    /// its default, every map empty. Off-chain; no circuit.
    fn contribute(s: &Stream<P>, state: &mut StateBuilder);
}

/// A step of real code, for [`Serial`]: `s ⊕ d` however the author likes,
/// behind the accumulator's `popeq`.
pub trait Fold<S> {
    /// What the step consumes per element.
    type Delta;
    /// The step. Evaluated on every slot of a flush, live or not, and
    /// applied by select where live — so it must be total on the default
    /// delta.
    fn step(c: &mut Circuit3, s: S, d: Self::Delta) -> S;
}

/// The serial step: `F`'s fold, flushed `1..=REST + 1` keys at a time by
/// [`Stream::sequence`]. Not [`ContentionFree`].
pub struct Serial<F, const REST: usize>(PhantomData<fn() -> F>);

/// The marker a primitive step earns: no operation of the stream reads
/// shared state, so no proof of one can be staled by another landing.
pub trait ContentionFree {}

/// The stream, placed in a ledger block.
///
/// It keeps its block's [`BlockLayout`] rather than building its handles in
/// the constructor (see the module docs), so every member handle is laid
/// out by the same value the block's own fields are.
pub struct Stream<P: StreamSpec> {
    layout: BlockLayout,
    start: usize,
    _p: PhantomData<fn() -> P>,
}

impl<P: StreamSpec> Stream<P> {
    /// The stream's fields from flat body index `start` under `layout` —
    /// what `#[derive(Ledger)]` emits for a field spelled `Stream<…>`.
    pub const fn at_layout(layout: BlockLayout, start: usize) -> Self {
        Stream {
            layout,
            start,
            _p: PhantomData,
        }
    }

    /// The stream's fields from flat index `start` of a block of `total`
    /// fields, at compactc's layout.
    pub const fn at_block(total: usize, start: usize) -> Self {
        Stream::at_layout(BlockLayout::compactc(total), start)
    }

    /// Handle → body. Field `start`.
    fn bodies(&self) -> LedgerMap<P::Key, P::Body> {
        LedgerMap::at_layout(self.layout, self.start)
    }

    /// INSERT under `key`: asserts the key is not present, stores the
    /// body, and on a primitive stream sequences the element at once.
    pub fn insert(&self, c: &mut Circuit3, key: &P::Key, body: &P::Body) {
        P::Step::insert(self, c, key, body)
    }

    /// TAKE `key`'s element: the body and the state it was sequenced with,
    /// removing everything read. Asserts the key is present.
    pub fn take(&self, c: &mut Circuit3, key: &P::Key) -> (Assumed<P::Body>, Assumed<P::State>) {
        P::Step::take(self, c, key)
    }

    /// COMBINE a delta with no element (a response raising last-seen).
    /// Blind on a primitive stream; on a serial stream it is a `popeq`
    /// read, the step, and a write — CONTENDED, like `sequence`.
    pub fn combine(&self, c: &mut Circuit3, delta: <P::Step as Step<P>>::Delta) {
        P::Step::combine(self, c, delta)
    }
}

impl<P: StreamSpec> LedgerWidth for Stream<P> {
    const WIDTH: usize = 1 + <P::Step as Step<P>>::WIDTH;
}

/// The bodies map, then the step's fields — each at its own default. The
/// accumulator starts at its cells' default, which is the identity of `Add`,
/// `Max` and `Or` and not of `Min` or `And`: `StateBuilder::set` the cell for
/// a stream that must start at the identity.
impl<P: StreamSpec> InitialState for Stream<P> {
    fn contribute(&self, state: &mut StateBuilder) {
        self.bodies().contribute(state);
        <P::Step as Step<P>>::contribute(self, state);
    }
}

impl<P: StreamSpec> ContentionFree for Stream<P> where P::Step: Primitive<P::State> {}

// ---- the primitive layout: bodies, then the step's cells and maps ---------------
//
// One impl per primitive TYPE rather than a blanket over `T: Primitive`:
// a blanket would overlap the `Serial` impl below (coherence cannot rule
// out a downstream `impl Primitive<TheirState> for Serial<…>`, since the
// state is a parameter of the trait). Each impl is bound to the specs
// whose step IS this type (`P: StreamSpec<Step = Self>`), which is also
// what lets `P::delta`'s result type normalize to the state.

macro_rules! primitive_steps {
    ($( [$($g:ident),*] $ty:ty ),* $(,)?) => {$(
        impl<P, $($g),*> Step<P> for $ty
        where
            P: StreamSpec<Step = $ty>,
            $ty: Primitive<P::State>,
        {
            type Delta = P::State;
            const WIDTH: usize = <$ty as Primitive<P::State>>::ACC_FIELDS
                + <$ty as Primitive<P::State>>::SNAPSHOT_FIELDS;
            const CONTENTION_FREE: bool = true;

            /// Assert not member; `bodies[k] = body` inline; then, as ONE
            /// attached hook, per component: blind `acc ⊕= delta(head(body))`,
            /// then blind `snapshot[k] = acc` — the stored state is the
            /// post-step value.
            fn insert(s: &Stream<P>, c: &mut Circuit3, key: &P::Key, body: &P::Body) {
                let bodies = s.bodies();
                let present = bodies.member(c, key);
                c.assert(not(is_true(present)).message("Stream key already present"));
                bodies.insert(c, key, body);
                let head = P::head(c, body);
                let delta = P::delta(c, &head);
                let acc = <$ty as Primitive<P::State>>::acc_at_layout(s.layout, s.start + 1);
                let snapshot = <$ty as Primitive<P::State>>::snapshot_at_layout::<P::Key>(
                    s.layout,
                    s.start + 1 + <$ty as Primitive<P::State>>::ACC_FIELDS,
                );
                // The blind half is a hook (M42): it runs after the body,
                // on whatever the accumulator holds at landing.
                let hook = <$ty as Primitive<P::State>>::combine(c, Hook::new(), &acc, &delta);
                let hook = <$ty as Primitive<P::State>>::snapshot(c, hook, &acc, &snapshot, key);
                c.then(hook);
            }

            /// Assert member; lookup and remove the body and each
            /// component's snapshot entry — every read is of an entry
            /// written once.
            fn take(s: &Stream<P>, c: &mut Circuit3, key: &P::Key) -> (Assumed<P::Body>, Assumed<P::State>) {
                let bodies = s.bodies();
                let present = bodies.member(c, key);
                c.assert(is_true(present).message("Stream key not present"));
                let body = bodies.lookup(c, key);
                bodies.remove(c, key);
                let snapshot = <$ty as Primitive<P::State>>::snapshot_at_layout::<P::Key>(
                    s.layout,
                    s.start + 1 + <$ty as Primitive<P::State>>::ACC_FIELDS,
                );
                let state = <$ty as Primitive<P::State>>::take(c, &snapshot, key);
                (body, state)
            }

            fn combine(s: &Stream<P>, c: &mut Circuit3, delta: P::State) {
                let acc = <$ty as Primitive<P::State>>::acc_at_layout(s.layout, s.start + 1);
                let hook = <$ty as Primitive<P::State>>::combine(c, Hook::new(), &acc, &delta);
                c.then(hook);
            }

            /// The accumulator's cells, then the snapshot maps.
            fn contribute(s: &Stream<P>, state: &mut StateBuilder) {
                <$ty as Primitive<P::State>>::acc_at_layout(s.layout, s.start + 1).contribute(state);
                <$ty as Primitive<P::State>>::snapshot_at_layout::<P::Key>(
                    s.layout,
                    s.start + 1 + <$ty as Primitive<P::State>>::ACC_FIELDS,
                )
                .contribute(state);
            }
        }
    )*};
}

primitive_steps! {
    [] Add, [] Max, [] Min, [] And, [] Or, [] Last, [] First,
    [A, B] (A, B),
    [A, B, C] (A, B, C),
    [A, B, C, D] (A, B, C, D),
}

// ---- the serial layout: bodies, heads, acc, staged -----------------------------------

impl<P, F, const REST: usize> Step<P> for Serial<F, REST>
where
    P: StreamSpec<Step = Serial<F, REST>>,
    F: Fold<P::State>,
    P::Head: LedgerRepr + ProofWires,
    P::State: LedgerRepr + ProofWires + Clone + Select<Public>,
{
    type Delta = F::Delta;
    const WIDTH: usize = 3;
    const CONTENTION_FREE: bool = false;

    /// Assert not member; `heads[k] = head(body)`; `bodies[k] = body`.
    fn insert(s: &Stream<P>, c: &mut Circuit3, key: &P::Key, body: &P::Body) {
        let bodies = s.bodies();
        let present = bodies.member(c, key);
        c.assert(not(is_true(present)).message("Stream key already present"));
        let head = P::head(c, body);
        s.heads().insert(c, key, &head);
        bodies.insert(c, key, body);
    }

    /// Assert staged; lookup and remove the staged state and the body.
    fn take(s: &Stream<P>, c: &mut Circuit3, key: &P::Key) -> (Assumed<P::Body>, Assumed<P::State>) {
        let staged = s.staged();
        let present = staged.member(c, key);
        c.assert(is_true(present).message("Stream key not sequenced"));
        let state = staged.lookup(c, key);
        staged.remove(c, key);
        let bodies = s.bodies();
        let body = bodies.lookup(c, key);
        bodies.remove(c, key);
        (body, state)
    }

    /// `popeq acc; step; write` — CONTENDED, and the write says so:
    /// `.stale(c)` names the read the write assumes current.
    fn combine(s: &Stream<P>, c: &mut Circuit3, delta: F::Delta) {
        let acc = s.acc();
        let state = acc.read(c).stale(c);
        let next = F::step(c, state, delta);
        acc.write(c, &next);
    }

    /// The heads map, the accumulator cell, the staged map.
    fn contribute(s: &Stream<P>, state: &mut StateBuilder) {
        s.heads().contribute(state);
        s.acc().contribute(state);
        s.staged().contribute(state);
    }
}

impl<P, F, const REST: usize> Stream<P>
where
    P: StreamSpec<Step = Serial<F, REST>>,
    F: Fold<P::State>,
    P::Head: LedgerRepr + ProofWires,
    P::State: LedgerRepr + ProofWires + Clone + Select<Public>,
{
    /// Handle → head. Field `start + 1`.
    fn heads(&self) -> LedgerMap<P::Key, P::Head> {
        LedgerMap::at_layout(self.layout, self.start + 1)
    }

    /// THE shared cell. Field `start + 2`.
    fn acc(&self) -> LedgerCell<P::State> {
        LedgerCell::at_layout(self.layout, self.start + 2)
    }

    /// Handle → the post-step state it was sequenced with. Field `start + 3`.
    fn staged(&self) -> LedgerMap<P::Key, P::State> {
        LedgerMap::at_layout(self.layout, self.start + 3)
    }

    /// SEQUENCE: the flusher's choice of subset AND order, one to `REST + 1`
    /// keys. Reads `acc` ONCE; per live key: asserts queued, looks up and
    /// removes the head, steps, stages the post-step state; writes `acc`
    /// once. The one `popeq` is the one contention point — a flush that
    /// lands stales every other flush proven against the old accumulator,
    /// and anyone may re-prove.
    pub fn sequence(&self, c: &mut Circuit3, keys: NonEmpty<P::Key, REST, Public>) {
        let heads = self.heads();
        let staged = self.staged();
        let acc = self.acc();
        // The one contended read, named as such; the head is an entry
        // written once and removed here, named too since the staged state
        // is computed from it.
        let state = acc.read(c).stale(c);
        let state = keys.fold(c, state, |c, s, key| {
            let queued = heads.member(c, key);
            c.assert(is_true(queued).message("Stream key not queued"));
            let head = heads.lookup(c, key).stale(c);
            heads.remove(c, key);
            let delta = P::delta(c, &head);
            let next = F::step(c, s, delta);
            staged.insert(c, key, &next);
            next
        });
        acc.write(c, &state);
    }
}
