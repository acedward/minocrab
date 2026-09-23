//! THE STREAM'S GATE (M41 A, notes/stream-design.org): both layouts placed
//! by `#[derive(Ledger)]`, both run on Midnight's on-chain VM through the
//! executor, and the contention claim checked on the transcript — a
//! primitive stream's insert, take and combine never read the accumulator;
//! a serial stream's sequence reads it exactly once.
//!
//! The two compile-fail gates (`sequence` absent on a primitive stream; a
//! bare `Fold` is not a step) are doctests on `v3::stream`.

use midnight_base_crypto::fab::{
    AlignedValue, Alignment, AlignmentAtom, AlignmentSegment, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_onchain_vm::ops::{Key as VmKey, Op};
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::{Array, HashMap as StorageHashMap};
use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{Fr, Public};
use minocrab_ledger::field_key;
use minocrab_sim::v3::exec::{self, Call, ExecError, Executed};
use minocrab_std::v3::blind::{Add, Max};
use minocrab_std::v3::{
    eq, label, ArgPath, CircuitArg, Disclose, Fold, Ledger, LedgerCell, LedgerWidth, NonEmpty,
    Serial, Stream, StreamSpec, Uint,
};

type U64 = Uint<64, Public>;

// ---- the two specs -------------------------------------------------------------------

/// A primitive stream: the sig-net outbox's shape, `(nonce, last seen)`
/// stepped by `(Add, Max)` with the body's height as the max's delta.
struct Outbox;

impl StreamSpec for Outbox {
    type Key = U64;
    type Body = U64;
    type Head = U64;
    type State = (U64, U64);
    type Step = (Add, Max);

    fn head(_c: &mut Circuit3, body: &U64) -> U64 {
        *body
    }

    fn delta(c: &mut Circuit3, head: &U64) -> (U64, U64) {
        (Uint::from_field_unchecked(c.constant(1u64)), *head)
    }
}

/// A serial stream: "the last report above a threshold, else one more" —
/// not a monoid, so it goes behind the popeq.
struct Reports;

struct AboveOrBump;

impl Fold<U64> for AboveOrBump {
    type Delta = U64;

    fn step(c: &mut Circuit3, s: U64, d: U64) -> U64 {
        let above = c.less_than(100u64, d.field(), 64);
        let bumped = c.add(s.field(), 1u64);
        Uint::from_field_unchecked(c.cond_select(above, d.field(), bumped))
    }
}

impl StreamSpec for Reports {
    type Key = U64;
    type Body = U64;
    type Head = U64;
    type State = U64;
    type Step = Serial<AboveOrBump, 2>;

    fn head(_c: &mut Circuit3, body: &U64) -> U64 {
        *body
    }

    fn delta(_c: &mut Circuit3, head: &U64) -> U64 {
        *head
    }
}

#[derive(Ledger)]
struct Block {
    outbox: Stream<Outbox>,
    reports: Stream<Reports>,
    after: LedgerCell<U64>,
}

const BLOCK: Block = Block::new();

// Field map: outbox = bodies 0, nonce 1, seen 2, nonce snapshots 3, seen
// snapshots 4; reports = bodies 5, heads 6, acc 7, staged 8; after 9.
const FIELDS: usize = 10;

label! {
    Key = "the key";
    Body = "the body";
    Keys = "the flushed keys";
    Expected = "the expected value";
}

#[test]
fn the_derive_places_both_layouts_by_width() {
    assert_eq!(<Stream<Outbox> as LedgerWidth>::WIDTH, 5);
    assert_eq!(<Stream<Reports> as LedgerWidth>::WIDTH, 4);
    assert_eq!(BLOCK.after.index(), 9);
}

// ---- state ----------------------------------------------------------------------------

fn u64_value(v: u64) -> AlignedValue {
    AlignedValue::new(
        Value(vec![ValueAtom(v.to_le_bytes().to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes { length: 8 })]),
    )
    .expect("a u64 fits")
}

fn cell(v: u64) -> StateValue<InMemoryDB> {
    StateValue::Cell(Sp::new(u64_value(v)))
}

fn map(entries: &[(u64, u64)]) -> StateValue<InMemoryDB> {
    let mut m: StorageHashMap<AlignedValue, StateValue<InMemoryDB>, InMemoryDB> = StorageHashMap::new();
    for (k, v) in entries {
        m = m.insert(u64_value(*k), cell(*v));
    }
    StateValue::Map(m)
}

/// The block's state from per-field values: maps as entry lists, cells as
/// values.
#[derive(Clone, Default)]
struct Seed {
    maps: [Vec<(u64, u64)>; FIELDS],
    cells: [u64; FIELDS],
}

const MAP_FIELDS: [usize; 6] = [0, 3, 4, 5, 6, 8];

impl Seed {
    fn state(&self) -> StateValue<InMemoryDB> {
        let fields: Vec<StateValue<InMemoryDB>> = (0..FIELDS)
            .map(|i| {
                if MAP_FIELDS.contains(&i) {
                    map(&self.maps[i])
                } else {
                    cell(self.cells[i])
                }
            })
            .collect();
        StateValue::Array(Array::from(fields))
    }
}

/// THE DEPLOY STATE (notes/ledger-header.org): the block's derived
/// `initial_state()` is this file's own hand seed at its defaults — both
/// streams' maps empty and every cell (bodies, accumulators, the trailing
/// cell) at zero — so a `Stream` contributes exactly the fields its width
/// claims, in the order its handles address them.
#[test]
fn the_derived_initial_state_is_the_default_seed() {
    assert!(Block::initial_state().build() == Seed::default().state());
}

fn field(state: &StateValue<InMemoryDB>, index: usize) -> StateValue<InMemoryDB> {
    let StateValue::Array(ref fields) = *state else {
        panic!("block array");
    };
    fields.get(index).expect("field in range").clone()
}

fn cell_of(state: &StateValue<InMemoryDB>, index: usize) -> u64 {
    let f = field(state, index);
    let StateValue::Cell(ref av) = f else {
        panic!("field {index} is a cell");
    };
    decode(av.value.0.first().map(|a| a.0.clone()).unwrap_or_default())
}

fn entry(state: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<u64> {
    let f = field(state, index);
    let StateValue::Map(ref m) = f else {
        panic!("field {index} is a map");
    };
    let e = m.get(&u64_value(key))?;
    let StateValue::Cell(ref av) = *e else {
        panic!("cells");
    };
    Some(decode(av.value.0.first().map(|a| a.0.clone()).unwrap_or_default()))
}

fn decode(bytes: Vec<u8>) -> u64 {
    let mut le = [0u8; 8];
    le[..bytes.len()].copy_from_slice(&bytes);
    u64::from_le_bytes(le)
}

fn compile(body: impl FnOnce(&mut Circuit3)) -> Compiled3 {
    let mut c = Circuit3::new();
    body(&mut c);
    c.finish(false)
}

fn run(compiled: &Compiled3, seed: &Seed, inputs: &[u64]) -> Result<Executed, ExecError> {
    let inputs: Vec<Fr> = inputs.iter().map(|&v| Fr::from(v)).collect();
    let ctx = exec::context(seed.state(), [7u8; 32]);
    exec::execute(&compiled.ir, &Call::new(&inputs, &[]), &ctx)
}

/// How many `popeq`s the transcript carries — every checked read.
fn popeqs(out: &Executed) -> usize {
    out.ops.iter().filter(|op| matches!(op, Op::Popeq { .. })).count()
}

fn two_args(c: &mut Circuit3) -> (U64, U64) {
    let k = <Uint<64> as CircuitArg>::declare(c, &ArgPath::root("k"));
    let b = <Uint<64> as CircuitArg>::declare(c, &ArgPath::root("b"));
    k.constrain(c);
    b.constrain(c);
    (k.disclose_as::<Key>(c), b.disclose_as::<Body>(c))
}

// ---- the primitive stream -----------------------------------------------------------

#[test]
fn a_primitive_stream_inserts_blind_and_takes_the_post_step_state() {
    let insert = compile(|c| {
        let (k, b) = two_args(c);
        BLOCK.outbox.insert(c, &k, &b);
    });
    let mut seed = Seed::default();
    seed.cells[1] = 6; // nonce
    seed.cells[2] = 100; // last seen
    // First insert: key 9, height 120.
    let out = run(&insert, &seed, &[9, 120]).expect("applies");
    assert_eq!(popeqs(&out), 1, "the one read is the not-member check on the key");
    assert_eq!(out.reads.len(), 1);
    assert_eq!(cell_of(&out.post, 1), 7, "nonce advanced");
    assert_eq!(cell_of(&out.post, 2), 120, "last seen raised");
    assert_eq!(entry(&out.post, 0, 9), Some(120), "the body");
    assert_eq!(entry(&out.post, 3, 9), Some(7), "the post-step nonce");
    assert_eq!(entry(&out.post, 4, 9), Some(120), "the post-step last seen");
    // A second insert with a LOWER height against the state the first left:
    // nonce advances, last seen stays.
    let mut seed2 = Seed::default();
    seed2.cells[1] = 7;
    seed2.cells[2] = 120;
    seed2.maps[0] = vec![(9, 120)];
    seed2.maps[3] = vec![(9, 7)];
    seed2.maps[4] = vec![(9, 120)];
    let out = run(&insert, &seed2, &[10, 50]).expect("applies");
    assert_eq!(cell_of(&out.post, 1), 8);
    assert_eq!(cell_of(&out.post, 2), 120);
    assert_eq!(entry(&out.post, 3, 10), Some(8));
    assert_eq!(entry(&out.post, 4, 10), Some(120));
    // The same key again is refused by the circuit.
    assert!(matches!(run(&insert, &seed2, &[9, 1]), Err(ExecError::Rejected { .. })));

    // Take: the body and the pair, and everything read is removed.
    let take = compile(|c| {
        let (k, expect_nonce) = two_args(c);
        let (body, state) = BLOCK.outbox.take(c, &k);
        let (nonce, seen) = *state;
        c.assert(eq(nonce, expect_nonce));
        c.assert(eq(body, 120u64));
        c.assert(eq(seen, 120u64));
    });
    let taken = run(&take, &seed2, &[9, 7]).expect("the stable reads apply");
    assert_eq!(popeqs(&taken), 4, "member + body + two components, all per-key");
    assert_eq!(entry(&taken.post, 0, 9), None);
    assert_eq!(entry(&taken.post, 3, 9), None);
    assert_eq!(entry(&taken.post, 4, 9), None);
    assert_eq!(cell_of(&taken.post, 1), 7, "the accumulator is untouched by take");
    assert!(matches!(run(&take, &seed2, &[11, 0]), Err(ExecError::Rejected { .. })), "absent key");

    // Combine with no element: blind max on last seen, nothing read.
    let combine = compile(|c| {
        let (_k, h) = two_args(c);
        let zero = Uint::from_field_unchecked(c.constant(0u64));
        BLOCK.outbox.combine(c, (zero, h));
    });
    let out = run(&combine, &seed2, &[0, 500]).expect("applies");
    assert_eq!(popeqs(&out), 0, "combine reads nothing");
    assert_eq!(cell_of(&out.post, 1), 7, "nonce + 0");
    assert_eq!(cell_of(&out.post, 2), 500);
}

// ---- the serial stream ---------------------------------------------------------------

#[test]
fn a_serial_stream_sequences_a_short_flush_reading_the_accumulator_once() {
    let insert = compile(|c| {
        let (k, b) = two_args(c);
        BLOCK.reports.insert(c, &k, &b);
    });
    let out = run(&insert, &Seed::default(), &[1, 150]).expect("applies");
    assert_eq!(popeqs(&out), 1, "insert: the not-member check only");
    assert_eq!(entry(&out.post, 5, 1), Some(150), "body");
    assert_eq!(entry(&out.post, 6, 1), Some(150), "head");
    assert_eq!(cell_of(&out.post, 7), 0, "acc untouched");

    // Three queued reports; flush one, two, three of them.
    let mut seed = Seed::default();
    seed.cells[7] = 10; // acc
    seed.maps[5] = vec![(1, 150), (2, 30), (3, 200)];
    seed.maps[6] = seed.maps[5].clone();
    let sequence = compile(|c| {
        let keys = <NonEmpty<Uint<64>, 2> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        BLOCK.reports.sequence(c, keys);
    });
    // Native twin of the fold over the live prefix.
    let native = |s: u64, d: u64| if d > 100 { d } else { s + 1 };
    for (inputs, order) in [
        (vec![2, 0, 0, 0], vec![2]),
        (vec![2, 1, 1, 0], vec![2, 1]),
        (vec![3, 2, 1, 2], vec![3, 1, 2]),
    ] {
        let out = run(&sequence, &seed, &inputs).expect("applies");
        let acc_reads = out
            .ops
            .iter()
            .filter(|op| matches!(op, Op::Idx { push_path: false, path, .. } if path.len() == 1 && path.iter().next().is_some_and(|k| *k == VmKey::Value(field_key(7)))))
            .count();
        assert_eq!(acc_reads, 1, "{order:?}: the accumulator is read exactly once");
        assert_eq!(popeqs(&out), 1 + 2 * order.len(), "{order:?}: acc + (member, head) per live key");
        let mut s = 10u64;
        for k in &order {
            let d = seed.maps[6].iter().find(|(kk, _)| kk == k).expect("queued").1;
            s = native(s, d);
            assert_eq!(entry(&out.post, 8, *k), Some(s), "{order:?}: staged[{k}] is the post-step state");
            assert_eq!(entry(&out.post, 6, *k), None, "{order:?}: head removed");
        }
        assert_eq!(cell_of(&out.post, 7), s, "{order:?}: acc written once with the final state");
        // Unflushed heads stay.
        for (k, _) in &seed.maps[6] {
            if !order.contains(k) {
                assert_eq!(entry(&out.post, 6, *k), Some(seed.maps[6].iter().find(|(kk, _)| kk == k).unwrap().1));
            }
        }
    }
    // A key that is not queued is the circuit's rejection (under the guard,
    // so a dead slot's garbage key is not).
    assert!(matches!(run(&sequence, &seed, &[9, 0, 0, 0]), Err(ExecError::Rejected { .. })));
    run(&sequence, &seed, &[1, 0, 9, 9]).expect("dead slots are not checked");

    // Take after a flush: the body and the staged state.
    let mut flushed = seed.clone();
    flushed.maps[6] = vec![(2, 30), (3, 200)];
    flushed.maps[8] = vec![(1, 150)];
    flushed.cells[7] = 150;
    let take = compile(|c| {
        let (k, expected) = two_args(c);
        let (body, state) = BLOCK.reports.take(c, &k);
        c.assert(eq(state, expected));
        c.assert(eq(body, 150u64));
    });
    let out = run(&take, &flushed, &[1, 150]).expect("applies");
    assert_eq!(popeqs(&out), 3, "member + staged + body");
    assert_eq!(entry(&out.post, 8, 1), None);
    assert_eq!(entry(&out.post, 5, 1), None);
    // Not yet sequenced: refused.
    assert!(matches!(run(&take, &flushed, &[2, 0]), Err(ExecError::Rejected { .. })));

    // Combine on a serial stream: read, step, write — one popeq on acc.
    let combine = compile(|c| {
        let (_k, d) = two_args(c);
        BLOCK.reports.combine(c, d);
    });
    let out = run(&combine, &flushed, &[0, 7]).expect("applies");
    assert_eq!(popeqs(&out), 1, "the contended read");
    assert_eq!(cell_of(&out.post, 7), 151, "150 bumped");
    let out = run(&combine, &flushed, &[0, 700]).expect("applies");
    assert_eq!(cell_of(&out.post, 7), 700);
}
