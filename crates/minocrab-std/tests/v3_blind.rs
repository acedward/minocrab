//! THE BLIND OPS' GATE (M40 A/B, notes/stream-design.org).
//!
//! Nothing in `v3::blind` is expressible in Compact, so there is no compactc
//! artifact to differ against. The gate is Midnight's own on-chain VM: every
//! transcript below is compiled, run by the executor
//! (`minocrab_sim::v3::exec`, `ResultModeGather` then `ResultModeVerify`)
//! against a SEEDED state, and the resulting cells and map entries are read
//! back and compared with the value the op is defined to leave. The failure
//! paths — an overflowing add, a take on an absent key — are checked to be
//! refused by the VM, not by the circuit.
//!
//! Two invariants ride along:
//!
//! 1. NO PUBLIC INPUT. Each blind op mints zero `public_input` gates and
//!    performs zero reads (`Executed::reads` is empty, `consumed_public` is
//!    zero), which is the whole point: with no `popeq` there is nothing a
//!    landed transaction can make stale.
//! 2. NO HIDDEN OPS. The typed spellings (`LedgerCell::snapshot_into`,
//!    `LedgerCell::combine_blind`, the `Primitive` tuple impls) lower to the
//!    byte-identical ZKIR of the explicit `minocrab_ledger` op lists.
//!
//! The cost table at the bottom (`costs`) prints `(k, rows, Impact ops)` per
//! op for the note.

use midnight_base_crypto::fab::{
    AlignedValue, Alignment, AlignmentAtom, AlignmentSegment, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::{Array, HashMap as StorageHashMap};
use minocrab::v3::{Circuit3, Compiled3, FieldT};
use minocrab::{Fr, Public};
use minocrab_ledger::{
    cell_add_at, cell_and_at, cell_max_at, cell_min_at, cell_or_at, cell_snapshot_into_map_at,
    cell_write_first_at, emit, ImpactElem, LedgerKey, LedgerValue,
};
use minocrab_sim::v3::cost;
use minocrab_sim::v3::exec::{self, Call, ExecError, Executed};
use minocrab_std::v3::blind::{Add, And, First, FirstAcc, Last, Max, Min, Or};
use minocrab_std::v3::{
    eq, Bool, Ledger, LedgerCell, LedgerMap, LedgerRepr, Monoid, Primitive, Uint,
};
use minocrab_zkir::v3::to_zkir_string;

type U64 = Uint<64, Public>;

/// The block under test: an accumulator cell and its snapshot map for a
/// `Uint<64>`, the same for a `Boolean`, and `First`'s two cells.
#[derive(Ledger)]
struct Block {
    n: LedgerCell<U64>,
    n_snap: LedgerMap<U64, U64>,
    b: LedgerCell<Bool<Public>>,
    b_snap: LedgerMap<U64, Bool<Public>>,
    first: LedgerCell<U64>,
    written: LedgerCell<Bool<Public>>,
}

const BLOCK: Block = Block::new();
const FIELDS: usize = 6;

// ---- the seeded state -----------------------------------------------------------

fn bytes_value(n: u32, bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        Value(vec![ValueAtom(bytes.to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes { length: n })]),
    )
    .expect("the bytes fit the atom")
}

fn u64_value(v: u64) -> AlignedValue {
    bytes_value(8, &v.to_le_bytes())
}

fn bool_value(v: bool) -> AlignedValue {
    bytes_value(1, &[u8::from(v)])
}

fn cell(av: AlignedValue) -> StateValue<InMemoryDB> {
    StateValue::Cell(Sp::new(av))
}

fn map_of(entries: &[(u64, AlignedValue)]) -> StateValue<InMemoryDB> {
    let mut m: StorageHashMap<AlignedValue, StateValue<InMemoryDB>, InMemoryDB> =
        StorageHashMap::new();
    for (k, v) in entries {
        m = m.insert(u64_value(*k), cell(v.clone()));
    }
    StateValue::Map(m)
}

#[derive(Clone, Default)]
struct Seed {
    n: u64,
    n_snap: Vec<(u64, u64)>,
    b: bool,
    b_snap: Vec<(u64, bool)>,
    first: u64,
    written: bool,
}

impl Seed {
    fn state(&self) -> StateValue<InMemoryDB> {
        let fields = vec![
            cell(u64_value(self.n)),
            map_of(&self.n_snap.iter().map(|(k, v)| (*k, u64_value(*v))).collect::<Vec<_>>()),
            cell(bool_value(self.b)),
            map_of(&self.b_snap.iter().map(|(k, v)| (*k, bool_value(*v))).collect::<Vec<_>>()),
            cell(u64_value(self.first)),
            cell(bool_value(self.written)),
        ];
        assert_eq!(fields.len(), FIELDS);
        StateValue::Array(Array::from(fields))
    }
}

fn field(state: &StateValue<InMemoryDB>, index: usize) -> StateValue<InMemoryDB> {
    let StateValue::Array(fields) = state else {
        panic!("the state is the block's array");
    };
    fields.get(index).expect("field in range").clone()
}

fn cell_bytes(state: &StateValue<InMemoryDB>, index: usize) -> Vec<u8> {
    let f = field(state, index);
    let StateValue::Cell(ref av) = f else {
        panic!("field {index} is a cell");
    };
    av.value.0.first().map(|a| a.0.clone()).unwrap_or_default()
}

fn cell_u64(state: &StateValue<InMemoryDB>, index: usize) -> u64 {
    let bytes = cell_bytes(state, index);
    let mut le = [0u8; 8];
    le[..bytes.len()].copy_from_slice(&bytes);
    u64::from_le_bytes(le)
}

fn cell_bool(state: &StateValue<InMemoryDB>, index: usize) -> bool {
    !cell_bytes(state, index).is_empty()
}

fn map_entry(state: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<Vec<u8>> {
    let f = field(state, index);
    let StateValue::Map(ref m) = f else {
        panic!("field {index} is a map");
    };
    let entry = m.get(&u64_value(key))?;
    let StateValue::Cell(ref av) = *entry else {
        panic!("map entries are cells");
    };
    Some(av.value.0.first().map(|a| a.0.clone()).unwrap_or_default())
}

fn map_u64(state: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<u64> {
    map_entry(state, index, key).map(|bytes| {
        let mut le = [0u8; 8];
        le[..bytes.len()].copy_from_slice(&bytes);
        u64::from_le_bytes(le)
    })
}

fn map_bool(state: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<bool> {
    map_entry(state, index, key).map(|bytes| !bytes.is_empty())
}

// ---- the circuits -----------------------------------------------------------------

/// Two public `Uint<64>` arguments, `k` then `d`.
fn two_args(c: &mut Circuit3) -> (U64, U64) {
    let k = c.arg::<FieldT>("k");
    let d = c.arg::<FieldT>("d");
    let k = Uint::from_field_unchecked(c.disclose(k, "k"));
    let d = Uint::from_field_unchecked(c.disclose(d, "d"));
    (k, d)
}

fn compile(body: impl FnOnce(&mut Circuit3)) -> Compiled3 {
    let mut c = Circuit3::new();
    body(&mut c);
    c.finish(false)
}

fn run(compiled: &Compiled3, seed: &Seed, inputs: &[u64]) -> Result<Executed, ExecError> {
    let inputs: Vec<Fr> = inputs.iter().map(|&v| Fr::from(v)).collect();
    let ctx = exec::context(seed.state(), [7u8; 32]);
    let call = Call::new(&inputs, &[]);
    exec::execute(&compiled.ir, &call, &ctx)
}

/// The gate's first invariant: the transcript READ nothing.
fn assert_blind(executed: &Executed) {
    assert!(executed.reads.is_empty(), "a blind op performs no read: {:?}", executed.reads);
    assert_eq!(executed.run.consumed_public, 0, "a blind op consumes no public transcript output");
    assert!(
        executed.preimage.public_transcript_outputs.is_empty(),
        "a blind op has no public transcript outputs"
    );
}

// ---- snapshot ---------------------------------------------------------------------

#[test]
fn snapshot_copies_the_cell_into_the_map_entry_without_reading_it() {
    let circuit = compile(|c| {
        let (k, _d) = two_args(c);
        BLOCK.n.snapshot_into(c, &BLOCK.n_snap, &k);
    });
    let seed = Seed { n: 4242, ..Seed::default() };
    let out = run(&circuit, &seed, &[9, 0]).expect("the snapshot applies");
    assert_blind(&out);
    assert_eq!(map_u64(&out.post, 1, 9), Some(4242), "n_snap[9] = n");
    assert_eq!(cell_u64(&out.post, 0), 4242, "the cell is untouched");
    // Overwrites an existing entry, as `Map.insert` does.
    let seed = Seed { n: 1, n_snap: vec![(9, 77)], ..Seed::default() };
    let out = run(&circuit, &seed, &[9, 0]).expect("applies over an existing entry");
    assert_eq!(map_u64(&out.post, 1, 9), Some(1));
}

#[test]
fn snapshot_of_a_boolean_cell() {
    let circuit = compile(|c| {
        let (k, _d) = two_args(c);
        BLOCK.b.snapshot_into(c, &BLOCK.b_snap, &k);
    });
    let seed = Seed { b: true, ..Seed::default() };
    let out = run(&circuit, &seed, &[3, 0]).expect("applies");
    assert_blind(&out);
    assert_eq!(map_bool(&out.post, 3, 3), Some(true));
}

// ---- the combines ----------------------------------------------------------------

#[test]
fn add_combines_blind_and_overflow_fails_the_transaction() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        BLOCK.n.combine_blind(c, Add, &d);
    });
    let seed = Seed { n: 40, ..Seed::default() };
    let out = run(&circuit, &seed, &[0, 2]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 0), 42);
    // The ledger's checked add: the circuit is satisfied, the state has no room.
    let seed = Seed { n: u64::MAX, ..Seed::default() };
    match run(&circuit, &seed, &[0, 1]) {
        Err(ExecError::NotApplied { .. }) => {}
        other => panic!("an overflowing add is refused by the ledger, got {other:?}"),
    }
}

#[test]
fn max_keeps_the_larger_on_both_arms() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        BLOCK.n.combine_blind(c, Max, &d);
    });
    // Δ wins.
    let out = run(&circuit, &Seed { n: 10, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 0), 25);
    // The cell wins — the arm the milestone's `branch 2` sketch got wrong.
    let out = run(&circuit, &Seed { n: 30, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_eq!(cell_u64(&out.post, 0), 30);
    // Equal: either arm leaves the same value.
    let out = run(&circuit, &Seed { n: 25, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_eq!(cell_u64(&out.post, 0), 25);
    // From the identity.
    let out = run(&circuit, &Seed::default(), &[0, 1]).expect("applies");
    assert_eq!(cell_u64(&out.post, 0), 1);
}

#[test]
fn min_keeps_the_smaller_on_both_arms() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        BLOCK.n.combine_blind(c, Min, &d);
    });
    let out = run(&circuit, &Seed { n: 10, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 0), 10);
    let out = run(&circuit, &Seed { n: 30, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_eq!(cell_u64(&out.post, 0), 25);
    let out = run(&circuit, &Seed { n: 25, ..Seed::default() }, &[0, 25]).expect("applies");
    assert_eq!(cell_u64(&out.post, 0), 25);
}

#[test]
fn and_or_combine_blind() {
    let and = compile(|c| {
        let (_k, d) = two_args(c);
        let d = Bool::from_field_unchecked(d.field());
        BLOCK.b.combine_blind(c, And, &d);
    });
    let or = compile(|c| {
        let (_k, d) = two_args(c);
        let d = Bool::from_field_unchecked(d.field());
        BLOCK.b.combine_blind(c, Or, &d);
    });
    for (a, d) in [(false, false), (false, true), (true, false), (true, true)] {
        let seed = Seed { b: a, ..Seed::default() };
        let out = run(&and, &seed, &[0, u64::from(d)]).expect("and applies");
        assert_blind(&out);
        assert_eq!(cell_bool(&out.post, 2), a && d, "and {a} {d}");
        let out = run(&or, &seed, &[0, u64::from(d)]).expect("or applies");
        assert_blind(&out);
        assert_eq!(cell_bool(&out.post, 2), a || d, "or {a} {d}");
    }
}

#[test]
fn last_overwrites_and_first_writes_once() {
    let last = compile(|c| {
        let (_k, d) = two_args(c);
        BLOCK.n.combine_blind(c, Last, &d);
    });
    let out = run(&last, &Seed { n: 5, ..Seed::default() }, &[0, 9]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 0), 9);

    let first = compile(|c| {
        let (_k, d) = two_args(c);
        let acc = FirstAcc {
            value: BLOCK.first,
            written: BLOCK.written,
        };
        <First as Primitive<U64>>::combine_blind(c, &acc, &d);
    });
    // Nothing written yet: the value lands and the flag is set.
    let out = run(&first, &Seed::default(), &[0, 9]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 4), 9);
    assert!(cell_bool(&out.post, 5));
    // Already written: both writes are skipped.
    let seed = Seed { first: 3, written: true, ..Seed::default() };
    let out = run(&first, &seed, &[0, 9]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 4), 3);
    assert!(cell_bool(&out.post, 5));
}

// ---- reading the snapshot back --------------------------------------------------

#[test]
fn take_reads_the_snapshot_and_removes_it_and_an_absent_key_is_refused() {
    // `take` then assert the value against the second argument: the executor
    // rejects the call if the read gave anything else.
    let circuit = compile(|c| {
        let (k, d) = two_args(c);
        let got = <Add as Primitive<U64>>::take(c, &BLOCK.n_snap, &k);
        c.assert(eq(got, d));
    });
    let seed = Seed { n_snap: vec![(9, 4242), (10, 1)], ..Seed::default() };
    let out = run(&circuit, &seed, &[9, 4242]).expect("the stable read applies");
    assert_eq!(out.reads.len(), 1, "one read: the snapshot entry");
    assert_eq!(map_u64(&out.post, 1, 9), None, "taken");
    assert_eq!(map_u64(&out.post, 1, 10), Some(1), "the other entry stays");
    // A wrong expectation is the circuit's rejection…
    assert!(matches!(run(&circuit, &seed, &[9, 1]), Err(ExecError::Rejected { .. })));
    // …and an absent key is the VM's.
    assert!(run(&circuit, &seed, &[11, 0]).is_err(), "an absent key does not apply");
}

// ---- tuples (M40 B) -------------------------------------------------------------

/// `(Add, Max)` over `(nonce, last_seen)` — the sig-net outbox's state — laid
/// out by the tuple impl: two cells then two maps.
type Pair = (Add, Max);
type PairState = (U64, U64);

struct PairBlock {
    acc: <Pair as Primitive<PairState>>::Acc,
    snap: <Pair as Primitive<PairState>>::Snapshot<U64>,
}

const PAIR_FIELDS: usize = 4;

fn pair_block() -> PairBlock {
    PairBlock {
        acc: <Pair as Primitive<PairState>>::acc_at_block(PAIR_FIELDS, 0),
        snap: <Pair as Primitive<PairState>>::snapshot_at_block::<U64>(PAIR_FIELDS, 2),
    }
}

fn pair_state(nonce: u64, seen: u64, snaps: &[(u64, u64, u64)]) -> StateValue<InMemoryDB> {
    StateValue::Array(Array::from(vec![
        cell(u64_value(nonce)),
        cell(u64_value(seen)),
        map_of(&snaps.iter().map(|(k, n, _)| (*k, u64_value(*n))).collect::<Vec<_>>()),
        map_of(&snaps.iter().map(|(k, _, s)| (*k, u64_value(*s))).collect::<Vec<_>>()),
    ]))
}

fn run_pair(compiled: &Compiled3, state: StateValue<InMemoryDB>, inputs: &[u64]) -> Result<Executed, ExecError> {
    let inputs: Vec<Fr> = inputs.iter().map(|&v| Fr::from(v)).collect();
    let ctx = exec::context(state, [7u8; 32]);
    exec::execute(&compiled.ir, &Call::new(&inputs, &[]), &ctx)
}

#[test]
fn the_tuple_lays_out_one_cell_and_one_map_per_component() {
    assert_eq!(<Pair as Primitive<PairState>>::ACC_FIELDS, 2);
    assert_eq!(<Pair as Primitive<PairState>>::SNAPSHOT_FIELDS, 2);
    assert_eq!(<(Add, Max, First) as Primitive<(U64, U64, U64)>>::ACC_FIELDS, 4);
    assert_eq!(<(Add, Max, First) as Primitive<(U64, U64, U64)>>::SNAPSHOT_FIELDS, 3);
    let block = pair_block();
    assert_eq!(block.acc.0.index(), 0);
    assert_eq!(block.acc.1.index(), 1);
    assert_eq!(block.snap.0.index(), 2);
    assert_eq!(block.snap.1.index(), 3);
}

#[test]
fn the_pair_round_trips_through_the_ledger() {
    let block = pair_block();
    // The outbox's insert: combine (1, 0) blind, then snapshot — so the
    // stored state is the post-step value (the DECIDED convention).
    let insert = compile(|c| {
        let (k, h) = two_args(c);
        let one = Uint::from_field_unchecked(c.constant(1u64));
        <Pair as Primitive<PairState>>::combine_blind(c, &block.acc, &(one, h));
        <Pair as Primitive<PairState>>::snapshot(c, &block.acc, &block.snap, &k);
    });
    let out = run_pair(&insert, pair_state(6, 100, &[]), &[9, 120]).expect("applies");
    assert_blind(&out);
    assert_eq!(cell_u64(&out.post, 0), 7, "nonce advanced");
    assert_eq!(cell_u64(&out.post, 1), 120, "last seen raised");
    assert_eq!(map_u64(&out.post, 2, 9), Some(7), "snapshot holds the post-step nonce");
    assert_eq!(map_u64(&out.post, 3, 9), Some(120), "and the post-step last seen");

    // Take, and the two components come back together.
    let take = compile(|c| {
        let (k, expect_nonce) = two_args(c);
        let (nonce, seen) = <Pair as Primitive<PairState>>::take(c, &block.snap, &k);
        c.assert(eq(nonce, expect_nonce));
        c.assert(eq(seen, 120u64));
    });
    let taken = run_pair(&take, out.post, &[9, 7]).expect("the stable reads apply");
    assert_eq!(taken.reads.len(), 2, "one read per component");
    assert_eq!(map_u64(&taken.post, 2, 9), None);
    assert_eq!(map_u64(&taken.post, 3, 9), None);
}

#[test]
fn the_tuple_monoid_is_componentwise() {
    let circuit = compile(|c| {
        let (a, b) = two_args(c);
        let id = <Pair as Monoid<PairState>>::identity(c);
        let x = <Pair as Monoid<PairState>>::combine(c, id, (a, b));
        let y = <Pair as Monoid<PairState>>::combine(c, x, (a, b));
        // (a + a, max(b, b)) == (2a, b)
        let twice = Uint::<64, Public>::from_field_unchecked(c.add(a.field(), a.field()));
        c.assert(eq(y.0, twice));
        c.assert(eq(y.1, b));
    });
    run_pair(&circuit, pair_state(0, 0, &[]), &[21, 5]).expect("the identity and combine agree");
}

// ---- no hidden ops -----------------------------------------------------------------

fn zkir(compiled: Compiled3) -> String {
    to_zkir_string(&compiled.ir).expect("IR serializes")
}

fn u64_ledger(v: U64) -> LedgerValue {
    LedgerValue::new(U64::atoms(), vec![ImpactElem::Wire(v.field())])
}

#[test]
fn the_typed_spellings_are_the_explicit_ops() {
    let typed = compile(|c| {
        let (k, d) = two_args(c);
        BLOCK.n.snapshot_into(c, &BLOCK.n_snap, &k);
        BLOCK.n.combine_blind(c, Add, &d);
        BLOCK.n.combine_blind(c, Max, &d);
        BLOCK.n.combine_blind(c, Min, &d);
        let b = Bool::from_field_unchecked(d.field());
        BLOCK.b.combine_blind(c, And, &b);
        BLOCK.b.combine_blind(c, Or, &b);
        BLOCK.n.combine_blind(c, Last, &d);
        let acc = FirstAcc { value: BLOCK.first, written: BLOCK.written };
        <First as Primitive<U64>>::combine_blind(c, &acc, &d);
    });
    let explicit = compile(|c| {
        let (k, d) = two_args(c);
        let k = u64_ledger(k);
        let d = u64_ledger(d);
        let n = [LedgerKey::Field(0)];
        let n_snap = [LedgerKey::Field(1)];
        let b = [LedgerKey::Field(2)];
        emit(c, &cell_snapshot_into_map_at(&n, &n_snap, &k));
        emit(c, &cell_add_at(&n, &d));
        emit(c, &cell_max_at(&n, &d));
        emit(c, &cell_min_at(&n, &d));
        let bd = LedgerValue::new(Bool::<Public>::atoms(), d.elems().to_vec());
        emit(c, &cell_and_at(&b, &bd));
        emit(c, &cell_or_at(&b, &bd));
        emit(c, &minocrab_ledger::cell_write_at(&n, &d));
        emit(c, &cell_write_first_at(&[LedgerKey::Field(4)], &[LedgerKey::Field(5)], &d));
    });
    assert_eq!(zkir(typed), zkir(explicit));
}

// ---- costs -----------------------------------------------------------------------------

/// `(k, rows, Impact ops)` per blind op, for notes/stream-design.org.
#[test]
fn costs() {
    let table: Vec<(&str, Compiled3)> = vec![
        ("snapshot", compile(|c| { let (k, _) = two_args(c); BLOCK.n.snapshot_into(c, &BLOCK.n_snap, &k); })),
        ("add", compile(|c| { let (_, d) = two_args(c); BLOCK.n.combine_blind(c, Add, &d); })),
        ("max", compile(|c| { let (_, d) = two_args(c); BLOCK.n.combine_blind(c, Max, &d); })),
        ("min", compile(|c| { let (_, d) = two_args(c); BLOCK.n.combine_blind(c, Min, &d); })),
        ("and", compile(|c| { let (_, d) = two_args(c); let d = Bool::from_field_unchecked(d.field()); BLOCK.b.combine_blind(c, And, &d); })),
        ("or", compile(|c| { let (_, d) = two_args(c); let d = Bool::from_field_unchecked(d.field()); BLOCK.b.combine_blind(c, Or, &d); })),
        ("last", compile(|c| { let (_, d) = two_args(c); BLOCK.n.combine_blind(c, Last, &d); })),
        ("first", compile(|c| { let (_, d) = two_args(c); let acc = FirstAcc { value: BLOCK.first, written: BLOCK.written }; <First as Primitive<U64>>::combine_blind(c, &acc, &d); })),
        ("(Add, Max) insert", compile(|c| {
            let block = pair_block();
            let (k, h) = two_args(c);
            let one = Uint::from_field_unchecked(c.constant(1u64));
            <Pair as Primitive<PairState>>::combine_blind(c, &block.acc, &(one, h));
            <Pair as Primitive<PairState>>::snapshot(c, &block.acc, &block.snap, &k);
        })),
        ("(Add, Max) take", compile(|c| {
            let block = pair_block();
            let (k, _) = two_args(c);
            let _ = <Pair as Primitive<PairState>>::take(c, &block.snap, &k);
        })),
    ];
    println!("| op | k | rows | Impact ops |");
    println!("|---|---|---|---|");
    for (name, compiled) in &table {
        let (k, rows) = cost(&compiled.ir);
        let seed = if name.starts_with("(Add") {
            None
        } else {
            Some(Seed { n_snap: vec![(9, 1)], ..Seed::default() })
        };
        let ops = match seed {
            Some(seed) => run(compiled, &seed, &[9, 1]).expect("applies").ops.len(),
            None => run_pair(compiled, pair_state(1, 1, &[(9, 1, 1)]), &[9, 1]).expect("applies").ops.len(),
        };
        println!("| {name} | {k} | {rows} | {ops} |");
    }
}
