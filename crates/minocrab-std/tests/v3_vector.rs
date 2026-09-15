//! BOUNDED AND NON-EMPTY VECTORS' GATE (M40 C, notes/stream-design.org).
//!
//! 1. A fold with ledger ops over a short vector emits the LIVE slots' ops
//!    only: the transcript the executor produces has one insert per live
//!    key and the post-state has exactly those entries.
//! 2. The step is applied only on live slots: the circuit's fold equals a
//!    native fold over the live prefix, across every length.
//! 3. The length is range-checked against `MAX`: a length past it is the
//!    circuit's rejection (the argument constraint), before any ledger op.
//! 4. `NonEmpty`'s head always runs: a tail of length zero still folds once.
//!    The all-empty case has no spelling (`NonEmpty::split` refuses it on
//!    the witness side; there is no circuit-side constructor without a
//!    head).

use midnight_base_crypto::fab::{
    AlignedValue, Alignment, AlignmentAtom, AlignmentSegment, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::{Array, HashMap as StorageHashMap};
use minocrab::v3::{Circuit3, Compiled3, FieldT, Prim};
use minocrab::{Fr, Private, Public};
use minocrab_sim::v3::exec::{self, Call, ExecError, Executed};
use minocrab_std::v3::{
    eq, label, ArgPath, Bounded, CircuitAbi, CircuitArg, Disclose, Ledger, LedgerCell,
    LedgerMap, NonEmpty, Uint,
};

type U64 = Uint<64, Public>;

#[derive(Ledger)]
struct Block {
    seen: LedgerMap<U64, U64>,
    total: LedgerCell<U64>,
}

const BLOCK: Block = Block::new();

label! {
    Keys = "the keys";
    Expected = "the expected fold";
}

// ---- state --------------------------------------------------------------------------

fn u64_value(v: u64) -> AlignedValue {
    AlignedValue::new(
        Value(vec![ValueAtom(v.to_le_bytes().to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes { length: 8 })]),
    )
    .expect("a u64 fits")
}

fn empty_state() -> StateValue<InMemoryDB> {
    let m: StorageHashMap<AlignedValue, StateValue<InMemoryDB>, InMemoryDB> = StorageHashMap::new();
    StateValue::Array(Array::from(vec![
        StateValue::Map(m),
        StateValue::Cell(Sp::new(u64_value(0))),
    ]))
}

fn map_keys(state: &StateValue<InMemoryDB>) -> Vec<u64> {
    let StateValue::Array(ref fields) = *state else {
        panic!("block array");
    };
    let f = fields.get(0).expect("field 0").clone();
    let StateValue::Map(ref m) = f else {
        panic!("field 0 is the map");
    };
    let mut keys: Vec<u64> = m
        .iter()
        .map(|entry| {
            let bytes = &entry.0.value.0[0].0;
            let mut le = [0u8; 8];
            le[..bytes.len()].copy_from_slice(bytes);
            u64::from_le_bytes(le)
        })
        .collect();
    keys.sort_unstable();
    keys
}

fn map_value(state: &StateValue<InMemoryDB>, key: u64) -> Option<u64> {
    let StateValue::Array(ref fields) = *state else {
        panic!("block array");
    };
    let f = fields.get(0).expect("field 0").clone();
    let StateValue::Map(ref m) = f else {
        panic!("field 0 is the map");
    };
    let entry = m.get(&u64_value(key))?;
    let StateValue::Cell(ref av) = *entry else {
        panic!("cells");
    };
    let bytes = av.value.0.first().map(|a| a.0.clone()).unwrap_or_default();
    let mut le = [0u8; 8];
    le[..bytes.len()].copy_from_slice(&bytes);
    Some(u64::from_le_bytes(le))
}

fn run(compiled: &Compiled3, inputs: &[u64]) -> Result<Executed, ExecError> {
    let inputs: Vec<Fr> = inputs.iter().map(|&v| Fr::from(v)).collect();
    let ctx = exec::context(empty_state(), [7u8; 32]);
    exec::execute(&compiled.ir, &Call::new(&inputs, &[]), &ctx)
}

fn compile(body: impl FnOnce(&mut Circuit3)) -> Compiled3 {
    let mut c = Circuit3::new();
    body(&mut c);
    c.finish(false)
}

// ---- the ABI ------------------------------------------------------------------------

#[test]
fn the_length_is_one_limb_typed_as_uint_0_to_max_plus_one() {
    assert_eq!(<Bounded<Uint<64>, 4> as CircuitAbi>::SLOTS, 5);
    assert_eq!(<NonEmpty<Uint<64>, 3> as CircuitAbi>::SLOTS, 5);
    let prims = <Bounded<Uint<64>, 4> as CircuitAbi>::prims();
    assert_eq!(prims[0], Prim::UintMax { maxval: 4 }, "0..=4: less_than 5 + assert");
    assert_eq!(prims.len(), 5);
    let prims = <Bounded<Uint<64>, 255> as CircuitAbi>::prims();
    assert_eq!(prims[0], Prim::Uint { bits: 8 }, "0..=255: a bit constraint");
    let prims = <Bounded<Uint<64>, 1> as CircuitAbi>::prims();
    assert_eq!(prims[0], Prim::Uint { bits: 1 }, "0..=1: boolean");
    let atoms = <NonEmpty<Uint<64>, 2> as CircuitAbi>::atoms();
    assert_eq!(atoms.len(), 4, "head, len, two slots");
    assert_eq!(atoms[1], AlignmentAtom::Bytes { length: 1 });
}

// ---- the fold with ledger ops --------------------------------------------------------

/// `keys: NonEmpty<Uint<64>, 3>`, disclosed; each live key is inserted with
/// its running index and the count is written to the cell.
fn insert_each() -> Compiled3 {
    compile(|c| {
        let keys = <NonEmpty<Uint<64>, 3> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        let zero = Uint::<64, Public>::from_field_unchecked(c.constant(0u64));
        let count = keys.fold(c, zero, |c, n, k| {
            BLOCK.seen.insert(c, k, &n);
            Uint::from_field_unchecked(c.add(n.field(), 1u64))
        });
        BLOCK.total.write(c, &count);
    })
}

#[test]
fn a_fold_emits_the_live_slots_ops_only() {
    let circuit = insert_each();
    // inputs: head, tail len, tail slots 0..3
    for len in 0..=3u64 {
        let out = run(&circuit, &[100, len, 101, 102, 103]).expect("applies");
        let live: Vec<u64> = (0..=len).map(|i| 100 + i).collect();
        assert_eq!(map_keys(&out.post), live, "len {len}: exactly the live keys");
        for (i, k) in live.iter().enumerate() {
            assert_eq!(map_value(&out.post, *k), Some(i as u64), "the running index");
        }
        // Transcript: one 5-op insert per live key, plus the 3-op cell write.
        assert_eq!(out.ops.len(), 5 * (len as usize + 1) + 3, "len {len}");
        assert_eq!(map_value(&out.post, 0), None);
    }
}

#[test]
fn a_length_past_max_is_rejected_by_the_argument_constraint() {
    let circuit = insert_each();
    // REST = 3: the length's type is `Uint<0..4>`, a 2-bit constraint, which
    // the walk refuses as a failed `constrain_bits` (a non-power-of-two
    // bound would be a `less_than` + `assert`, an `ExecError::Rejected`).
    match run(&circuit, &[100, 4, 101, 102, 103]) {
        Err(ExecError::Circuit(e)) => assert!(e.to_string().contains("constrain_bits"), "{e}"),
        other => panic!("tail len 4 on REST = 3 must be refused by the constraint, got {other:?}"),
    }
    // REST = 4 takes the other constraint shape: `less_than 5` + `assert`.
    let circuit = compile(|c| {
        let keys = <Bounded<Uint<64>, 4> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        keys.for_each(c, |c, k| BLOCK.seen.insert(c, k, k));
    });
    match run(&circuit, &[5, 1, 2, 3, 4]) {
        Err(ExecError::Rejected { .. }) => {}
        other => panic!("len 5 on MAX = 4 must be rejected, got {other:?}"),
    }
}

#[test]
fn a_bounded_of_length_zero_folds_nothing() {
    let circuit = compile(|c| {
        let keys = <Bounded<Uint<64>, 4> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        keys.for_each(c, |c, k| BLOCK.seen.insert(c, k, k));
    });
    // inputs: len, four slots
    let out = run(&circuit, &[0, 1, 2, 3, 4]).expect("applies");
    assert!(map_keys(&out.post).is_empty());
    assert_eq!(out.ops.len(), 0, "no live slot, no op");
    let out = run(&circuit, &[4, 1, 2, 3, 4]).expect("applies");
    assert_eq!(map_keys(&out.post), vec![1, 2, 3, 4]);
    assert_eq!(out.ops.len(), 20);
}

// ---- the differential against a native fold ------------------------------------------

#[test]
fn the_fold_applies_the_step_on_live_slots_only() {
    // max over the live prefix, then (sum, max) as a pair state.
    let circuit = compile(|c| {
        let keys = <Bounded<Uint<64>, 4> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        let expected_sum = <Uint<64, Private> as CircuitArg>::declare(c, &ArgPath::root("sum"));
        let expected_max = <Uint<64, Private> as CircuitArg>::declare(c, &ArgPath::root("max"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        let expected_sum = expected_sum.disclose_as::<Expected>(c);
        let expected_max = expected_max.disclose_as::<Expected>(c);
        let zero = Uint::<64, Public>::from_field_unchecked(c.constant(0u64));
        let (sum, max) = keys.fold(c, (zero, zero), |c, (s, m), k| {
            let s = Uint::from_field_unchecked(c.add(s.field(), k.field()));
            let below = c.less_than(m.field(), k.field(), 64);
            let m = Uint::from_field_unchecked(c.cond_select(below, k.field(), m.field()));
            (s, m)
        });
        c.assert(eq(sum, expected_sum));
        c.assert(eq(max, expected_max));
    });
    // Dead slots carry LARGE values, so applying a dead step would show.
    let slots = [5u64, 9, 2, 7];
    for len in 0..=4usize {
        let live = &slots[..len];
        let sum: u64 = live.iter().sum();
        let max: u64 = live.iter().copied().max().unwrap_or(0);
        let mut inputs = vec![len as u64];
        inputs.extend_from_slice(&slots);
        inputs.push(sum);
        inputs.push(max);
        run(&circuit, &inputs).unwrap_or_else(|e| panic!("len {len}: {e}"));
        // And the wrong expectation is rejected, so the equality is real.
        let mut wrong = inputs.clone();
        wrong[5] += 1;
        assert!(matches!(run(&circuit, &wrong), Err(ExecError::Rejected { .. })), "len {len}");
    }
}

#[test]
fn iter_yields_the_live_bits() {
    let circuit = compile(|c| {
        let keys = <Bounded<Uint<64>, 3> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        let expected = <Uint<64, Private> as CircuitArg>::declare(c, &ArgPath::root("n"));
        keys.constrain(c);
        let keys = keys.disclose_as::<Keys>(c);
        let expected = expected.disclose_as::<Expected>(c);
        // A pure computation: count the live bits.
        let lives: Vec<_> = keys.iter(c).map(|(live, _)| live).collect();
        let mut n = c.constant(0u64);
        for live in lives {
            n = c.add(n, live.field());
        }
        c.assert(eq(Uint::<64, Public>::from_field_unchecked(n), expected));
    });
    for len in 0..=3u64 {
        run(&circuit, &[len, 1, 2, 3, len]).expect("the live count is the length");
    }
}

// ---- NonEmpty ---------------------------------------------------------------------------

#[test]
fn the_head_always_folds() {
    let circuit = insert_each();
    let out = run(&circuit, &[42, 0, 0, 0, 0]).expect("applies");
    assert_eq!(map_keys(&out.post), vec![42]);
    assert_eq!(map_value(&out.post, 42), Some(0));
}

#[test]
fn the_witness_side_pads_and_splits_and_refuses_the_empty_case() {
    let (len, slots) = Bounded::<u64, 4, Private>::pad(&[1, 2], 0);
    assert_eq!((len, slots), (2, [1, 2, 0, 0]));
    let (head, len, tail) = NonEmpty::<u64, 3, Private>::split(&[9, 8], 0);
    assert_eq!((head, len, tail), (9, 1, [8, 0, 0]));
    assert!(std::panic::catch_unwind(|| NonEmpty::<u64, 3, Private>::split(&[], 0)).is_err());
    assert!(std::panic::catch_unwind(|| Bounded::<u64, 2, Private>::pad(&[1, 2, 3], 0)).is_err());
}

/// The argument labels, for the interface: `keys_head`, `keys_tail_len`,
/// `keys_tail_0` …
#[test]
fn the_slots_are_labelled_head_then_tail() {
    let compiled = compile(|c| {
        let keys = <NonEmpty<Uint<64>, 2> as CircuitArg>::declare(c, &ArgPath::root("keys"));
        let _ = c.arg::<FieldT>("after");
        keys.constrain(c);
    });
    // The serialized ZKIR names its inputs in declaration order.
    let zkir = minocrab_zkir::v3::to_zkir_string(&compiled.ir).expect("serializes");
    let positions: Vec<usize> = ["keys_head", "keys_tail_len", "keys_tail_0", "keys_tail_1", "after"]
        .iter()
        .map(|name| zkir.find(name).unwrap_or_else(|| panic!("input {name} declared in {zkir}")))
        .collect();
    assert!(positions.windows(2).all(|w| w[0] < w[1]), "declared in order: {positions:?}");
}
