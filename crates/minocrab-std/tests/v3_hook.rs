//! THE HOOKS' GATE (M42 A, notes/hooks-design.org).
//!
//! Every `Hook` method is run through the executor (`minocrab_sim::v3::exec`,
//! Midnight's on-chain VM) against a SEEDED state, and the resulting cells
//! and map entries are read back — including each failure row of the
//! design's table, which must be refused by the VM at landing and never by
//! the circuit. Then the attachment semantics: hooks run after the whole
//! body, in attachment order, under the guard captured at `c.then`, and are
//! refused inside `when_private`. Every hook that applies is BLIND: zero
//! reads, zero public transcript outputs. And NO HIDDEN OPS: a hook lowers
//! to the byte-identical ZKIR of the explicit `minocrab_ledger` op lists.

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
    branch, cell_add_at, cell_snapshot_into_map_at, dup, emit, idx_path, member, push_cell,
    ImpactElem, LedgerKey, LedgerValue,
};
use minocrab_sim::v3::exec::{self, Call, ExecError, Executed};
use minocrab_std::v3::{entry, Bool, Hook, Ledger, LedgerCell, LedgerMap, Uint};
use minocrab_zkir::v3::to_zkir_string;

type U64 = Uint<64, Public>;

/// The block under test.
#[derive(Ledger)]
struct Block {
    n: LedgerCell<U64>,
    m: LedgerCell<U64>,
    snap: LedgerMap<U64, U64>,
    b: LedgerCell<Bool<Public>>,
    flag: LedgerCell<Bool<Public>>,
    first: LedgerCell<U64>,
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

fn map_of(entries: &[(u64, u64)]) -> StateValue<InMemoryDB> {
    let mut m: StorageHashMap<AlignedValue, StateValue<InMemoryDB>, InMemoryDB> =
        StorageHashMap::new();
    for (k, v) in entries {
        m = m.insert(u64_value(*k), cell(u64_value(*v)));
    }
    StateValue::Map(m)
}

#[derive(Clone, Default)]
struct Seed {
    n: u64,
    m: u64,
    snap: Vec<(u64, u64)>,
    b: bool,
    flag: bool,
    first: u64,
}

impl Seed {
    fn state(&self) -> StateValue<InMemoryDB> {
        let fields = vec![
            cell(u64_value(self.n)),
            cell(u64_value(self.m)),
            map_of(&self.snap),
            cell(bool_value(self.b)),
            cell(bool_value(self.flag)),
            cell(u64_value(self.first)),
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

fn map_u64(state: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<u64> {
    let f = field(state, index);
    let StateValue::Map(ref m) = f else {
        panic!("field {index} is a map");
    };
    let entry = m.get(&u64_value(key))?;
    let StateValue::Cell(ref av) = *entry else {
        panic!("map entry under {key} is a cell, got {:?}", *entry);
    };
    let bytes = av.value.0.first().map(|a| a.0.clone()).unwrap_or_default();
    let mut le = [0u8; 8];
    le[..bytes.len()].copy_from_slice(&bytes);
    Some(u64::from_le_bytes(le))
}

const N: usize = 0;
const M: usize = 1;
const SNAP: usize = 2;
const B: usize = 3;
const FLAG: usize = 4;
const FIRST: usize = 5;

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
    // `entry` finishes with a communications commitment; the hand-built
    // circuits (`compile`) without one. The randomness is ignored there.
    let call = Call::new(&inputs, &[]).with_comm_rand(Fr::from(11u64));
    exec::execute(&compiled.ir, &call, &ctx)
}

/// Apply and require success; the transcript READ nothing.
fn apply(compiled: &Compiled3, seed: &Seed, inputs: &[u64]) -> Executed {
    let out = run(compiled, seed, inputs).expect("the hook applies");
    assert!(out.reads.is_empty(), "a hook performs no read: {:?}", out.reads);
    assert_eq!(out.run.consumed_public, 0, "a hook consumes no public transcript output");
    assert!(out.preimage.public_transcript_outputs.is_empty());
    out
}

/// Apply and require the LEDGER to refuse it (the circuit was satisfied).
fn refused(compiled: &Compiled3, seed: &Seed, inputs: &[u64]) {
    match run(compiled, seed, inputs) {
        Err(ExecError::NotApplied { .. }) => {}
        other => panic!("the ledger refuses this transaction, got {other:?}"),
    }
}

// ---- the read-modify-writes ----------------------------------------------------------

#[test]
fn add_and_sub_blind_with_overflow_and_underflow_refused() {
    let add = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().add(&BLOCK.n, d));
    });
    let out = apply(&add, &Seed { n: 40, ..Seed::default() }, &[0, 2]);
    assert_eq!(cell_u64(&out.post, N), 42);
    refused(&add, &Seed { n: u64::MAX, ..Seed::default() }, &[0, 1]);

    let sub = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().sub(&BLOCK.n, d));
    });
    let out = apply(&sub, &Seed { n: 40, ..Seed::default() }, &[0, 2]);
    assert_eq!(cell_u64(&out.post, N), 38);
    refused(&sub, &Seed { n: 1, ..Seed::default() }, &[0, 2]);
}

#[test]
fn a_literal_delta_is_an_immediate() {
    let add = compile(|c| {
        let (_k, _d) = two_args(c);
        c.then(Hook::new().add(&BLOCK.n, 1u64).sub(&BLOCK.m, 3u64));
    });
    // The transcript embeds no wire beyond the two disclosed arguments.
    let wires = add
        .disclosures
        .iter()
        .filter(|d| d.label == "impact public input")
        .count();
    assert_eq!(wires, 0, "a literal delta names no wire");
    let out = apply(&add, &Seed { n: 4, m: 10, ..Seed::default() }, &[0, 0]);
    assert_eq!(cell_u64(&out.post, N), 5);
    assert_eq!(cell_u64(&out.post, M), 7);
}

#[test]
fn max_and_min_keep_the_right_arm() {
    let max = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().max(&BLOCK.n, d));
    });
    assert_eq!(cell_u64(&apply(&max, &Seed { n: 10, ..Seed::default() }, &[0, 25]).post, N), 25);
    assert_eq!(cell_u64(&apply(&max, &Seed { n: 30, ..Seed::default() }, &[0, 25]).post, N), 30);
    assert_eq!(cell_u64(&apply(&max, &Seed { n: 25, ..Seed::default() }, &[0, 25]).post, N), 25);

    let min = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().min(&BLOCK.n, d));
    });
    assert_eq!(cell_u64(&apply(&min, &Seed { n: 10, ..Seed::default() }, &[0, 25]).post, N), 10);
    assert_eq!(cell_u64(&apply(&min, &Seed { n: 30, ..Seed::default() }, &[0, 25]).post, N), 25);
}

#[test]
fn and_and_or_on_a_boolean_cell() {
    let and = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().and(&BLOCK.b, Bool::from_field_unchecked(d.field())));
    });
    let or = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().or(&BLOCK.b, Bool::from_field_unchecked(d.field())));
    });
    for (a, d) in [(false, false), (false, true), (true, false), (true, true)] {
        let seed = Seed { b: a, ..Seed::default() };
        assert_eq!(cell_bool(&apply(&and, &seed, &[0, u64::from(d)]).post, B), a && d, "and {a} {d}");
        assert_eq!(cell_bool(&apply(&or, &seed, &[0, u64::from(d)]).post, B), a || d, "or {a} {d}");
    }
    // Literals too.
    let lit = compile(|c| {
        let (_k, _d) = two_args(c);
        c.then(Hook::new().or(&BLOCK.b, true));
    });
    assert!(cell_bool(&apply(&lit, &Seed::default(), &[0, 0]).post, B));
}

// ---- the plain writes ---------------------------------------------------------------

#[test]
fn write_insert_and_remove_as_effects() {
    let circuit = compile(|c| {
        let (k, d) = two_args(c);
        c.then(
            Hook::new()
                .write(&BLOCK.n, d)
                .insert(&BLOCK.snap, k, d)
                .remove(&BLOCK.snap, 77u64),
        );
    });
    let seed = Seed { n: 1, snap: vec![(77, 5)], ..Seed::default() };
    let out = apply(&circuit, &seed, &[9, 42]);
    assert_eq!(cell_u64(&out.post, N), 42);
    assert_eq!(map_u64(&out.post, SNAP, 9), Some(42));
    assert_eq!(map_u64(&out.post, SNAP, 77), None, "removed");
    // Remove of an absent key is a no-op, never a failure.
    let out = apply(&circuit, &Seed::default(), &[9, 42]);
    assert_eq!(map_u64(&out.post, SNAP, 77), None);
}

// ---- slot to slot -------------------------------------------------------------------

#[test]
fn copy_snapshots_a_cell_into_a_map_and_copy_cell_between_cells() {
    let circuit = compile(|c| {
        let (k, _d) = two_args(c);
        c.then(Hook::new().copy(&BLOCK.n, &BLOCK.snap, k).copy_cell(&BLOCK.n, &BLOCK.m));
    });
    let out = apply(&circuit, &Seed { n: 4242, m: 1, ..Seed::default() }, &[9, 0]);
    assert_eq!(map_u64(&out.post, SNAP, 9), Some(4242), "snap[9] = n");
    assert_eq!(cell_u64(&out.post, M), 4242, "m = n");
    assert_eq!(cell_u64(&out.post, N), 4242, "n untouched");
}

#[test]
fn move_entry_moves_a_present_entry_and_refuses_an_absent_source() {
    let circuit = compile(|c| {
        let (k, d) = two_args(c);
        c.then(Hook::new().move_entry(&BLOCK.snap, k, d));
    });
    let seed = Seed { snap: vec![(5, 77), (6, 1)], ..Seed::default() };
    let out = apply(&circuit, &seed, &[5, 9]);
    assert_eq!(map_u64(&out.post, SNAP, 9), Some(77), "moved to 9");
    assert_eq!(map_u64(&out.post, SNAP, 5), None, "gone from 5");
    assert_eq!(map_u64(&out.post, SNAP, 6), Some(1), "others untouched");
    // Overwrites an existing destination, as `insert` does.
    let out = apply(&circuit, &seed, &[5, 6]);
    assert_eq!(map_u64(&out.post, SNAP, 6), Some(77));
    // An absent source fails the transaction — and does NOT plant a Null.
    refused(&circuit, &seed, &[8, 9]);
}

// ---- the branches -------------------------------------------------------------------

#[test]
fn if_absent_runs_the_arm_only_when_the_key_is_absent() {
    let circuit = compile(|c| {
        let (k, d) = two_args(c);
        c.then(Hook::new().if_absent(&BLOCK.snap, k, |h| h.insert(&BLOCK.snap, k, d).add(&BLOCK.n, 1u64)));
    });
    let out = apply(&circuit, &Seed { n: 1, ..Seed::default() }, &[9, 42]);
    assert_eq!(map_u64(&out.post, SNAP, 9), Some(42), "absent: inserted");
    assert_eq!(cell_u64(&out.post, N), 2, "absent: the arm ran");
    let seed = Seed { n: 1, snap: vec![(9, 7)], ..Seed::default() };
    let out = apply(&circuit, &seed, &[9, 42]);
    assert_eq!(map_u64(&out.post, SNAP, 9), Some(7), "present: untouched");
    assert_eq!(cell_u64(&out.post, N), 1, "present: the arm was skipped");
    // A failure INSIDE the arm fails only when the arm runs.
    refused(&circuit, &Seed { n: u64::MAX, ..Seed::default() }, &[9, 42]);
    let seed = Seed { n: u64::MAX, snap: vec![(9, 7)], ..Seed::default() };
    apply(&circuit, &seed, &[9, 42]);
}

#[test]
fn if_below_runs_the_arm_only_when_the_cell_is_below_the_bound() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().if_below(&BLOCK.n, d, |h| h.write(&BLOCK.m, 1u64)));
    });
    assert_eq!(cell_u64(&apply(&circuit, &Seed { n: 3, ..Seed::default() }, &[0, 5]).post, M), 1);
    assert_eq!(cell_u64(&apply(&circuit, &Seed { n: 5, ..Seed::default() }, &[0, 5]).post, M), 0);
    assert_eq!(cell_u64(&apply(&circuit, &Seed { n: 9, ..Seed::default() }, &[0, 5]).post, M), 0);
}

#[test]
fn if_unset_is_the_first_write() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().if_unset(&BLOCK.flag, |h| h.write(&BLOCK.first, d).write(&BLOCK.flag, true)));
    });
    let out = apply(&circuit, &Seed::default(), &[0, 9]);
    assert_eq!(cell_u64(&out.post, FIRST), 9);
    assert!(cell_bool(&out.post, FLAG));
    // A second first-write is skipped.
    let seed = Seed { first: 9, flag: true, ..Seed::default() };
    let out = apply(&circuit, &seed, &[0, 11]);
    assert_eq!(cell_u64(&out.post, FIRST), 9);
    assert!(cell_bool(&out.post, FLAG));
}

// ---- composition and attachment ------------------------------------------------------

#[test]
fn then_concatenates_and_hooks_run_in_attachment_order() {
    let concat = compile(|c| {
        let (_k, _d) = two_args(c);
        c.then(Hook::new().write(&BLOCK.n, 1u64).then(Hook::new().write(&BLOCK.n, 2u64)));
    });
    assert_eq!(cell_u64(&apply(&concat, &Seed::default(), &[0, 0]).post, N), 2);

    let ordered = compile(|c| {
        let (_k, _d) = two_args(c);
        c.then(Hook::new().write(&BLOCK.n, 1u64));
        c.then(Hook::new().write(&BLOCK.n, 2u64));
    });
    assert_eq!(cell_u64(&apply(&ordered, &Seed::default(), &[0, 0]).post, N), 2);
    let reversed = compile(|c| {
        let (_k, _d) = two_args(c);
        c.then(Hook::new().write(&BLOCK.n, 2u64));
        c.then(Hook::new().write(&BLOCK.n, 1u64));
    });
    assert_eq!(cell_u64(&apply(&reversed, &Seed::default(), &[0, 0]).post, N), 1);
}

#[test]
fn a_hook_runs_after_the_whole_body_whatever_the_position_of_then() {
    let circuit = compile(|c| {
        let (_k, d) = two_args(c);
        c.then(Hook::new().add(&BLOCK.n, 1u64));
        // An inline write that appears AFTER the `then` still lands first.
        BLOCK.n.write(c, &d);
    });
    let out = run(&circuit, &Seed { n: 100, ..Seed::default() }, &[0, 10]).expect("applies");
    assert_eq!(cell_u64(&out.post, N), 11, "write 10, then += 1");
    assert_eq!(circuit_deferred_is_flushed(), 0);
}

fn circuit_deferred_is_flushed() -> usize {
    let mut c = Circuit3::new();
    c.then(Hook::new().add(&BLOCK.n, 1u64));
    assert_eq!(c.deferred_count(), 1);
    c.flush_deferred();
    c.deferred_count()
}

#[test]
fn entry_flushes_the_hooks_before_the_outputs() {
    let compiled = entry(|c, (): ()| {
        c.then(Hook::new().add(&BLOCK.n, 1u64));
        let ten = Uint::from_field_unchecked(c.constant(10u64));
        BLOCK.n.write(c, &ten);
    });
    let out = run(&compiled, &Seed { n: 100, ..Seed::default() }, &[]).expect("applies");
    assert_eq!(cell_u64(&out.post, N), 11);
}

#[test]
fn a_hook_attached_inside_when_is_emitted_under_that_guard() {
    let circuit = compile(|c| {
        let (g, _d) = two_args(c);
        let g = Bool::from_field_unchecked(g.field());
        c.when(g, |c| {
            c.then(Hook::new().add(&BLOCK.n, 1u64));
        });
        // And a hook attached outside runs regardless.
        c.then(Hook::new().add(&BLOCK.m, 1u64));
    });
    let seed = Seed { n: 5, m: 5, ..Seed::default() };
    let on = apply(&circuit, &seed, &[1, 0]);
    assert_eq!(cell_u64(&on.post, N), 6, "guard on: the hook ran");
    assert_eq!(cell_u64(&on.post, M), 6);
    let off = apply(&circuit, &seed, &[0, 0]);
    assert_eq!(cell_u64(&off.post, N), 5, "guard off: absent from the transcript");
    assert_eq!(cell_u64(&off.post, M), 6, "the unguarded hook still ran");
    // The guard is in the TRANSCRIPT, not the circuit: the skipped hook's
    // ops are not run at all (four fewer ops than the on-path).
    assert_eq!(on.ops.len(), off.ops.len() + 4);
}

#[test]
#[should_panic(expected = "inside `when_private`")]
fn a_hook_inside_when_private_is_refused_at_build_time() {
    compile(|c| {
        let g = c.arg::<FieldT>("g");
        let g = Bool::from_field_unchecked(g);
        c.when_private(g, |c| {
            c.then(Hook::new().add(&BLOCK.n, 1u64));
        });
    });
}

// ---- the reach bound, positive side ----------------------------------------------------

/// Four `at_key` steps is the deepest copy destination the type admits; the
/// module's compile-fail doctest is the fifth. This only has to compile.
#[allow(dead_code)]
fn a_copy_four_keys_deep_compiles(c: &mut Circuit3) {
    const DEEP: LedgerMap<U64, LedgerMap<U64, LedgerMap<U64, LedgerMap<U64, LedgerMap<U64, U64>>>>> =
        LedgerMap::at(1);
    let k = Uint::<64, Public>::from_field_unchecked(c.constant(1u64));
    let four = DEEP.at_key(c, &k).at_key(c, &k).at_key(c, &k).at_key(c, &k);
    c.then(Hook::new().copy(&BLOCK.n, &four, k).move_entry(&four, k, k));
}

// ---- no hidden ops --------------------------------------------------------------------

#[test]
fn a_hook_lowers_to_the_explicit_op_lists_byte_for_byte() {
    let hook = compile(|c| {
        let (k, d) = two_args(c);
        c.then(
            Hook::new()
                .add(&BLOCK.n, d)
                .copy(&BLOCK.n, &BLOCK.snap, k)
                .if_absent(&BLOCK.snap, 3u64, |h| h.add(&BLOCK.m, 1u64)),
        );
    });
    let explicit = compile(|c| {
        let (k, d) = two_args(c);
        let n = [LedgerKey::Field(0)];
        let m = [LedgerKey::Field(1)];
        let snap = [LedgerKey::Field(2)];
        let one = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(1u64))]);
        let three = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(3u64))]);
        let d = LedgerValue::bytes(8, vec![ImpactElem::Wire(d.field())]);
        let k = LedgerValue::bytes(8, vec![ImpactElem::Wire(k.field())]);
        emit(c, &cell_add_at(&n, &d));
        emit(c, &cell_snapshot_into_map_at(&n, &snap, &k));
        let arm = cell_add_at(&m, &one);
        emit(
            c,
            &[
                dup(0),
                idx_path(false, false, &snap),
                push_cell(false, &three),
                member(),
                branch(arm.len() as u32),
            ],
        );
        emit(c, &arm);
    });
    assert_eq!(
        to_zkir_string(&hook.ir).expect("lowers"),
        to_zkir_string(&explicit.ir).expect("lowers")
    );
}
