//! THE SERIAL REFERENCE STREAM (M41 B, notes/stream-design.org): a fee
//! estimate that is NOT a monoid — an exponential moving average — so it
//! goes behind the accumulator's `popeq`: `report` inserts, `sequence`
//! flushes one to four reports through the step, `settle` takes one.
//!
//! Gates: short flushes of one to four run on the on-chain VM through the
//! executor and match a native fold over the same reports; the flush reads
//! the accumulator exactly once; the row and k table per circuit is printed
//! in the style of notes/nonce-admin.org §11.

use midnight_base_crypto::fab::{
    AlignedValue, Alignment, AlignmentAtom, AlignmentSegment, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_onchain_vm::ops::{Key, Op};
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::{Array, HashMap as StorageHashMap};
use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{Fr, Public};
use minocrab_sim::v3::cost;
use minocrab_ledger::field_key;
use minocrab_sim::v3::exec::{self, Call, ExecError, Executed};
use minocrab_std::v3::{
    circuit, label, Disclose, Discloses, Fold, Ledger, LedgerRepr, NonEmpty, Serial, Stream,
    StreamSpec, Uint,
};

type U64 = Uint<64, Public>;

/// A gas report: what the step looks at is the whole body.
#[derive(LedgerRepr)]
struct Report {
    gas_used: U64,
}

/// `ema' = (7·ema + gas) / 8` — a weighted average, not associative, so a
/// primitive cannot express it and the popeq path must.
struct Ema;

impl Fold<U64> for Ema {
    type Delta = U64;

    fn step(c: &mut Circuit3, s: U64, d: U64) -> U64 {
        let weighted = c.mul(s.field(), 7u64);
        let sum = c.add(weighted, d.field());
        let (q, _rem) = c.div_mod_power_of_two(sum, 3);
        Uint::from_field_unchecked(q)
    }
}

struct Fees;

impl StreamSpec for Fees {
    type Key = U64;
    type Body = Report;
    type Head = U64;
    type State = U64;
    /// Flushed one to four at a time: REST counts the optional slots.
    type Step = Serial<Ema, 3>;

    fn head(_c: &mut Circuit3, body: &Report) -> U64 {
        body.gas_used
    }

    fn delta(_c: &mut Circuit3, head: &U64) -> U64 {
        *head
    }
}

#[derive(Ledger)]
struct Block {
    fees: Stream<Fees>,
}

const BLOCK: Block = Block::new();

// Field map: bodies 0, heads 1, acc 2, staged 3.
const ACC: usize = 2;

label! {
    ReportId = "the report id";
    GasUsed = "the gas used";
    FlushKeys = "the flushed report ids";
}

#[circuit]
fn report(c: &mut Circuit3, id: Uint<64>, gas_used: Uint<64>) -> Discloses<(ReportId, GasUsed)> {
    let id = id.disclose_as::<ReportId>(c);
    let gas_used = gas_used.disclose_as::<GasUsed>(c);
    BLOCK.fees.insert(c, &id, &Report { gas_used });
    Discloses::of(())
}

#[circuit]
fn sequence(c: &mut Circuit3, keys: NonEmpty<Uint<64>, 3>) -> Discloses<(FlushKeys,)> {
    let keys = keys.disclose_as::<FlushKeys>(c);
    BLOCK.fees.sequence(c, keys);
    Discloses::of(())
}

#[circuit]
fn settle(c: &mut Circuit3, id: Uint<64>) -> Discloses<(ReportId,)> {
    let id = id.disclose_as::<ReportId>(c);
    let (_report, _ema) = BLOCK.fees.take(c, &id);
    Discloses::of(())
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

fn state(reports: &[(u64, u64)], acc: u64, staged: &[(u64, u64)]) -> StateValue<InMemoryDB> {
    StateValue::Array(Array::from(vec![map(reports), map(reports), cell(acc), map(staged)]))
}

fn decode(bytes: Vec<u8>) -> u64 {
    let mut le = [0u8; 8];
    le[..bytes.len()].copy_from_slice(&bytes);
    u64::from_le_bytes(le)
}

fn field(st: &StateValue<InMemoryDB>, index: usize) -> StateValue<InMemoryDB> {
    let StateValue::Array(ref fields) = *st else {
        panic!("block array");
    };
    fields.get(index).expect("field").clone()
}

fn cell_of(st: &StateValue<InMemoryDB>, index: usize) -> u64 {
    let f = field(st, index);
    let StateValue::Cell(ref av) = f else {
        panic!("cell");
    };
    decode(av.value.0.first().map(|a| a.0.clone()).unwrap_or_default())
}

fn entry(st: &StateValue<InMemoryDB>, index: usize, key: u64) -> Option<u64> {
    let f = field(st, index);
    let StateValue::Map(ref m) = f else {
        panic!("map");
    };
    let e = m.get(&u64_value(key))?;
    let StateValue::Cell(ref av) = *e else {
        panic!("cells");
    };
    Some(decode(av.value.0.first().map(|a| a.0.clone()).unwrap_or_default()))
}

fn run(compiled: &Compiled3, st: StateValue<InMemoryDB>, inputs: &[u64]) -> Result<Executed, ExecError> {
    let inputs: Vec<Fr> = inputs.iter().map(|&v| Fr::from(v)).collect();
    let ctx = exec::context(st, [7u8; 32]);
    exec::execute(&compiled.ir, &Call::new(&inputs, &[]).with_comm_rand(Fr::from(5u64)), &ctx)
}

fn popeqs(out: &Executed) -> usize {
    out.ops.iter().filter(|op| matches!(op, Op::Popeq { .. })).count()
}

// ---- the gates ------------------------------------------------------------------------

const REPORTS: [(u64, u64); 4] = [(1, 100), (2, 300), (3, 50), (4, 1000)];

fn native_ema(s: u64, d: u64) -> u64 {
    (7 * s + d) / 8
}

#[test]
fn a_report_is_a_pure_insert() {
    let out = run(&report(), state(&[], 200, &[]), &[9, 123]).expect("applies");
    assert_eq!(popeqs(&out), 1, "the not-member check");
    assert_eq!(entry(&out.post, 0, 9), Some(123));
    assert_eq!(entry(&out.post, 1, 9), Some(123));
    assert_eq!(cell_of(&out.post, ACC), 200, "acc untouched");
    // Twice is refused.
    assert!(matches!(run(&report(), out.post, &[9, 1]), Err(ExecError::Rejected { .. })));
}

/// Flushes of one, two, three and four reports, in a chosen order, against
/// a native fold — and the accumulator read once each time.
#[test]
fn short_flushes_of_one_to_four_match_the_native_fold() {
    let sequence = sequence();
    let orders: [Vec<u64>; 4] = [vec![2], vec![3, 1], vec![4, 2, 1], vec![1, 2, 3, 4]];
    for order in orders {
        // inputs: head, tail len, three tail slots (padding zeros).
        let mut inputs = vec![order[0], (order.len() - 1) as u64];
        for i in 1..4 {
            inputs.push(order.get(i).copied().unwrap_or(0));
        }
        let out = run(&sequence, state(&REPORTS, 200, &[]), &inputs)
            .unwrap_or_else(|e| panic!("{order:?}: {e}"));
        let acc_reads = out
            .ops
            .iter()
            .filter(|op| matches!(op, Op::Idx { push_path: false, path, .. } if path.len() == 1 && path.iter().next().is_some_and(|k| *k == Key::Value(field_key(2)))))
            .count();
        assert_eq!(acc_reads, 1, "{order:?}: the accumulator is read once");
        assert_eq!(popeqs(&out), 1 + 2 * order.len(), "{order:?}: acc + (member, head) per report");
        let mut s = 200u64;
        for k in &order {
            let gas = REPORTS.iter().find(|(id, _)| id == k).expect("known").1;
            s = native_ema(s, gas);
            assert_eq!(entry(&out.post, 3, *k), Some(s), "{order:?}: staged[{k}]");
            assert_eq!(entry(&out.post, 1, *k), None, "{order:?}: head removed");
            assert_eq!(entry(&out.post, 0, *k), Some(gas), "{order:?}: body kept for settle");
        }
        assert_eq!(cell_of(&out.post, ACC), s, "{order:?}: acc written once");
    }
    // An unqueued key in a live slot is refused; in a dead slot it is not.
    assert!(matches!(run(&sequence, state(&REPORTS, 200, &[]), &[9, 0, 0, 0, 0]), Err(ExecError::Rejected { .. })));
    run(&sequence, state(&REPORTS, 200, &[]), &[1, 0, 9, 9, 9]).expect("dead slots are unchecked");
    // A tail length past three is refused by the argument constraint.
    assert!(run(&sequence, state(&REPORTS, 200, &[]), &[1, 4, 2, 3, 4]).is_err());
}

#[test]
fn a_settle_takes_the_report_and_its_state() {
    let st = state(&[(2, 300)], 212, &[(2, 212)]);
    let out = run(&settle(), st, &[2]).expect("applies");
    assert_eq!(popeqs(&out), 3, "member + staged + body");
    assert_eq!(entry(&out.post, 3, 2), None);
    assert_eq!(entry(&out.post, 0, 2), None);
    // Unsequenced: refused.
    assert!(matches!(run(&settle(), state(&[(5, 1)], 0, &[]), &[5]), Err(ExecError::Rejected { .. })));
}

/// THE ROW TABLE, in §11's style: the flush proof pays for four slots
/// whatever the count; report and settle are per key.
#[test]
fn the_row_table() {
    println!("| circuit | k | rows |");
    println!("|---|---|---|");
    for (name, compiled) in [("report", report()), ("sequence (1..=4)", sequence()), ("settle", settle())] {
        let (k, rows) = cost(&compiled.ir);
        println!("| {name} | {k} | {rows} |");
    }
    let (k, _) = cost(&sequence().ir);
    assert!(k <= 11, "a four-wide flush stays at k <= 11, got {k}");
}
