//! COMPOSITE SLOTS IN A HEADED BLOCK (notes/ledger-header.org; FR-011): a
//! contract that embeds a standard keeps its `Signet`, its `Pending` and its
//! `Outbox` in the BODY, one root slot along, and the Signet notification
//! the MPC follows carries the moved path.
//!
//! The oracle is compactc's own layout. For a body of fourteen fields or
//! fewer the headed layout IS compactc's layout of the same fields behind
//! one leading field — `[1..=n]` either way — so the headed contract's
//! circuits must be BYTE-IDENTICAL to a twin whose first field is a plain
//! `LedgerField` (standing where the magic sits). That twin is an ordinary
//! compactc-layout block; nothing about it is new. The notification's
//! `depth ‖ path` is then checked on the emitted ZKIR itself: the treasury
//! as shipped notifies `1 ‖ [5]`, the headed one `1 ‖ [6]`.
//!
//! T8 (SC-006), THE COST: a probe of four ledger ops over the same body,
//! with and without the standard, priced by `minocrab_sim::v3::cost` at
//! every size where compactc's shape changes — equal `(k, rows)` and equal
//! instruction counts, as are the headed treasury's three circuits and the
//! shipped ones'. Against a magic declared as an ordinary first field the
//! header is never dearer, and cheaper where that field pushes compactc's
//! layout a level deeper (15 and 225 own fields).
//!
//! IT IS A TEST-ONLY CONTRACT, like `tests/evm_outbox.rs`'s: it adds no
//! circuit to the crate's frozen snapshots or to the ZKIR dump.

use minocrab::v3::{Circuit3, Compiled3};
use minocrab_contracts::evm::erc20::Erc20;
use minocrab_contracts::evm_flow::{
    Contract, Emitted, Failed, Handle, HandleOwned, Inserted, Outbox, Owned, Pending, Succeeded,
};
use minocrab_contracts::signet_flow::{Requested, Settled, Signet};
use minocrab_contracts::treasury::{
    Amount, OwnerCommitment, RefundRecipient, SentAmount, Transfer, Treasury,
};
use minocrab_sim::v3::cost;
use minocrab_std::v3::{
    circuit, pad32, BlockLayout, Bytes, Disclose, Discloses, FieldPath, Ledger, LedgerCell,
    LedgerCounter, LedgerField, LedgerHeader, LedgerMap, LedgerWidth, Uint, B32,
};
use minocrab_zkir::v3::to_zkir_string;

// ---- the standard ----------------------------------------------------------------

/// The tests' placeholder standard: magic-only, a Cell at `[0]`.
#[derive(LedgerHeader)]
struct Mip0099;

impl LedgerHeader for Mip0099 {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
}

// ---- the treasury, headed, and its compactc twin ----------------------------------

/// The README treasury with a standard declared between its two slots:
/// seven body fields, `root[0]` the standard's.
#[derive(Ledger)]
struct Headed {
    signet: Signet,
    std: Mip0099,
    transfers: Pending<Transfer, Owned<Amount>, 2>,
}

const HEADED: Headed = Headed::new();

/// The same body behind a plain leading field: compactc's layout of eight
/// fields, which for a flat body is the headed layout exactly.
#[derive(Ledger)]
struct Leading {
    lead: LedgerField,
    signet: Signet,
    transfers: Pending<Transfer, Owned<Amount>, 2>,
}

const LEADING: Leading = Leading::new();

/// The treasury's three circuits, verbatim, against one block.
macro_rules! treasury_circuits {
    ($block:ident, $send:ident, $complete:ident, $refund:ident) => {
        #[circuit]
        fn $send(
            c: &mut Circuit3,
            evm_nonce: Uint<64>,
            key_version: Uint<8>,
            token: Contract<Erc20>,
            to: Bytes<20>,
            amount: Uint<64>,
        ) -> Discloses<(SentAmount, OwnerCommitment, Requested)> {
            let sent = amount.field().disclose_as::<SentAmount>(c);
            $block.transfers.request_owned::<OwnerCommitment>(
                c,
                token,
                (to, amount.widen::<128>()),
                key_version,
                evm_nonce,
                |_, _| Amount {
                    amount: Uint::from_field_unchecked(sent),
                },
            );
            Discloses::of(())
        }

        #[circuit]
        fn $complete(c: &mut Circuit3, ticket: Succeeded<Transfer>) -> Discloses<Settled> {
            let outcome = $block.transfers.complete(c, ticket);
            let _amount = outcome.env.inner.amount;
            Discloses::of(())
        }

        #[circuit]
        fn $refund(
            c: &mut Circuit3,
            ticket: Failed<Transfer>,
        ) -> Discloses<(Settled, RefundRecipient)> {
            let (_owner, _env, _flag) = $block
                .transfers
                .refund_to_owner::<RefundRecipient>(c, ticket);
            let Amount { amount: _amount } = *_env;
            Discloses::of(())
        }
    };
}

treasury_circuits!(HEADED, send_headed, complete_headed, refund_headed);
treasury_circuits!(LEADING, send_leading, complete_leading, refund_leading);

// ---- the outbox, headed, and its compactc twin ------------------------------------

/// The outbox's seven fields after the Signet's five, a standard first.
#[derive(Ledger)]
struct HeadedOutbox {
    std: Mip0099,
    signet: Signet,
    calls: Outbox<Transfer, HandleOwned<Amount>, 2>,
}

const HEADED_OUTBOX: HeadedOutbox = HeadedOutbox::new();

#[derive(Ledger)]
struct LeadingOutbox {
    lead: LedgerField,
    signet: Signet,
    calls: Outbox<Transfer, HandleOwned<Amount>, 2>,
}

const LEADING_OUTBOX: LeadingOutbox = LeadingOutbox::new();

/// The outbox's call and emit, against one block.
macro_rules! outbox_circuits {
    ($block:ident, $call:ident, $emit:ident) => {
        #[circuit]
        fn $call(
            c: &mut Circuit3,
            key_version: Uint<8>,
            token: Contract<Erc20>,
            to: Bytes<20>,
            amount: Uint<64>,
        ) -> Discloses<(SentAmount, OwnerCommitment, Inserted)> {
            let sent = amount.field().disclose_as::<SentAmount>(c);
            $block.calls.call_owned::<OwnerCommitment>(
                c,
                token,
                (to, amount.widen::<128>()),
                key_version,
                |_, _| Amount {
                    amount: Uint::from_field_unchecked(sent),
                },
            );
            Discloses::of(())
        }

        #[circuit]
        fn $emit(c: &mut Circuit3, handle: Handle) -> Discloses<Emitted> {
            $block.calls.emit(c, handle);
            Discloses::of(())
        }
    };
}

outbox_circuits!(HEADED_OUTBOX, call_headed, emit_headed);
outbox_circuits!(LEADING_OUTBOX, call_leading, emit_leading);

// ---- the tests ----------------------------------------------------------------------

/// The serialized ZKIR — what the dump gate compares.
fn zkir(compiled: minocrab::v3::Compiled3) -> String {
    to_zkir_string(&compiled.ir).expect("the IR serializes")
}

/// The notification's packed `depth ‖ path[0..4]` limb as it appears in
/// the ZKIR: `depth << 8 | path[i] << (16 + 8i)`
/// (`construct_notification_v1`), an immediate serialized little-endian.
fn notification_immediate(depth: u8, path: [u8; 4]) -> String {
    let mut packed: u64 = u64::from(depth) << 8;
    for (i, p) in path.into_iter().enumerate() {
        packed |= u64::from(p) << (16 + 8 * i);
    }
    let bytes = packed.to_le_bytes();
    let len = bytes.iter().rposition(|b| *b != 0).map_or(1, |i| i + 1);
    let hex: String = bytes[..len].iter().map(|b| format!("{b:02x}")).collect();
    format!("\"0x{hex}\"")
}

/// FR-011, the layout: the Signet's five fields at `[1]..[5]`, the pending
/// records at `[6]` (depth 1), the standard's magic at `[0]` — the
/// standard declared BETWEEN the two slots, which does not matter.
#[test]
fn the_signet_and_the_pending_slot_move_one_root_slot_along() {
    assert_eq!(HEADED.std.magic().field_path().as_slice(), &[0]);
    assert_eq!(HEADED.signet.signer.field_path().as_slice(), &[1]);
    assert_eq!(HEADED.signet.mpc_response_key.index(), 2);
    assert_eq!(HEADED.signet.request_nonce.index(), 3);
    assert_eq!(HEADED.signet.caip2_id.index(), 4);
    assert_eq!(HEADED.signet.evm_chain_id.index(), 5);
    assert_eq!(HEADED.transfers.record_path().as_slice(), &[6]);
    assert_eq!(HEADED.transfers.record_path().depth(), 1);
    // The twin agrees, field for field, its plain field where the magic is.
    assert_eq!(LEADING.lead.field_path().as_slice(), &[0]);
    assert_eq!(LEADING.signet.signer.field_path().as_slice(), &[1]);
    assert_eq!(LEADING.transfers.record_path().as_slice(), &[6]);
    // …and the treasury as shipped is where it always was.
    let shipped = &minocrab_contracts::treasury::TREASURY;
    assert_eq!(shipped.signet.signer.field_path().as_slice(), &[0]);
    assert_eq!(shipped.transfers.record_path().as_slice(), &[5]);
}

/// The circuits: every one of the headed treasury's is byte-identical to
/// its compactc twin's (the leading-field block), so every ledger op, the
/// Signet reads and the filed record all use the moved paths.
#[test]
fn the_headed_treasury_is_its_compactc_twin_byte_for_byte() {
    assert_eq!(zkir(send_headed()), zkir(send_leading()), "send");
    assert_eq!(
        zkir(complete_headed()),
        zkir(complete_leading()),
        "complete"
    );
    assert_eq!(zkir(refund_headed()), zkir(refund_leading()), "refund");
}

/// THE NOTIFICATION: the headed `send` notifies `depth 1 ‖ [6, 0, 0, 0]`,
/// the shipped treasury's `depth 1 ‖ [5, 0, 0, 0]` — each carries its own
/// and not the other's.
#[test]
fn the_notification_carries_the_moved_path() {
    let moved = notification_immediate(1, [6, 0, 0, 0]);
    let unmoved = notification_immediate(1, [5, 0, 0, 0]);
    assert_eq!(moved, "\"0x000106\"");
    assert_eq!(unmoved, "\"0x000105\"");
    let headed = zkir(send_headed());
    let shipped = zkir(Treasury::send());
    assert!(headed.contains(&moved), "the headed send notifies [6]");
    assert!(!headed.contains(&unmoved), "…and not [5]");
    assert!(shipped.contains(&unmoved), "the shipped send notifies [5]");
    assert!(!shipped.contains(&moved), "…and not [6]");
}

/// The header costs the treasury nothing (T8, SC-006): each headed circuit
/// has the shipped treasury's instruction count, `k` and rows EXACTLY —
/// `send` (11, 1619), `complete` (15, 25611), `refund` (15, 26009) at the
/// pinned toolchain. An index byte moved at the same depth changes an
/// immediate, never an instruction, and Midnight's cost model prices it
/// the same (see the T8 probe below). Measured, not assumed.
#[test]
fn the_headed_treasury_costs_what_the_shipped_one_does() {
    for (name, headed, shipped) in [
        ("send", send_headed().ir, Treasury::send().ir),
        ("complete", complete_headed().ir, Treasury::complete().ir),
        ("refund", refund_headed().ir, Treasury::refund().ir),
    ] {
        assert_eq!(
            headed.instructions.len(),
            shipped.instructions.len(),
            "{name}: instructions"
        );
        assert_eq!(cost(&headed), cost(&shipped), "{name}: (k, rows)");
    }
}

/// The outbox in a headed block (the standard declared FIRST this time):
/// its seven fields at `[6]..[12]`, the records at `[6]`, and `call` and
/// `emit` byte-identical to the compactc twin's.
#[test]
fn the_headed_outbox_is_its_compactc_twin_byte_for_byte() {
    assert_eq!(
        <Outbox<Transfer, HandleOwned<Amount>, 2> as LedgerWidth>::WIDTH,
        7
    );
    assert_eq!(HEADED_OUTBOX.std.magic().field_path().as_slice(), &[0]);
    assert_eq!(HEADED_OUTBOX.signet.signer.field_path().as_slice(), &[1]);
    assert_eq!(HEADED_OUTBOX.calls.record_path().as_slice(), &[6]);
    assert_eq!(LEADING_OUTBOX.lead.field_path().as_slice(), &[0]);
    assert_eq!(LEADING_OUTBOX.signet.signer.field_path().as_slice(), &[1]);
    assert_eq!(LEADING_OUTBOX.calls.record_path().as_slice(), &[6]);
    assert_eq!(zkir(call_headed()), zkir(call_leading()), "call");
    assert_eq!(zkir(emit_headed()), zkir(emit_leading()), "emit");
    assert!(zkir(emit_headed()).contains(&notification_immediate(1, [6, 0, 0, 0])));
}

// ---- T8: what the header costs a circuit (SC-006) --------------------------------------

type U64 = Uint<64, minocrab::Public>;

/// The cost probe's block with a standard: three own fields behind it.
#[derive(Ledger)]
struct ProbeHeaded {
    std: Mip0099,
    first: LedgerCell<U64>,
    middle: LedgerCounter,
    last: LedgerMap<U64, U64>,
}

/// The same three fields without it.
#[derive(Ledger)]
struct ProbePlain {
    first: LedgerCell<U64>,
    middle: LedgerCounter,
    last: LedgerMap<U64, U64>,
}

/// The same fields behind a magic declared as an ordinary first field —
/// what a contract without the feature writes (compactc's layout).
#[derive(Ledger)]
struct ProbeMagicFirst {
    magic: LedgerCell<B32<minocrab::Public>>,
    first: LedgerCell<U64>,
    middle: LedgerCounter,
    last: LedgerMap<U64, U64>,
}

const PROBE_HEADED: ProbeHeaded = ProbeHeaded::new();
const PROBE_PLAIN: ProbePlain = ProbePlain::new();
const PROBE_MAGIC_FIRST: ProbeMagicFirst = ProbeMagicFirst::new();

/// Body sizes the sweep prices: both sides of every place compactc's shape
/// changes — the flat root's last width (14, 15), the first segmented one
/// (16), the root's second and third segment (30, 31), the sixteen-entry
/// headed roots (211, 224, 225), depth 3 (226), and the byte's end (255,
/// 256).
const T8_SIZES: [usize; 13] = [3, 4, 14, 15, 16, 30, 31, 211, 224, 225, 226, 255, 256];

/// THE PROBE: four ledger ops — a Cell read and a Cell write on the first
/// field, a Counter increment on the middle one, a Map insert on the last —
/// built as an exported entry point is (`finish(true)`, as `#[circuit]`
/// ends) and priced by `minocrab_sim::v3::cost`, `row_snapshot`'s measure.
fn probe(first: FieldPath, middle: FieldPath, last: FieldPath) -> Compiled3 {
    let mut c = Circuit3::new();
    let cell = LedgerCell::<U64>::at_path(first.as_slice());
    let _seen = cell.read(&mut c);
    let v: U64 = Uint::from_field_unchecked(c.constant(42u64));
    cell.write(&mut c, &v);
    LedgerCounter::at_path(middle.as_slice()).increment(&mut c, 1);
    let key: U64 = Uint::from_field_unchecked(c.constant(9u64));
    let value: U64 = Uint::from_field_unchecked(c.constant(7u64));
    LedgerMap::<U64, U64>::at_path(last.as_slice()).insert(&mut c, &key, &value);
    c.finish(true)
}

/// The probe over body fields `0`, `n / 2` and `n - 1` of an `n`-field
/// body, each body field's path given by `path`.
fn probe_over(n: usize, path: impl Fn(usize) -> FieldPath) -> Compiled3 {
    probe(path(0), path(n / 2), path(n - 1))
}

/// `(k, rows, instructions)`.
fn price(compiled: &Compiled3) -> (u8, usize, usize) {
    let (k, rows) = cost(&compiled.ir);
    (k, rows, compiled.ir.instructions.len())
}

/// T8 (SC-006), WITH AND WITHOUT THE HEADER: the probe over the same body
/// costs the same `(k, rows)` and the same instruction count at every size
/// in [`T8_SIZES`] — measured equal, not within a tolerance. The header
/// moves every body path one root slot along at the SAME depth, which
/// changes index immediates and never an instruction; the ±1–2 rows the
/// research allowed for Midnight's fixed-constant cache does not show up in
/// its cost model. At the pinned toolchain the probe is (7, 68) rows for a
/// flat body, (7, 82) at depth 2 and (7, 94) at depth 3, both ways.
#[test]
fn t8_the_header_costs_the_probe_nothing_at_any_size() {
    // The derived blocks themselves, three own fields.
    let headed = probe(
        PROBE_HEADED.first.field_path(),
        PROBE_HEADED.middle.field_path(),
        PROBE_HEADED.last.field_path(),
    );
    let plain = probe(
        PROBE_PLAIN.first.field_path(),
        PROBE_PLAIN.middle.field_path(),
        PROBE_PLAIN.last.field_path(),
    );
    assert_eq!(PROBE_HEADED.std.magic().field_path().as_slice(), &[0]);
    assert_eq!(PROBE_HEADED.first.field_path().as_slice(), &[1]);
    assert_eq!(PROBE_PLAIN.first.field_path().as_slice(), &[0]);
    assert_eq!(price(&headed), price(&plain), "the derived blocks");

    // Every size, through the layout the derive gives each block.
    for n in T8_SIZES {
        let headed = probe_over(n, |k| FieldPath::in_layout(BlockLayout::headed(n), k));
        let plain = probe_over(n, |k| FieldPath::in_layout(BlockLayout::compactc(n), k));
        assert_eq!(price(&headed), price(&plain), "{n} own fields");
    }
}

/// T8, AGAINST A MAGIC DECLARED FIRST (a plain `LedgerCell<B32>` as field
/// 0, compactc's layout of `n + 1` fields — what a contract gets without
/// this feature): the header is never dearer. Up to 14 own fields the two
/// are the same circuit, byte for byte (the compactc parity of
/// `header_small_differential.rs`). Where the extra field pushes compactc's
/// layout one level deeper the headed probe is CHEAPER at equal `k`:
///
/// - 15 own fields (the twin's 16 fields segment: depth 2 against the
///   header's 1): 2 instructions and 14 rows fewer — the Cell write's
///   `idxp` and `insc` (4 + 1 public-input elements) and one more path
///   element (+3) on each of the read, the increment and the insert;
/// - 225 own fields (the twin's 226: depth 3 against 2): the same
///   instructions and 12 rows fewer — +3 elements on each of the four ops.
///
/// Everywhere else the two have one depth and one cost.
#[test]
fn t8_against_a_magic_declared_first_the_header_is_never_dearer() {
    let headed = probe(
        PROBE_HEADED.first.field_path(),
        PROBE_HEADED.middle.field_path(),
        PROBE_HEADED.last.field_path(),
    );
    let magic_first = probe(
        PROBE_MAGIC_FIRST.first.field_path(),
        PROBE_MAGIC_FIRST.middle.field_path(),
        PROBE_MAGIC_FIRST.last.field_path(),
    );
    // The magic where the standard's is, and the three fields after it.
    assert_eq!(PROBE_MAGIC_FIRST.magic.field_path().as_slice(), &[0]);
    assert_eq!(zkir(headed), zkir(magic_first), "the derived blocks");

    for n in T8_SIZES.into_iter().filter(|n| *n < 256) {
        let headed = probe_over(n, |k| FieldPath::in_layout(BlockLayout::headed(n), k));
        let twin = probe_over(n, |k| FieldPath::in_block(n + 1, k + 1));
        let (k_h, rows_h, ins_h) = price(&headed);
        let (k_t, rows_t, ins_t) = price(&twin);
        assert_eq!(k_h, k_t, "{n} own fields: k");
        match n {
            ..=14 => assert_eq!(zkir(headed), zkir(twin), "{n} own fields"),
            15 => {
                assert_eq!((ins_t - ins_h, rows_t - rows_h), (2, 14), "15 own fields");
            }
            225 => {
                assert_eq!((ins_t - ins_h, rows_t - rows_h), (0, 12), "225 own fields");
            }
            _ => assert_eq!((rows_h, ins_h), (rows_t, ins_t), "{n} own fields"),
        }
    }
}

/// The one-op case the compactc parity gate's negative control compiles
/// (`header_n16`'s `wLast`, 15 own fields): the headed write of the last
/// field is 3 Impact instructions at depth 1, the magic-first twin's 5 at
/// depth 2, and the difference in rows is those 5 public-input elements.
#[test]
fn t8_the_negative_controls_last_write_is_five_rows_cheaper_headed() {
    let write = |path: FieldPath| {
        let mut c = Circuit3::new();
        let v: U64 = Uint::from_field_unchecked(c.constant(42u64));
        LedgerCell::<U64>::at_path(path.as_slice()).write(&mut c, &v);
        c.finish(true)
    };
    let headed = write(FieldPath::in_layout(BlockLayout::headed(15), 14));
    let twin = write(FieldPath::in_block(16, 15));
    assert_eq!(headed.ir.instructions.len(), 3);
    assert_eq!(twin.ir.instructions.len(), 5);
    let ((k_h, rows_h), (k_t, rows_t)) = (cost(&headed.ir), cost(&twin.ir));
    assert_eq!(k_h, k_t, "k");
    assert_eq!(rows_t - rows_h, 5, "rows {rows_h} vs {rows_t}");
}
