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
//! IT IS A TEST-ONLY CONTRACT, like `tests/evm_outbox.rs`'s: it adds no
//! circuit to the crate's frozen snapshots or to the ZKIR dump.

use minocrab::v3::Circuit3;
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
    circuit, pad32, Bytes, Disclose, Discloses, Ledger, LedgerField, LedgerHeader, LedgerWidth,
    Uint,
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

/// The header costs the body nothing here: the headed `send` has the
/// shipped treasury's `k` and its row count to within the fixed-constant
/// cache (research F6: an index byte moved at the same depth changes an
/// immediate, never an instruction). Measured, not assumed.
#[test]
fn the_header_moves_no_instruction_and_at_most_a_constant() {
    let headed = send_headed().ir;
    let shipped = Treasury::send().ir;
    assert_eq!(headed.instructions.len(), shipped.instructions.len());
    let (k_h, rows_h) = cost(&headed);
    let (k_s, rows_s) = cost(&shipped);
    assert_eq!(k_h, k_s, "k");
    assert!(rows_h.abs_diff(rows_s) <= 2, "rows {rows_h} vs {rows_s}");
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
