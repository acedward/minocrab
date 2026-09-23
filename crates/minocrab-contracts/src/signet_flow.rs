//! THE SIGNET ROUND TRIP'S SHARED MACHINERY — the block's configuration,
//! the record a request files, and the attested output a settle verifies.
//!
//! Every Sig Network operation a Midnight contract makes is one future split
//! across two transactions. A REQUEST circuit files a signing record and
//! cross-calls the Signet singleton so the MPC comes to read it; a SETTLE
//! circuit, in a later transaction, verifies the MPC's attestation over the
//! typed response and consumes the record. The ledger map entry IS the
//! suspended continuation; the attestation is the value the future resolves
//! with. (notes/signet-async.org is the design of record — M35.)
//!
//! # What lives here, and why
//!
//! M35 put a `Pending<Env, Resp>` slot here, keyed by a hand-written
//! `Response` type per kind. M37 rung D replaced it with
//! [`crate::evm_flow::Pending<Call, Env, WORDS>`], which is keyed by the CALL
//! ([`crate::evm::EvmCall`]) and derives the kind byte, the response type,
//! the ABI words, the selector, the gas envelope and the signing path from
//! it. What is left in this module is what the typed slot is BUILT ON, and
//! it is here rather than there because it is the WIRE — the MPC's side of
//! the protocol, which no contract-facing API gets to reshape:
//!
//! - [`Signet`] — the block's one configuration slot (signer address, MPC
//!   response key, request nonce, caip2 id, EVM chain id). Five ledger
//!   fields a contract declares once; `#[derive(Ledger)]` threads its offset
//!   into every `Pending` and `Fired` slot, which is why a typed request
//!   takes no `&SELF.signet`.
//! - `file_request` — the filing every request does, whatever the slot:
//!   read the context, assemble the record, hash its id, assert freshness,
//!   bump the nonce, store it, store the environment beside it, notify the
//!   singleton with the record map's own path. `evm_flow`'s three request
//!   methods are this function plus a transaction.
//! - [`EvmTx`] and [`SignRequest`] — the transaction shape the record holds
//!   and the request that files it. `evm::build_tx` builds the first from a
//!   call type; nothing outside this crate writes either by hand.
//! - [`Attested`] — `serializedOutput` on the wire: the kind byte then the
//!   attested value. The signed preimage is over exactly its limbs.
//! - [`Outcome`] — what a settle hands back.
//! - The three disclosure labels and the [`Requested`] / [`Settled`] label
//!   sets a request and a settle publish.
//!
//! RETIRED IN M37 RUNG D, with the vault that used them: `Pending`, `Fired`,
//! the `Settle` ticket, the `Response` and `FailureResponse` traits, and
//! `Commit<T>` (whose domain was a `&str` at both ends —
//! [`crate::evm_flow::Commit<T, Tag>`] takes it as a type, so a `to` and an
//! `open` that disagree no longer compiles).
//!
//! TYPES CONSTRAIN THE AUTHOR, ASSERTS CONSTRAIN THE PROVER: nothing in
//! either module removes an in-circuit check on untrusted input.
//!
//! NO TIMEOUT, by decision (dmd, 2026-09-05): a request with no response
//! stays pending; a refund happens only on an ATTESTED non-success
//! ([`crate::evm_flow::Pending::refund`]).
//!
//! # What does not compile
//!
//! An environment with a private field (`#[derive(LedgerRepr)]` has no impl
//! at `Private`, so a secret cannot be captured across the suspension by
//! accident — what Rust's own `async` would silently do):
//!
//! ```compile_fail
//! use minocrab::{Private, Public};
//! use minocrab_std::v3::{LedgerRepr, Uint, B32};
//!
//! #[derive(LedgerRepr)]
//! struct Env { amount: Uint<64, Public>, secret: B32<Private> }
//! ```
//!
//! THE SAME CODE WITH THE ONE CHANGE REVERTED compiles:
//!
//! ```
//! use minocrab::Public;
//! use minocrab_std::v3::{LedgerRepr, Uint, B32};
//!
//! #[derive(LedgerRepr)]
//! struct Env { amount: Uint<64, Public>, secret: B32<Public> }
//! ```

use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::{Private, Public};
use minocrab_ledger::{XcallCommitment, XcallEntryPointHash};
use minocrab_std::v3::borsh::{BorshReader, CircuitBorsh, FieldSpec, LayoutPath, Limbs};
use minocrab_std::v3::Serializer;
use minocrab_std::v3::Assumed;
use minocrab_std::v3::{
    is_true, kernel, label, not, ArgPath, BlockLayout, CircuitAbi, CircuitArg, Disclose,
    LedgerCell, LedgerCounter, LedgerField, LedgerMap, LedgerRepr, LedgerWidth, Prim,
    Secp256k1Point, Uint,
};
use signet_signer_interface::notification::construct_notification_v1;
use signet_signer_interface::{RequestId, SignetSigner};

use crate::common::{Caip2Id, SigningPath};
use crate::signet::{
    self, EventRecordV2, EvmCalldata, EvmType2TxParams,
};

// ---- the response types ------------------------------------------------------

/// `serializedOutput` on the wire: the kind byte then the response body.
///
/// What the MPC signs is `keccak256(requestId ‖ borsh(Attested))`, and
/// [`crate::evm_flow::Pending::complete`] asserts `kind == Call::KIND`
/// before verifying — so an
/// attestation issued for another settle circuit fails the kind check, and
/// one with a forged kind fails the signature.
pub struct Attested<R> {
    pub kind: Uint<8>,
    pub output: R,
}

impl<R: CircuitAbi> CircuitAbi for Attested<R> {
    const SLOTS: usize = <Uint<8>>::SLOTS + R::SLOTS;

    fn push_atoms(atoms: &mut Vec<minocrab::AlignmentAtom>) {
        <Uint<8>>::push_atoms(atoms);
        R::push_atoms(atoms);
    }

    fn push_prims(prims: &mut Vec<Prim>) {
        <Uint<8>>::push_prims(prims);
        R::push_prims(prims);
    }
}

impl<R: CircuitArg> CircuitArg for Attested<R> {
    fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
        Attested {
            kind: <Uint<8>>::declare(c, &path.field("kind")),
            output: R::declare(c, &path.field("output")),
        }
    }

    fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
        self.kind.push_slots(slots);
        self.output.push_slots(slots);
    }
}

impl<R: CircuitBorsh<Private>> CircuitBorsh<Private> for Attested<R> {
    const LEN: usize = 1 + R::LEN;

    fn read<Rd: BorshReader<Private>>(c: &mut Circuit3, r: &mut Rd) -> Self {
        Attested {
            kind: <Uint<8>>::read(c, r),
            output: R::read(c, r),
        }
    }

    fn push_limbs(&self, limbs: &mut Limbs<Private>) {
        self.kind.push_limbs(limbs);
        self.output.push_limbs(limbs);
    }

    fn push_segments(&self, out: &mut Serializer<Private>) {
        self.kind.push_segments(out);
        self.output.push_segments(out);
    }

    fn constrain_canonical(&self, c: &mut Circuit3) {
        self.kind.constrain_canonical(c);
        self.output.constrain_canonical(c);
    }

    fn push_layout(path: &LayoutPath, offset: &mut usize, out: &mut Vec<FieldSpec>) {
        <Uint<8>>::push_layout(&path.field("kind"), offset, out);
        R::push_layout(&path.field("output"), offset, out);
    }
}

// ---- the shared configuration slot ------------------------------------------------

/// The block's ONE Signet configuration: five consecutive ledger fields a
/// contract declares once (`signet: Signet` in its `#[derive(Ledger)]`
/// block) and every `Pending` slot reads through.
///
/// Holding these together is what lets `Pending::request` take the sender,
/// chain id, caip2 id and nonce from CONTEXT and `Pending::settle` the MPC
/// key — none of them is an argument a circuit can pass wrongly. The
/// `signer` cell is `sealed` (written at deployment, never by a circuit).
pub struct Signet {
    /// `sealed ledger signetSigner: SignetSigner` — the singleton's address.
    pub signer: LedgerField,
    /// `mpcResponseKey: Secp256k1Point` — the key every attestation is
    /// verified under.
    pub mpc_response_key: LedgerCell<Secp256k1Point<Public>>,
    /// `signetRequestNonce: Counter` — one per contract, so two requests
    /// with identical parameters still hash to distinct ids.
    pub request_nonce: LedgerCounter,
    /// `caip2Id: Bytes<32>` — the destination chain, in the record.
    pub caip2_id: LedgerCell<Caip2Id<Public>>,
    /// `evmChainId: Uint<64>` — the destination chain, in the signed
    /// transaction.
    pub evm_chain_id: LedgerCell<Uint<64, Public>>,
}

impl Signet {
    /// The five fields from flat body index `start` under `layout` (what
    /// `#[derive(Ledger)]` calls). In a block with a standard the five
    /// follow the headed layout like every other body field.
    pub const fn at_layout(layout: BlockLayout, start: usize) -> Self {
        Signet {
            signer: LedgerField::at_layout(layout, start),
            mpc_response_key: LedgerCell::at_layout(layout, start + 1),
            request_nonce: LedgerCounter::at_layout(layout, start + 2),
            caip2_id: LedgerCell::at_layout(layout, start + 3),
            evm_chain_id: LedgerCell::at_layout(layout, start + 4),
        }
    }

    /// The five fields from flat index `start` of a block of `total`
    /// fields, at compactc's layout.
    pub const fn at_block(total: usize, start: usize) -> Self {
        Signet::at_layout(BlockLayout::compactc(total), start)
    }

    /// The deployment's writes, for a contract's `initialize`: the MPC key
    /// and the two chain identifiers. The signer cell is sealed and set at
    /// deployment; the nonce starts at zero.
    pub fn initialize(
        &self,
        c: &mut Circuit3,
        mpc_response_key: &Secp256k1Point<Public>,
        caip2_id: &Caip2Id<Public>,
        evm_chain_id: &Uint<64, Public>,
    ) {
        self.mpc_response_key.write(c, mpc_response_key);
        self.caip2_id.write(c, caip2_id);
        self.evm_chain_id.write(c, evm_chain_id);
    }

    /// The singleton's calling handle, by the sealed cell's path.
    fn signer(&self) -> SignetSigner {
        SignetSigner::at_field_path(self.signer.field_path().as_slice())
    }
}

impl LedgerWidth for Signet {
    const WIDTH: usize = 5;
}

// ---- the request ---------------------------------------------------------------------

/// The EVM transaction a request asks the MPC to sign, WITHOUT its chain
/// id: that is the block's ([`Signet::evm_chain_id`]), read by
/// `Pending::request`, so a request cannot name another chain than the
/// one the contract is configured for.
pub struct EvmTx<const WORDS: usize> {
    pub nonce: Wire3<FieldT, Private>,
    pub max_priority_fee_per_gas: Wire3<FieldT, Private>,
    pub max_fee_per_gas: Wire3<FieldT, Private>,
    pub gas_limit: Wire3<FieldT, Private>,
    pub to: Wire3<FieldT, Private>,
    pub value: Wire3<FieldT, Private>,
    /// `Maybe<EvmCalldata>`: the flag then the (always-present, zero-filled
    /// when absent) calldata.
    pub calldata_is_some: Wire3<FieldT, Private>,
    pub calldata: EvmCalldata<Private, WORDS>,
}

/// What a request circuit supplies: whose key signs (the version and the
/// derivation path) and what it signs.
pub struct SignRequest<const WORDS: usize> {
    pub key_version: Uint<8>,
    pub path: SigningPath<Private>,
    pub tx: EvmTx<WORDS>,
}

label! {
    /// The request id, disclosed on filing: the map key.
    pub RequestIdFiled = "request id";
    /// The whole signing record, disclosed on filing: what the MPC reads.
    pub RequestRecordFiled = "request record";
    /// The request id, disclosed on settling: which entry is consumed.
    pub RequestIdSettled = "settle request id";
}

/// Everything `Pending::request` discloses — the label set a request
/// circuit declares, as one type.
pub type Requested = (
    RequestIdFiled,
    RequestRecordFiled,
    XcallEntryPointHash,
    XcallCommitment,
);

/// Everything `Pending::settle` discloses.
pub type Settled = (RequestIdSettled,);

/// What a settle hands back: the consumed entry, typed.
pub struct Outcome<Env, R, const WORDS: usize> {
    /// The request id, disclosed.
    pub request_id: RequestId<Public>,
    /// The environment the request filed — an inline read of the entry
    /// written at the request, so an assumption (M42 B): the proof uses it
    /// freely; writing it back is `.stale(c)`.
    pub env: Assumed<Env>,
    /// The attested output — verified, its kind checked, its fields
    /// canonical.
    pub output: R,
    /// The signing record the MPC read, should the settle logic need a
    /// field of it (the request nonce, say). Read inline, likewise.
    pub record: Assumed<EventRecordV2<WORDS>>,
}

/// The filing every request does, whatever the slot: read the context,
/// assemble the record with `kind`, hash it, assert freshness, bump the
/// nonce, store the record, run `after_insert` (a `Pending` stores its
/// environment there), notify the MPC with the record map's own path.
pub(crate) fn file_request<const WORDS: usize>(
    c: &mut Circuit3,
    signet: &Signet,
    records: &LedgerMap<RequestId<Public>, EventRecordV2<WORDS>>,
    req: SignRequest<WORDS>,
    kind: u8,
    after_insert: impl FnOnce(&mut Circuit3, RequestId<Public>),
) -> RequestId<Public> {
    // Kept even though guard threading no longer uses it: dropping this
    // `Copy` would renumber every later identifier, moving the ZKIR
    // (notes/edsl-trim.org §B, the removal's zero-movement gate).
    let _ = c.constant(1u64);
    let zero = c.constant(0u64);
    let me = kernel::cache_self_address(c);
    // Read, hashed into the record, bumped: the filing's one
    // read-modify-write, named as such (M42 B; notes/nonce-admin.org §10.1).
    let nonce = signet.request_nonce.read(c).stale(c);
    let caip2 = signet.caip2_id.read(c).stale(c);
    let chain_id = signet.evm_chain_id.read(c).stale(c);
    let tx = req.tx;
    let tx_params = EvmType2TxParams::<Private, WORDS> {
        chain_id: chain_id.field().private(),
        nonce: tx.nonce,
        max_priority_fee_per_gas: tx.max_priority_fee_per_gas,
        max_fee_per_gas: tx.max_fee_per_gas,
        gas_limit: tx.gas_limit,
        to: tx.to,
        value: tx.value,
        calldata_is_some: tx.calldata_is_some,
        calldata: tx.calldata,
        access_list_entry_count: zero.private(),
    };
    let record = signet::construct_sign_bidirectional_event_v2(
        c,
        me.private(),
        nonce.field().private(),
        req.key_version.field(),
        req.path,
        tx_params,
        caip2.private(),
        kind,
    );

    let request_id = c.region("signet flow: file", |c| {
        let request_id =
            signet::calculate_request_id_v2(c, &record).disclose_as::<RequestIdFiled>(c);
        let exists = records.member(c, &request_id);
        c.assert(not(is_true(exists)).message("Request already exists"));
        signet.request_nonce.increment(c, 1);
        let stored = EventRecordV2::from_limbs(record.limbs().disclose_as::<RequestRecordFiled>(c));
        records.insert(c, &request_id, &stored);
        after_insert(c, request_id);
        request_id
    });

    c.region("signet flow: notify", |c| {
        // Receiver first (compactc's order; the argument below emits).
        let signer = signet.signer().pin(c);
        let path = records.field_path();
        let mut bytes = [0u8; 4];
        bytes[..path.as_slice().len()].copy_from_slice(path.as_slice());
        let notification = construct_notification_v1::<Public>(c, &me.bytes(), path.depth(), bytes);
        signer.sign_bidirectional(c, request_id, notification);
    });
    request_id
}
