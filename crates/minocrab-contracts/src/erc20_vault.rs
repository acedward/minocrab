//! `erc20-vault` (signet-midnight-examples `0d9c1660`) — THE benchmark
//! target: the shielded cross-chain ERC-20 vault, on the Poseidon protocol
//! (M28). Ported circuit by circuit, instruction order following the Compact
//! source; each port carries a differential test against compactc's
//! artifact (`tests/erc20_vault_differential.rs`).
//!
//! Seventeen circuits: `initialise`; the two allowances (`approveStata`,
//! `approveRouter`); and five flows, each a request circuit plus one or two
//! settle circuits — deposit (`startDeposit` / `completeDeposit`), withdraw
//! (`startWithdraw` / `completeWithdraw` / `refundWithdraw`), swap
//! (`startSwap` / `completeSwap` / `refundSwap`), supply (`startSupply` /
//! `completeSupply` / `refundSupply`) and redeem (`startRedeem` /
//! `completeRedeem` / `refundRedeem`).
//!
//! WHAT CHANGED FROM THE NINE-CIRCUIT VAULT (notes/vault-refresh.org):
//! every commitment is `upgradeFromTransient(transientHash(…))` — the
//! identity commitment, the refund commitment and the token domain
//! separator; every request id and attestation digest is Poseidon too
//! (`signet::calculate_request_id`); each flow keeps a SETTLE VIEW beside
//! its request record (who may settle, which token, how much, as typed
//! ledger values) so no settle circuit re-parses calldata; refunds are one
//! circuit per flow, gated by the fixed 5-byte failure output; and the
//! ledger block is 21 fields, which compactc SEGMENTS (six fields at
//! `[0, i]`, fifteen at `[1, i − 6]`) — `#[derive(Ledger)]` computes the
//! same paths, and the notification's depth and path bytes are read off the
//! map handle rather than written by hand.
//!
//! The Compact ledger block, in declaration order (the field index):
//! ```text
//! export ledger signBidirectionalEventMap: …;                    // 0  [0,0]
//! sealed ledger signetSigner: SignetSigner;                      // 1  [0,1]
//! export ledger mpcResponseKey: Secp256k1Point;                  // 2  [0,2]
//! export ledger signetRequestNonce: Counter;                     // 3  [0,3]
//! export ledger initialised: Counter;                            // 4  [0,4]
//! export ledger vaultEvmAddress: Bytes<20>;                      // 5  [0,5]
//! export ledger evmChainId: Uint<64>;                            // 6  [1,0]
//! export ledger caip2Id: Bytes<32>;                              // 7  [1,1]
//! sealed ledger deployer: Bytes<32>;                             // 8  [1,2]
//! export ledger depositEventMap: …;                              // 9  [1,3]
//! export ledger depositSettleViews: Map<RequestId, DepositSettleView>;   // 10 [1,4]
//! export ledger withdrawSettleViews: Map<RequestId, WithdrawSettleView>; // 11 [1,5]
//! export ledger uniswapRouter: Bytes<20>;                        // 12 [1,6]
//! export ledger swapEventMap: …;                                 // 13 [1,7]
//! export ledger swapSettleViews: Map<RequestId, SwapSettleView>; // 14 [1,8]
//! export ledger stataUnderlying: Bytes<20>;                      // 15 [1,9]
//! export ledger stataToken: Bytes<20>;                           // 16 [1,10]
//! export ledger supplyEventMap: …;                               // 17 [1,11]
//! export ledger supplySettleViews: Map<RequestId, SupplySettleView>; // 18 [1,12]
//! export ledger redeemEventMap: …;                               // 19 [1,13]
//! export ledger redeemSettleViews: Map<RequestId, RedeemSettleView>; // 20 [1,14]
//! ```

use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::{Private, Public};
use minocrab_ledger::{XcallCommitment, XcallEntryPointHash};
use minocrab_std::v3::hash::upgrade_from_transient;
use minocrab_std::v3::kernel;
use minocrab_std::v3::{
    contract, eq, is_true, label, not, own_public_key, Bytes, BytesN,
    Check, CircuitArg, CoinColor, CoinNonce, CoinRecipient, Disclose, Discloses, Either, Ledger,
    LedgerCell, LedgerCounter, LedgerField, LedgerMap, LedgerRepr, Maybe, Secp256k1Point,
    TokenDomainSeparator, Uint, B32,
};

use signet_signer_interface::notification::construct_notification_v1;
use signet_signer_interface::SignetSigner;

use crate::common::{self, RefundCommitment, UserCommitment};
use crate::signet;

// ---- disclosure labels ---------------------------------------------------------------

// What each circuit discloses, one zero-sized type per logical value; a
// circuit's `Discloses<(…)>` names exactly the set it makes public, and the
// generated test beside each circuit fails on any other disclosure.
label! {
    VaultEvmAddress = "the vault's derived EVM address";
    UniswapRouter = "the Uniswap router address";
    StataUnderlying = "the Aave underlying ERC20 (USDC)";
    StataToken = "the Aave stata wrapper (ERC-4626)";
    EvmChainId = "the EVM chain id";
    Caip2Id = "the CAIP-2 chain id";
    MpcResponseKey = "the MPC response key";
    DepositorCommitment = "depositor identity commitment";
    RequestId = "request id";
    RequestRecord = "request record";
    DepositedErc20 = "the deposited ERC20";
    DepositedAmount = "the deposited amount";
    WithdrawnErc20 = "the withdrawn ERC20";
    WithdrawnAmount = "the withdrawn amount";
    SurrenderedCoinNonce = "surrendered coin nonce";
    SurrenderedCoinColor = "surrendered coin color";
    SurrenderedCoinValue = "surrendered coin value";
    WithdrawerRefundCommitment = "withdrawer refund commitment";
    SoldErc20 = "the sold ERC20";
    BoughtErc20 = "the bought ERC20";
    SwapAmountOut = "the swap's amountOut";
    SwapAmountInMaximum = "the swap's amountInMaximum";
    SwapperRefundCommitment = "swapper refund commitment";
    SuppliedAmount = "the supplied amount";
    SupplierRefundCommitment = "supplier refund commitment";
    RedeemedShares = "the redeemed shares";
    RedeemerRefundCommitment = "redeemer refund commitment";
    ApprovedErc20 = "the approved ERC20";
    SettleRequestId = "settle request id";
    WithdrawalOutcome = "withdrawal EVM outcome";
    RefundMintNonce = "refund mint nonce";
    RefundRecipient = "own public key as refund recipient";
    SwapRecipient = "own public key as swap recipient";
    SwapMintNonce = "swap mint nonce";
    SwapChangeNonce = "swap change nonce";
    AttestedAmountIn = "attested amountIn spent";
    SupplyRecipient = "own public key as supply recipient";
    SupplyMintNonce = "supply mint nonce";
    AttestedShares = "attested shares minted";
    RedeemRecipient = "own public key as redeem recipient";
    RedeemMintNonce = "redeem mint nonce";
    AttestedAssets = "attested assets redeemed";
    ClaimRequestId = "claim request id";
    ClaimRecipientTag = "claim recipient tag";
    ClaimRecipientSide = "claim recipient side";
    ClaimRecipientOwnKey = "own public key as claim recipient";
    ClaimRecipientKey = "claim recipient key";
    ClaimRecipientContract = "claim recipient contract";
    ClaimMintNonce = "claim mint nonce";
}

// ---- constants -----------------------------------------------------------------------

/// The domain-separation prefix of `userCommitment`.
pub const USER_PAD: &str = "vault:user:";

/// The domain-separation prefix of `vaultTokenDomainSeparator`.
pub const TOKEN_PAD: &str = "erc20:vault:";

/// The domain-separation prefix of `refundCommitment`.
pub const REFUND_PAD: &str = "vault:refund:";

/// The vault's own MPC key-derivation path, `pad(32, "vault")`.
pub const VAULT_PATH: &str = "vault";

/// `vaultResponseSchema()` — the exact-width 34-byte ABI schema string, used
/// as both schemas of every transfer / approve request.
pub const VAULT_RESPONSE_SCHEMA: &[u8] = b"[{\"name\":\"success\",\"type\":\"bool\"}]";

/// `swapOutputSchema()` (38 bytes) and `swapRespondSchema()` (37 bytes).
pub const SWAP_OUTPUT_SCHEMA: &[u8] = b"[{\"name\":\"amountIn\",\"type\":\"uint256\"}]";
pub const SWAP_RESPOND_SCHEMA: &[u8] = b"[{\"name\":\"amountIn\",\"type\":\"uint64\"}]";

/// `supplyOutputSchema()` (36 bytes) and `supplyRespondSchema()` (35 bytes).
pub const SUPPLY_OUTPUT_SCHEMA: &[u8] = b"[{\"name\":\"shares\",\"type\":\"uint256\"}]";
pub const SUPPLY_RESPOND_SCHEMA: &[u8] = b"[{\"name\":\"shares\",\"type\":\"uint64\"}]";

/// `redeemOutputSchema()` (36 bytes) and `redeemRespondSchema()` (35 bytes).
pub const REDEEM_OUTPUT_SCHEMA: &[u8] = b"[{\"name\":\"assets\",\"type\":\"uint256\"}]";
pub const REDEEM_RESPOND_SCHEMA: &[u8] = b"[{\"name\":\"assets\",\"type\":\"uint64\"}]";

/// `transfer(address,uint256)`'s selector.
pub const TRANSFER_SELECTOR: [u8; 4] = [0xa9, 0x05, 0x9c, 0xbb];
/// `approve(address,uint256)`'s selector.
pub const APPROVE_SELECTOR: [u8; 4] = [0x09, 0x5e, 0xa7, 0xb3];
/// `exactOutputSingle((address,address,uint24,address,uint256,uint256,uint160))`.
pub const EXACT_OUTPUT_SINGLE_SELECTOR: [u8; 4] = [0x50, 0x23, 0xb4, 0xdf];
/// ERC-4626 `deposit(uint256,address)`.
pub const DEPOSIT_SELECTOR: [u8; 4] = [0x6e, 0x55, 0x3f, 0x65];
/// ERC-4626 `redeem(uint256,address,address)`.
pub const REDEEM_SELECTOR: [u8; 4] = [0xba, 0x08, 0x76, 0x52];

/// The MPC's fixed failure output: 0xdeadbeef ‖ 0x01, 5 bytes — attested
/// only for a transaction that NEVER EXECUTED.
pub const MPC_FAILURE_OUTPUT: [u8; 5] = [0xde, 0xad, 0xbe, 0xef, 0x01];

/// The ABI word counts of the calldata shapes the vault signs.
pub const VAULT_WORDS: usize = 2;
pub const SWAP_WORDS: usize = 7;
pub const SUPPLY_WORDS: usize = 2;
pub const REDEEM_WORDS: usize = 3;

/// The schema widths ARE the schema literals' lengths, so an event type
/// and the schema bytes it carries cannot drift apart.
pub const VAULT_SCHEMA_LEN: usize = VAULT_RESPONSE_SCHEMA.len();
pub const SWAP_OUTPUT_LEN: usize = SWAP_OUTPUT_SCHEMA.len();
pub const SWAP_RESPOND_LEN: usize = SWAP_RESPOND_SCHEMA.len();
pub const SUPPLY_OUTPUT_LEN: usize = SUPPLY_OUTPUT_SCHEMA.len();
pub const SUPPLY_RESPOND_LEN: usize = SUPPLY_RESPOND_SCHEMA.len();
pub const REDEEM_OUTPUT_LEN: usize = REDEEM_OUTPUT_SCHEMA.len();
pub const REDEEM_RESPOND_LEN: usize = REDEEM_RESPOND_SCHEMA.len();

/// The contract-FIXED gas envelope of the vault-signed requests: 1 gwei
/// priority fee, 30 gwei cap, and a per-call limit.
///
/// THE THREE LIMITS NOW LIVE IN THE LIBRARY (M38 rung A,
/// notes/evm-interfaces.org §2.3): a per-function gas default is a fact
/// about the function, so [`crate::evm::erc20::CALL_GAS`],
/// [`crate::evm::uniswap_v3::SWAP_GAS`] and
/// [`crate::evm::erc4626::CALL_GAS`] define them and these three names are
/// aliases. Same numbers, one definition — `evm::tests::
/// the_gas_defaults_are_the_vaults` pins the equality, and this lineage's
/// hand-written circuits keep spelling the constants they always did.
pub const FIXED_PRIORITY_FEE: u64 = 1_000_000_000;
pub const FIXED_MAX_FEE: u64 = 30_000_000_000;
pub const ERC20_CALL_GAS: u64 = crate::evm::erc20::CALL_GAS;
pub const SWAP_GAS: u64 = crate::evm::uniswap_v3::SWAP_GAS;
pub const LENDING_GAS: u64 = crate::evm::erc4626::CALL_GAS;

/// The event instantiations, one per request shape.
pub type VaultEvent<V> =
    signet::SignBidirectionalEvent<V, VAULT_WORDS, VAULT_SCHEMA_LEN, VAULT_SCHEMA_LEN>;
pub type SwapEvent<V> =
    signet::SignBidirectionalEvent<V, SWAP_WORDS, SWAP_OUTPUT_LEN, SWAP_RESPOND_LEN>;
pub type SupplyEvent<V> =
    signet::SignBidirectionalEvent<V, SUPPLY_WORDS, SUPPLY_OUTPUT_LEN, SUPPLY_RESPOND_LEN>;
pub type RedeemEvent<V> =
    signet::SignBidirectionalEvent<V, REDEEM_WORDS, REDEEM_OUTPUT_LEN, REDEEM_RESPOND_LEN>;

/// The same records as the maps hold them — distinct types per shape, so a
/// 3-word record cannot be read with 2-word offsets.
pub type VaultRecord = signet::EventRecord<VAULT_WORDS, VAULT_SCHEMA_LEN, VAULT_SCHEMA_LEN>;
pub type SwapRecord = signet::EventRecord<SWAP_WORDS, SWAP_OUTPUT_LEN, SWAP_RESPOND_LEN>;
pub type SupplyRecord = signet::EventRecord<SUPPLY_WORDS, SUPPLY_OUTPUT_LEN, SUPPLY_RESPOND_LEN>;
pub type RedeemRecord = signet::EventRecord<REDEEM_WORDS, REDEEM_OUTPUT_LEN, REDEEM_RESPOND_LEN>;

pub use crate::common::secp256k1_point_atoms;

// ---- the settle views ------------------------------------------------------------------

/// `struct DepositSettleView { commitment: Bytes<32>; erc20: Bytes<20>;
/// amount: Uint<64> }` — the depositor commitment that gates
/// `completeDeposit`, and what it mints.
#[derive(LedgerRepr)]
pub struct DepositSettleView {
    pub commitment: UserCommitment<Public>,
    pub erc20: Bytes<20, Public>,
    pub amount: Uint<64, Public>,
}

/// `struct WithdrawSettleView { commitment; erc20; amount }` — the refund
/// commitment that gates a re-mint, and what it re-mints.
#[derive(LedgerRepr)]
pub struct WithdrawSettleView {
    pub commitment: RefundCommitment<Public>,
    pub erc20: Bytes<20, Public>,
    pub amount: Uint<64, Public>,
}

/// `struct SwapSettleView { commitment; tokenIn; tokenOut; amountOut;
/// amountInMaximum }`.
#[derive(LedgerRepr)]
pub struct SwapSettleView {
    pub commitment: RefundCommitment<Public>,
    pub token_in: Bytes<20, Public>,
    pub token_out: Bytes<20, Public>,
    pub amount_out: Uint<64, Public>,
    pub amount_in_maximum: Uint<64, Public>,
}

/// `struct SupplySettleView { commitment; amount }`.
#[derive(LedgerRepr)]
pub struct SupplySettleView {
    pub commitment: RefundCommitment<Public>,
    pub amount: Uint<64, Public>,
}

/// `struct RedeemSettleView { commitment; shares }`.
#[derive(LedgerRepr)]
pub struct RedeemSettleView {
    pub commitment: RefundCommitment<Public>,
    pub shares: Uint<64, Public>,
}

// ---- the ledger block ------------------------------------------------------------------

/// THE LEDGER BLOCK — the Compact `ledger` declarations in the module doc,
/// as types. Declaration order IS the field index and `#[derive(Ledger)]`
/// computes each field's segmented path from it, so nothing here writes a
/// path or an atom list: a map knows its key's and value's FAB atoms from
/// the types, and a lookup hands back the view rather than limbs.
#[derive(Ledger)]
pub struct Vault {
    pub sign_bidirectional_event_map: LedgerMap<signet::RequestId<Public>, VaultRecord>,
    /// `sealed ledger signetSigner: SignetSigner` — a handle read through the
    /// interface crate's own `SignetSigner::at_field_path`.
    pub signet_signer: LedgerField,
    pub mpc_response_key: LedgerCell<Secp256k1Point<Public>>,
    pub signet_request_nonce: LedgerCounter,
    pub initialised: LedgerCounter,
    pub vault_evm_address: LedgerCell<Bytes<20, Public>>,
    pub evm_chain_id: LedgerCell<Uint<64, Public>>,
    pub caip2_id: LedgerCell<common::Caip2Id<Public>>,
    /// `sealed ledger deployer: Bytes<32>` — write-once at deployment; the
    /// read is an ordinary cell read.
    pub deployer: LedgerCell<UserCommitment<Public>>,
    pub deposit_event_map: LedgerMap<signet::RequestId<Public>, VaultRecord>,
    pub deposit_settle_views: LedgerMap<signet::RequestId<Public>, DepositSettleView>,
    pub withdraw_settle_views: LedgerMap<signet::RequestId<Public>, WithdrawSettleView>,
    pub uniswap_router: LedgerCell<Bytes<20, Public>>,
    pub swap_event_map: LedgerMap<signet::RequestId<Public>, SwapRecord>,
    pub swap_settle_views: LedgerMap<signet::RequestId<Public>, SwapSettleView>,
    pub stata_underlying: LedgerCell<Bytes<20, Public>>,
    pub stata_token: LedgerCell<Bytes<20, Public>>,
    pub supply_event_map: LedgerMap<signet::RequestId<Public>, SupplyRecord>,
    pub supply_settle_views: LedgerMap<signet::RequestId<Public>, SupplySettleView>,
    pub redeem_event_map: LedgerMap<signet::RequestId<Public>, RedeemRecord>,
    pub redeem_settle_views: LedgerMap<signet::RequestId<Public>, RedeemSettleView>,
}

/// The vault's ledger block. A `const`: the whole thing is field paths, so
/// it exists at compile time and costs nothing at run time.
pub const VAULT: Vault = Vault::new();

// ---- shared pieces -----------------------------------------------------------------------

/// `assert(initialised >= 1, "Not initialised")`.
fn assert_initialised(c: &mut Circuit3) {
    let init = VAULT.initialised.read(c);
    c.assert(init.gt(0u64).message("Not initialised"));
}

fn b32_eq(a: &B32<Private>, b: &B32<Private>) -> Check<Private> {
    eq(a.hi, b.hi).and(eq(a.lo, b.lo))
}

/// `userCommitment(sk)` — `upgradeFromTransient(transientHash([pad(32,
/// "vault:user:"), sk]))`, the MPC's key-derivation PATH for a deposit.
fn user_commitment(c: &mut Circuit3, sk: &common::SecretKey<Private>) -> UserCommitment<Private> {
    common::commitment_transient(c, sk)
}

/// `refundCommitment(sk, requestId)` — `upgradeFromTransient(transientHash([
/// pad(32, "vault:refund:"), sk, requestId]))`. Deliberately NOT
/// `userCommitment`: reuse would link settle views to depositor identities.
fn refund_commitment(
    c: &mut Circuit3,
    sk: &common::SecretKey<Private>,
    request_id: &signet::RequestId<Private>,
) -> RefundCommitment<Private> {
    let sk = sk.bytes();
    let rid = request_id.bytes();
    c.region("refund commitment (transientHash)", |c| {
        let pad = B32::pad(c, REFUND_PAD);
        let f = c.transient_hash(&[pad.hi.private(), pad.lo.private(), sk.hi, sk.lo, rid.hi, rid.lo]);
        RefundCommitment(upgrade_from_transient(c, f))
    })
}

/// `vaultTokenDomainSeparator(erc20Address)` —
/// `upgradeFromTransient(transientHash([pad(32, "erc20:vault:"),
/// erc20Address as Field as Bytes<32>]))`. The address is a `Bytes<20>`
/// limb (160 bits, by its argument type or its ledger atom), so its
/// `Bytes<32>` rendering is `[hi: 0, lo: addr]`.
fn vault_token_domain_separator(
    c: &mut Circuit3,
    erc20_address: Wire3<FieldT, Public>,
) -> TokenDomainSeparator<Public> {
    c.region("token domain separator (transientHash)", |c| {
        let pad = B32::pad(c, TOKEN_PAD);
        let zero = c.constant(0u64);
        let f = c.transient_hash(&[pad.hi, pad.lo, zero, erc20_address]);
        TokenDomainSeparator(upgrade_from_transient(c, f))
    })
}

/// The contract-FIXED gas envelope as three private wires: priority fee,
/// fee cap, and the call's limit.
fn fixed_gas(c: &mut Circuit3, limit: u64) -> [Wire3<FieldT, Private>; 3] {
    let priority_fee = c.constant(FIXED_PRIORITY_FEE);
    let max_fee = c.constant(FIXED_MAX_FEE);
    let gas = c.constant(limit);
    [priority_fee.private(), max_fee.private(), gas.private()]
}

/// `EvmCalldata<WORDS> { selector, noWords: WORDS, words }`.
fn calldata<const WORDS: usize>(
    c: &mut Circuit3,
    selector: &[u8; 4],
    words: [B32<Private>; WORDS],
) -> signet::EvmCalldata<Private, WORDS> {
    let selector = c.constant(minocrab::Fr::from_le_bytes(selector).unwrap());
    let no_words = c.constant(WORDS as u64);
    signet::EvmCalldata {
        selector: selector.private(),
        no_words: no_words.private(),
        words,
    }
}

/// `EvmType2TxParams<WORDS, 0, 0> { chainId: evmChainId, nonce, gas…, to,
/// value: 0, calldata: some(calldata), accessList: [] }`. The caller reads
/// `evmChainId` itself, in the struct literal's order — before a `to` that
/// is a cell read (`approveStata`, `startSwap`, the lending flows), after
/// the calldata's reads.
fn tx_params<const WORDS: usize>(
    c: &mut Circuit3,
    chain_id: Uint<64, Public>,
    evm_nonce: Wire3<FieldT, Private>,
    gas: [Wire3<FieldT, Private>; 3],
    to: Wire3<FieldT, Private>,
    calldata: signet::EvmCalldata<Private, WORDS>,
) -> signet::EvmType2TxParams<Private, WORDS> {
    let zero = c.constant(0u64);
    let one = c.constant(1u64);
    signet::EvmType2TxParams {
        chain_id: chain_id.field().private(),
        nonce: evm_nonce,
        max_priority_fee_per_gas: gas[0],
        max_fee_per_gas: gas[1],
        gas_limit: gas[2],
        to,
        value: zero.private(),
        calldata_is_some: one.private(),
        calldata,
        access_list_entry_count: zero.private(),
    }
}

/// `constructSignBidirectionalEvent(kernel.self(), signetRequestNonce as
/// Uint<64>, keyVersion, path, ecdsa, unused, pad(64, ""), evmType2,
/// txParams, caip2Id, outputSchema, respondSchema)` — with the three ledger
/// reads in compactc's order: the nonce (a `const` before the call), then
/// the receiver `kernel.self()`, then `caip2Id` among the arguments.
fn assemble_request<const WORDS: usize, const LEN_OUT: usize, const LEN_RESPOND: usize>(
    c: &mut Circuit3,
    key_version: Wire3<FieldT, Private>,
    path: common::SigningPath<Private>,
    tx_params: signet::EvmType2TxParams<Private, WORDS>,
    output_schema: &[u8],
    respond_schema: &[u8],
) -> signet::SignBidirectionalEvent<Private, WORDS, LEN_OUT, LEN_RESPOND> {
    // The request nonce is read, hashed into the record, and bumped: the
    // one read-modify-write every filing makes, named as such (M42 B).
    let request_nonce = VAULT.signet_request_nonce.read(c).stale(c);
    let sender = kernel::self_address(c).private();
    let caip2 = VAULT.caip2_id.read(c).stale(c).private();
    let output_schema = BytesN::<Private, LEN_OUT>::literal(c, output_schema);
    let respond_schema = BytesN::<Private, LEN_RESPOND>::literal(c, respond_schema);
    signet::construct_sign_bidirectional_event(
        c,
        sender,
        request_nonce.field().private(),
        key_version,
        path,
        tx_params,
        caip2,
        output_schema,
        respond_schema,
    )
}

/// `requestId = disclose(calculateRequestId(request))` +
/// `assert(!map.member(requestId), "Request already exists")`.
fn check_fresh_request<const WORDS: usize, const LEN_OUT: usize, const LEN_RESPOND: usize>(
    c: &mut Circuit3,
    request: &signet::SignBidirectionalEvent<Private, WORDS, LEN_OUT, LEN_RESPOND>,
    map: &LedgerMap<signet::RequestId<Public>, signet::EventRecord<WORDS, LEN_OUT, LEN_RESPOND>>,
) -> signet::RequestId<Public> {
    let request_id_priv = signet::calculate_request_id(c, request);
    c.region("record: freshness", |c| {
        let request_id = request_id_priv.disclose_as::<RequestId>(c);
        let exists = map.member(c, &request_id);
        c.assert(not(is_true(exists)).message("Request already exists"));
        request_id
    })
}

/// `signetRequestNonce.increment(1)` + `map.insert(requestId,
/// disclose(request))`.
fn insert_request<const WORDS: usize, const LEN_OUT: usize, const LEN_RESPOND: usize>(
    c: &mut Circuit3,
    request: &signet::SignBidirectionalEvent<Private, WORDS, LEN_OUT, LEN_RESPOND>,
    map: &LedgerMap<signet::RequestId<Public>, signet::EventRecord<WORDS, LEN_OUT, LEN_RESPOND>>,
    request_id: &signet::RequestId<Public>,
) {
    c.region("record: insert", |c| {
        VAULT.signet_request_nonce.increment(c, 1);
        let record =
            signet::EventRecord::from_limbs(request.limbs().disclose_as::<RequestRecord>(c));
        map.insert(c, request_id, &record);
    });
}

/// `signetSigner.signBidirectional(requestId,
/// constructSignBidirectionalEventNotificationV1(kernel.self(), depth,
/// path))` — the signer read, the caller's own address, the notification and
/// the cross-contract call. The notification's depth and path bytes ARE the
/// request map's compiled ledger path, read off the handle.
fn notify_signet<K, V>(
    c: &mut Circuit3,
    request_id: &signet::RequestId<Public>,
    map: &LedgerMap<K, V>,
) {
    c.region("xcall: notify signet", |c| {
        // compactc evaluates a call's RECEIVER before its argument
        // expressions, so the sealed-cell read is pinned FIRST.
        let signer =
            SignetSigner::at_field_path(VAULT.signet_signer.field_path().as_slice()).pin(c);
        let me = kernel::self_address(c);
        let path = map.field_path();
        let mut bytes = [0u8; 4];
        bytes[..path.as_slice().len()].copy_from_slice(path.as_slice());
        let notification = construct_notification_v1::<Public>(c, &me.bytes(), path.depth(), bytes);
        signer.sign_bidirectional(c, *request_id, notification);
    });
}

/// The request-only tail: freshness, record, notify.
fn record_and_notify<const WORDS: usize, const LEN_OUT: usize, const LEN_RESPOND: usize>(
    c: &mut Circuit3,
    request: &signet::SignBidirectionalEvent<Private, WORDS, LEN_OUT, LEN_RESPOND>,
    map: &LedgerMap<signet::RequestId<Public>, signet::EventRecord<WORDS, LEN_OUT, LEN_RESPOND>>,
) -> signet::RequestId<Public> {
    let request_id = check_fresh_request(c, request, map);
    insert_request(c, request, map, &request_id);
    notify_signet(c, &request_id, map);
    request_id
}

/// `struct ShieldedCoinInfo { nonce: Bytes<32>, color: Bytes<32>,
/// value: Uint<128> }` as an argument.
#[derive(CircuitArg)]
struct ShieldedCoinArg {
    nonce: CoinNonce<Private>,
    color: CoinColor<Private>,
    value: Uint<128>,
}

/// `color = tokenType(vaultTokenDomainSeparator(erc20), kernel.self());
/// assert(coin.color == color); assert(coin.value == amount)` — the
/// surrendered coin must be THIS vault token, of exactly `amount`.
fn assert_vault_coin(
    c: &mut Circuit3,
    erc20: Wire3<FieldT, Public>,
    amount: Wire3<FieldT, Private>,
    coin: &ShieldedCoinArg,
    color_message: &'static str,
    value_message: &'static str,
) {
    let domain_sep = vault_token_domain_separator(c, erc20);
    let me = kernel::self_address(c);
    let color = minocrab_std::v3::token_type(c, &domain_sep, &me.bytes());
    c.assert(b32_eq(&coin.color.bytes(), &color.private().bytes()).message(color_message));
    c.assert(eq(coin.value.field(), amount).message(value_message));
}

/// `receiveShielded(disclose(coin)); sendImmediateShielded(disclose(coin),
/// shieldedBurnAddress(), disclose(coin).value)` — custody, then the
/// full-value burn.
fn burn_surrendered_coin(c: &mut Circuit3, one: Wire3<FieldT, Public>, coin: ShieldedCoinArg) {
    let coin = minocrab_std::v3::ShieldedCoinInfo3 {
        nonce: coin.nonce.disclose_as::<SurrenderedCoinNonce>(c),
        color: coin.color.disclose_as::<SurrenderedCoinColor>(c),
        value: coin.value.field().disclose_as::<SurrenderedCoinValue>(c),
    };
    common::receive_shielded(c, &coin);
    common::burn_coin(c, one, &coin);
}

/// `struct Secp256k1Point { x: Bytes<32>, y: Bytes<32> }` — the `bigR`
/// nonce point of an ECDSA signature.
#[derive(CircuitArg)]
struct BigR {
    x: B32<Private>,
    y: B32<Private>,
}

/// `struct Secp256k1EcdsaSignature { bigR: Secp256k1Point, s: Bytes<32>,
/// recoveryId: Uint<8> }` — the MPC's attestation, in circuit-input form
/// (`bigR.x` and `s` little-endian). Compact wraps it in a one-field
/// `RespondBidirectionalEvent { signature }`; the argument labels keep the
/// `respond` abbreviation the interface snapshot froze. `bigR.y` and
/// `recoveryId` are part of the wire shape and read by nothing, as in the
/// Compact original.
#[derive(CircuitArg)]
struct RespondSignature {
    big_r: BigR,
    s: B32<Private>,
    recovery_id: Uint<8>,
}

/// `assert(verifyRespondBidirectionalEvent<LEN>(disclosedRequestId,
/// serializedOutput, disclose(respondBidirectionalEvent), mpcResponseKey),
/// "Invalid attestation signature")` — the `mpcResponseKey` read, the
/// Poseidon digest over the id and the presented output, and the ECDSA
/// check.
fn assert_attestation<const LEN_OUTPUT: usize>(
    c: &mut Circuit3,
    request_id: &signet::RequestId<Public>,
    respond: &RespondSignature,
    output_limbs: &[Wire3<FieldT, Private>],
) {
    let mpc_key = VAULT.mpc_response_key.read(c);
    let rid_priv = request_id.private();
    let valid = signet::verify_respond_bidirectional_event::<Private, LEN_OUTPUT>(
        c,
        &rid_priv,
        output_limbs,
        &signet::Secp256k1SigLimbs {
            big_r_x: respond.big_r.x,
            s: respond.s,
        },
        mpc_key.point().private(),
    );
    c.assert_with(valid, Some("Invalid attestation signature"));
}

/// `assertAttestedFailureOutput(disclosedRequestId, respondBidirectionalEvent,
/// serializedOutput)` — the gate every refund circuit runs first: the fixed
/// 5-byte failure output is attested only for a transaction that NEVER
/// EXECUTED, and its width routes it here.
fn assert_attested_failure_output(
    c: &mut Circuit3,
    request_id: &signet::RequestId<Public>,
    respond: &RespondSignature,
    serialized_output: Wire3<FieldT, Private>,
) {
    assert_initialised(c);
    assert_attestation::<5>(c, request_id, respond, &[serialized_output]);
    let is_failure = c.test_eq(
        serialized_output,
        minocrab::Fr::from_le_bytes(&MPC_FAILURE_OUTPUT).unwrap(),
    );
    c.assert_with(is_failure, Some("Not the MPC failure output"));
}

/// `deserialize<{ success: Boolean }, 1>(serializedOutput).success` — the
/// packed Boolean is (byte == 1).
fn attested_success(c: &mut Circuit3, serialized_output: Wire3<FieldT, Private>) -> Wire3<FieldT, Private> {
    let one = c.constant(1u64);
    c.test_eq(serialized_output, one.private())
}

/// `assert(refundCommitment(callerSecretKey(), requestId) == stored,
/// message)` — a FRESH witness against the pinned commitment.
fn assert_refund_commitment(
    c: &mut Circuit3,
    request_id: &signet::RequestId<Public>,
    stored: &RefundCommitment<Public>,
    message: &'static str,
) {
    let sk = common::witness_sk(c);
    let rid_priv = request_id.private();
    let mine = refund_commitment(c, &sk, &rid_priv);
    c.assert(b32_eq(&mine.bytes(), &stored.private().bytes()).message(message));
}

/// `mintShieldedToken(vaultTokenDomainSeparator(erc20), amount,
/// disclose(mintNonce), left(ownPublicKey()))` with the recipient's
/// `ownPublicKey()` witnessed FIRST (`const recipient = …` precedes the
/// call in every settle circuit that mints to the caller).
fn mint_to_own_key<R: minocrab::v3::DisclosureLabel>(
    c: &mut Circuit3,
    erc20: Wire3<FieldT, Public>,
    amount: Uint<64, Public>,
    mint_nonce: &CoinNonce<Public>,
) {
    let own_pk = own_public_key(c).disclose_as::<R>(c);
    let domain_sep = vault_token_domain_separator(c, erc20);
    common::mint_shielded_token_to_key(c, &domain_sep, amount, mint_nonce, &own_pk);
}

/// `numericAbiWord(unlimitedAllowance())` — 2^128 − 1 as an ABI word: 16
/// zero bytes then 16 `0xff` bytes.
fn unlimited_allowance_word(c: &mut Circuit3) -> B32<Private> {
    let mut max_word = [0u8; 32];
    max_word[16..].copy_from_slice(&[0xff; 16]);
    B32 {
        hi: c.constant(minocrab::Fr::from(u64::from(max_word[31]))).private(),
        lo: c
            .constant(minocrab::Fr::from_le_bytes(&max_word[..31]).unwrap())
            .private(),
    }
}

/// `struct DepositRequest { erc20Address: Bytes<20>, amount: Uint<128> }`.
#[derive(CircuitArg)]
struct DepositRequest {
    erc20_address: Bytes<20>,
    amount: Uint<128>,
}

/// `struct WithdrawRequest { erc20Address: Bytes<20>, amount: Uint<128>,
/// destEvmAddress: Bytes<20> }`.
#[derive(CircuitArg)]
struct WithdrawRequest {
    erc20_address: Bytes<20>,
    amount: Uint<128>,
    dest_evm_address: Bytes<20>,
}

/// `struct SwapRequest { tokenIn: Bytes<20>, tokenOut: Bytes<20>, fee:
/// Uint<24>, amountOut: Uint<128>, amountInMaximum: Uint<128> }`.
#[derive(CircuitArg)]
struct SwapRequest {
    token_in: Bytes<20>,
    token_out: Bytes<20>,
    fee: Uint<24>,
    amount_out: Uint<128>,
    amount_in_maximum: Uint<128>,
}

#[contract]
impl Vault {
    // ==== Initialisation and configuration ===============================================

    /// `export circuit initialise(vaultEvm: Bytes<20>, swapRouter: Bytes<20>,
    /// stataUnderlyingAddr: Bytes<20>, stataTokenAddr: Bytes<20>, chainId:
    /// Uint<64>, chainCaip2Id: Bytes<32>, responseKey: Secp256k1Point): []` —
    /// one-shot, deployer-gated post-deploy configuration.
    ///
    /// The parameters after `c` are the Compact parameter list, in declaration
    /// order — which is the wire contract.
    #[circuit]
    pub fn initialise(
        c: &mut Circuit3,
        vault_evm: Bytes<20>,
        swap_router: Bytes<20>,
        stata_underlying_addr: Bytes<20>,
        stata_token_addr: Bytes<20>,
        chain_id: Uint<64>,
        chain_caip2_id: common::Caip2Id<Private>,
        response_key: Secp256k1Point,
    ) -> Discloses<(
        VaultEvmAddress,
        UniswapRouter,
        StataUnderlying,
        StataToken,
        EvmChainId,
        Caip2Id,
        MpcResponseKey,
    )> {
        // assert(initialised == 0, "Already initialised")
        c.region("initialised gate", |c| {
            let count = VAULT.initialised.read(c);
            c.assert(count.eq(0u64).message("Already initialised"));
        });

        // assert(userCommitment(callerSecretKey()) == deployer, "Not the deployer")
        c.region("deployer gate", |c| {
            let sk = common::witness_sk(c);
            let mine = user_commitment(c, &sk);
            let stored = VAULT.deployer.read(c);
            c.assert(b32_eq(&mine.bytes(), &stored.private().bytes()).message("Not the deployer"));
        });

        c.assert(chain_id.gt(0u64).message("Chain ID must be positive"));
        c.assert(swap_router.ne(0u64).message("Router cannot be zero"));
        c.assert(stata_underlying_addr.ne(0u64).message("stataUnderlying cannot be zero"));
        c.assert(stata_token_addr.ne(0u64).message("stataToken cannot be zero"));

        // initialised.increment(1)
        VAULT.initialised.increment(c, 1);

        // The seven configuration writes, in source order.
        c.region("configuration writes", |c| {
            let vault_evm = vault_evm.disclose_as::<VaultEvmAddress>(c);
            VAULT.vault_evm_address.write(c, &vault_evm);
            let swap_router = swap_router.disclose_as::<UniswapRouter>(c);
            VAULT.uniswap_router.write(c, &swap_router);
            let stata_underlying = stata_underlying_addr.disclose_as::<StataUnderlying>(c);
            VAULT.stata_underlying.write(c, &stata_underlying);
            let stata_token = stata_token_addr.disclose_as::<StataToken>(c);
            VAULT.stata_token.write(c, &stata_token);
            let chain_id = chain_id.disclose_as::<EvmChainId>(c);
            VAULT.evm_chain_id.write(c, &chain_id);
            let caip2 = chain_caip2_id.disclose_as::<Caip2Id>(c);
            VAULT.caip2_id.write(c, &caip2);
            let response_key = response_key.disclose_as::<MpcResponseKey>(c);
            VAULT.mpc_response_key.write(c, &response_key);
        });

        Discloses::of(())
    }

    /// `export circuit approveStata(evmNonce: Uint<64>, keyVersion: Uint<8>): []`
    /// — one-time MPC-signed `approve(stataToken, unlimitedAllowance())` ON the
    /// underlying USDC, so the wrapper can pull it during a supply. Signed with
    /// the VAULT account; recorded in `signBidirectionalEventMap` (path `[0,0]`).
    #[circuit]
    pub fn approve_stata(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
    ) -> Discloses<(RequestId, RequestRecord, XcallEntryPointHash, XcallCommitment)> {
        // Kept even though guard threading no longer uses it: dropping this
        // `Copy` would renumber every later identifier, moving the ZKIR
        // (notes/edsl-trim.org §B, the removal's zero-movement gate).
        let _ = c.constant(1u64);
        assert_initialised(c);

        // approve(stataToken, 2^128−1): the spender is the wrapper.
        let stata_token = VAULT.stata_token.read(c).stale(c);
        let word0 = signet::evm_address_abi_word(c, stata_token.field().private());
        let word1 = unlimited_allowance_word(c);
        let calldata = calldata(c, &APPROVE_SELECTOR, [word0, word1]);

        // Contract-FIXED gas envelope; `to` is the underlying token (read where
        // the struct literal names it, after `chainId`).
        let gas = fixed_gas(c, ERC20_CALL_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let stata_underlying = VAULT.stata_underlying.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, stata_underlying.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: VaultEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            VAULT_RESPONSE_SCHEMA,
            VAULT_RESPONSE_SCHEMA,
        );
        record_and_notify(c, &request, &VAULT.sign_bidirectional_event_map);
        Discloses::of(())
    }

    /// `export circuit approveRouter(erc20Address: Bytes<20>, evmNonce:
    /// Uint<64>, keyVersion: Uint<8>): []` — permissionless per-token router
    /// allowance, signed with the VAULT account: spender and amount are
    /// contract-fixed, so the caller chooses ONLY the token.
    #[circuit]
    pub fn approve_router(
        c: &mut Circuit3,
        erc20_address: Bytes<20>,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
    ) -> Discloses<(ApprovedErc20, RequestId, RequestRecord, XcallEntryPointHash, XcallCommitment)> {
        // Kept even though guard threading no longer uses it: dropping this
        // `Copy` would renumber every later identifier, moving the ZKIR
        // (notes/edsl-trim.org §B, the removal's zero-movement gate).
        let _ = c.constant(1u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(erc20_address.ne(0u64).message("ERC20 address cannot be zero"));
        });

        // approve(uniswapRouter, 2^128−1): the spender is the pinned router.
        let router = VAULT.uniswap_router.read(c).stale(c);
        let word0 = signet::evm_address_abi_word(c, router.field().private());
        let word1 = unlimited_allowance_word(c);
        let calldata = calldata(c, &APPROVE_SELECTOR, [word0, word1]);

        // Contract-FIXED gas envelope; `to` is the (disclosed) ERC20 itself.
        let gas = fixed_gas(c, ERC20_CALL_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let erc20 = erc20_address.disclose_as::<ApprovedErc20>(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, erc20.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: VaultEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            VAULT_RESPONSE_SCHEMA,
            VAULT_RESPONSE_SCHEMA,
        );
        record_and_notify(c, &request, &VAULT.sign_bidirectional_event_map);
        Discloses::of(())
    }

    // ==== Deposit ========================================================================

    /// `export circuit startDeposit(evmNonce: Uint<64>, gasLimit: Uint<64>,
    /// maxFeePerGas: Uint<128>, maxPriorityFeePerGas: Uint<128>, keyVersion:
    /// Uint<8>, depositRequest: DepositRequest): []` — records
    /// `transfer(vaultEvmAddress, amount)` on the ERC20, signed by the MPC with
    /// the CALLER's derived account (the path is the caller's commitment), and
    /// pins the settle view `completeDeposit` mints from.
    #[circuit]
    pub fn start_deposit(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        gas_limit: Uint<64>,
        max_fee_per_gas: Uint<128>,
        max_priority_fee_per_gas: Uint<128>,
        key_version: Uint<8>,
        deposit_request: DepositRequest,
    ) -> Discloses<(
        DepositorCommitment,
        RequestId,
        RequestRecord,
        DepositedErc20,
        DepositedAmount,
        XcallEntryPointHash,
        XcallCommitment,
    )> {
        // Kept even though guard threading no longer uses it: dropping this
        // `Copy` would renumber every later identifier, moving the ZKIR
        // (notes/edsl-trim.org §B, the removal's zero-movement gate).
        let _ = c.constant(1u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(deposit_request.erc20_address.ne(0u64).message("ERC20 address cannot be zero"));
            c.assert(deposit_request.amount.gt(0u64).message("Amount must be positive"));
            // completeDeposit mints via a Uint<64> API, so reject unclaimable amounts.
            c.assert(deposit_request.amount.le(u64::MAX).message("Amount exceeds Uint<64> max"));
            c.assert(gas_limit.gt(0u64).message("Gas limit must be positive"));
        });

        // const caller = disclose(userCommitment(callerSecretKey()))
        let sk = common::witness_sk(c);
        let caller = user_commitment(c, &sk).disclose_as::<DepositorCommitment>(c);

        // The pinned recipient stops a client having the MPC sign a transfer to
        // themselves: transfer(vaultEvmAddress, amount).
        let vault_evm = VAULT.vault_evm_address.read(c).stale(c);
        let word0 = signet::evm_address_abi_word(c, vault_evm.field().private());
        let word1 = signet::numeric_abi_word(c, deposit_request.amount.field());
        let calldata = calldata(c, &TRANSFER_SELECTOR, [word0, word1]);

        // The depositor's own gas envelope (their account pays).
        let gas = [
            max_priority_fee_per_gas.field(),
            max_fee_per_gas.field(),
            gas_limit.field(),
        ];
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, deposit_request.erc20_address.field(), calldata);

        let request: VaultEvent<Private> = assemble_request(
            c,
            key_version.field(),
            common::SigningPath::from(caller.private()),
            tx,
            VAULT_RESPONSE_SCHEMA,
            VAULT_RESPONSE_SCHEMA,
        );

        let request_id = check_fresh_request(c, &request, &VAULT.deposit_event_map);
        insert_request(c, &request, &VAULT.deposit_event_map, &request_id);

        // depositSettleViews.insert(requestId, { commitment: caller, erc20:
        //   disclose(erc20Address), amount: disclose(amount as Uint<64>) })
        let erc20 = deposit_request.erc20_address.disclose_as::<DepositedErc20>(c);
        let amount = deposit_request.amount.field().disclose_as::<DepositedAmount>(c);
        let view = DepositSettleView {
            commitment: caller,
            erc20,
            amount: Uint::<64, Public>::from_field_checked(c, amount),
        };
        VAULT.deposit_settle_views.insert(c, &request_id, &view);

        notify_signet(c, &request_id, &VAULT.deposit_event_map);
        Discloses::of(())
    }

    /// `export circuit completeDeposit(requestId: RequestId,
    /// respondBidirectionalEvent: RespondBidirectionalEvent, serializedOutput:
    /// Bytes<1>, mintNonce: Bytes<32>, recipient: Maybe<Either<ZswapCoinPublicKey,
    /// ContractAddress>>): []` — settles a successful deposit: mints shielded
    /// vault tokens for the deposited amount. Depositor-gated, one settle per
    /// request.
    #[circuit]
    pub fn complete_deposit(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<1>,
        mint_nonce: CoinNonce<Private>,
        recipient: Maybe<
            Either<
                minocrab_std::v3::ZswapCoinPublicKey<Private>,
                minocrab_std::v3::ContractAddress<Private>,
                Private,
            >,
        >,
    ) -> Discloses<(
        ClaimRequestId,
        ClaimRecipientTag,
        ClaimRecipientSide,
        ClaimRecipientOwnKey,
        ClaimRecipientKey,
        ClaimRecipientContract,
        ClaimMintNonce,
    )> {
        let one = c.constant(1u64);
        let output = serialized_output.field();

        // const disclosedRequestId = disclose(requestId)
        let request_id = request_id.disclose_as::<ClaimRequestId>(c);
        assert_initialised(c);

        // assert(deserialize<VaultResponse, 1>(serializedOutput).success)
        let success = attested_success(c, output);
        c.assert_with(success, Some("ERC20 transfer returned false"));

        assert_attestation::<1>(c, &request_id, &respond_bidirectional_event, &[output]);

        // Double-settle protection, then the view.
        let view = c.region("event map consume", |c| {
            let found = VAULT.deposit_event_map.member(c, &request_id);
            c.assert(is_true(found).message("Deposit not found"));
            VAULT.deposit_event_map.remove(c, &request_id);
            VAULT.deposit_settle_views.lookup(c, &request_id)
        });

        // assert(userCommitment(callerSecretKey()) == view.commitment, "Not the depositor")
        c.region("depositor gate", |c| {
            let sk = common::witness_sk(c);
            let mine = user_commitment(c, &sk);
            c.assert(
                b32_eq(&mine.bytes(), &view.commitment.private().bytes()).message("Not the depositor"),
            );
        });
        VAULT.deposit_settle_views.remove(c, &request_id);

        // const claimRecipient = disclose(recipient).is_some
        //   ? disclose(recipient).value : left(ownPublicKey())
        let recipient = c.region("recipient select", |c| {
            let rec_is_some = recipient.is_some.field().disclose_as::<ClaimRecipientTag>(c);
            let rec_is_left = recipient.value.is_left.field().disclose_as::<ClaimRecipientSide>(c);
            let not_some = c.not(rec_is_some);
            let own_pk = c
                .when(not_some, own_public_key)
                .or_default()
                .disclose_as::<ClaimRecipientOwnKey>(c);
            let rec_left = recipient.value.left.disclose_as::<ClaimRecipientKey>(c);
            let rec_right = recipient.value.right.disclose_as::<ClaimRecipientContract>(c);
            let is_left = c.cond_select(rec_is_some, rec_is_left, one);
            let left = minocrab_std::v3::ZswapCoinPublicKey(B32 {
                hi: c.cond_select(rec_is_some, rec_left.bytes().hi, own_pk.bytes().hi),
                lo: c.cond_select(rec_is_some, rec_left.bytes().lo, own_pk.bytes().lo),
            });
            let right = minocrab_std::v3::ContractAddress(B32 {
                hi: c.cond_select(rec_is_some, rec_right.bytes().hi, 0u64),
                lo: c.cond_select(rec_is_some, rec_right.bytes().lo, 0u64),
            });
            CoinRecipient { is_left, left, right }
        });

        // mintShieldedToken(vaultTokenDomainSeparator(view.erc20), view.amount,
        //   disclose(mintNonce), claimRecipient)
        let domain_sep = vault_token_domain_separator(c, view.erc20.field());
        let mint_nonce = mint_nonce.disclose_as::<ClaimMintNonce>(c);
        common::mint_shielded_token(c, &domain_sep, view.amount, &mint_nonce, &recipient);
        Discloses::of(())
    }

    // ==== Withdraw =======================================================================

    /// `export circuit startWithdraw(evmNonce: Uint<64>, keyVersion: Uint<8>,
    /// withdrawRequest: WithdrawRequest, coin: ShieldedCoinInfo): []` — burns
    /// the surrendered vault coin up front and records
    /// `transfer(destEvmAddress, amount)`, signed with the VAULT's own account
    /// under a contract-fixed gas envelope; pins the withdrawer's refund
    /// commitment in the settle view.
    #[circuit]
    pub fn start_withdraw(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
        withdraw_request: WithdrawRequest,
        coin: ShieldedCoinArg,
    ) -> Discloses<(
        WithdrawnErc20,
        RequestId,
        SurrenderedCoinNonce,
        SurrenderedCoinColor,
        SurrenderedCoinValue,
        RequestRecord,
        WithdrawerRefundCommitment,
        WithdrawnAmount,
        XcallEntryPointHash,
        XcallCommitment,
    )> {
        let one = c.constant(1u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(withdraw_request.erc20_address.ne(0u64).message("ERC20 address cannot be zero"));
            c.assert(withdraw_request.amount.gt(0u64).message("Amount must be positive"));
            // refundWithdraw re-mints via a Uint<64> API.
            c.assert(withdraw_request.amount.le(u64::MAX).message("Amount exceeds Uint<64> max"));
        });

        let erc20 = withdraw_request.erc20_address.disclose_as::<WithdrawnErc20>(c);
        let amount = withdraw_request.amount.field();
        assert_vault_coin(
            c,
            erc20.field(),
            amount,
            &coin,
            "Coin is not the vault token for this ERC20",
            "Coin value must equal the withdraw amount",
        );

        // transfer(destEvmAddress, amount), signed by the VAULT account.
        let word0 = signet::evm_address_abi_word(c, withdraw_request.dest_evm_address.field());
        let word1 = signet::numeric_abi_word(c, amount);
        let calldata = calldata(c, &TRANSFER_SELECTOR, [word0, word1]);
        let gas = fixed_gas(c, ERC20_CALL_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, erc20.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: VaultEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            VAULT_RESPONSE_SCHEMA,
            VAULT_RESPONSE_SCHEMA,
        );
        let request_id = check_fresh_request(c, &request, &VAULT.sign_bidirectional_event_map);

        burn_surrendered_coin(c, one, coin);

        insert_request(c, &request, &VAULT.sign_bidirectional_event_map, &request_id);

        // withdrawSettleViews.insert(requestId, { commitment:
        //   disclose(refundCommitment(callerSecretKey(), requestId)), erc20, amount })
        let sk = common::witness_sk(c);
        let rid_priv = request_id.private();
        let commitment =
            refund_commitment(c, &sk, &rid_priv).disclose_as::<WithdrawerRefundCommitment>(c);
        let amount = amount.disclose_as::<WithdrawnAmount>(c);
        let view = WithdrawSettleView {
            commitment,
            erc20,
            amount: Uint::<64, Public>::from_field_checked(c, amount),
        };
        VAULT.withdraw_settle_views.insert(c, &request_id, &view);

        notify_signet(c, &request_id, &VAULT.sign_bidirectional_event_map);
        Discloses::of(())
    }

    /// `export circuit completeWithdraw(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<1>, mintNonce): []` — settles an EXECUTED
    /// withdrawal in both branches, decided by the attested 1-byte bool: on
    /// success only cleanup (anyone may settle it), on a `false` return a
    /// withdrawer-only re-mint.
    #[circuit]
    pub fn complete_withdraw(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<1>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, WithdrawalOutcome, RefundMintNonce, RefundRecipient)> {
        let output = serialized_output.field();
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_initialised(c);
        assert_attestation::<1>(c, &request_id, &respond_bidirectional_event, &[output]);

        // Deposits never insert withdrawSettleViews, so a deposit cannot be
        // settled here.
        let view = c.region("event map consume", |c| {
            let pending = VAULT.withdraw_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Withdrawal not found"));
            let view = VAULT.withdraw_settle_views.lookup(c, &request_id);
            VAULT.sign_bidirectional_event_map.remove(c, &request_id);
            view
        });

        // const succeeded = disclose(deserialize<VaultResponse, 1>(output).success)
        let succeeded = attested_success(c, output).disclose_as::<WithdrawalOutcome>(c);

        // Hoisted out of the `if` as in the source: the witness is consumed
        // unconditionally, the hash computed once.
        let my_commitment = {
            let sk = common::witness_sk(c);
            let rid_priv = request_id.private();
            refund_commitment(c, &sk, &rid_priv)
        };
        let domain_sep = vault_token_domain_separator(c, view.erc20.field());

        // The transfer can fail by the ERC20 returning false even when the
        // transaction succeeds: if (!succeeded) { withdrawer-only re-mint }.
        let refunding = c.not(succeeded);
        let mint_nonce = mint_nonce.disclose_as::<RefundMintNonce>(c);
        c.when(refunding, |c| {
            c.assert(
                b32_eq(&my_commitment.bytes(), &view.commitment.private().bytes())
                    .message("Not the withdrawer"),
            );
            let own_pk = own_public_key(c).disclose_as::<RefundRecipient>(c);
            common::mint_shielded_token_to_key(c, &domain_sep, view.amount, &mint_nonce, &own_pk);
        });

        VAULT.withdraw_settle_views.remove(c, &request_id);
        Discloses::of(())
    }

    /// `export circuit refundWithdraw(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<5>, mintNonce): []` — withdrawer-only re-mint of
    /// the surrendered amount when the transfer never executed.
    #[circuit]
    pub fn refund_withdraw(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<5>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, RefundMintNonce, RefundRecipient)> {
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_attested_failure_output(c, &request_id, &respond_bidirectional_event, serialized_output.field());

        let view = c.region("settle view", |c| {
            let pending = VAULT.withdraw_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Withdrawal not found"));
            VAULT.withdraw_settle_views.lookup(c, &request_id)
        });
        assert_refund_commitment(c, &request_id, &view.commitment, "Not the withdrawer");
        VAULT.sign_bidirectional_event_map.remove(c, &request_id);
        VAULT.withdraw_settle_views.remove(c, &request_id);

        let mint_nonce = mint_nonce.disclose_as::<RefundMintNonce>(c);
        mint_to_own_key::<RefundRecipient>(c, view.erc20.field(), view.amount, &mint_nonce);
        Discloses::of(())
    }

    // ==== Swap (Uniswap V3) ==============================================================

    /// `export circuit startSwap(evmNonce: Uint<64>, keyVersion: Uint<8>,
    /// swapRequest: SwapRequest, coin: ShieldedCoinInfo): []` — burns the
    /// surrendered `amountInMaximum` of tokenIn and records `exactOutputSingle`
    /// on the pinned router, signed with the VAULT's account.
    #[circuit]
    pub fn start_swap(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
        swap_request: SwapRequest,
        coin: ShieldedCoinArg,
    ) -> Discloses<(
        SoldErc20,
        BoughtErc20,
        RequestId,
        SurrenderedCoinNonce,
        SurrenderedCoinColor,
        SurrenderedCoinValue,
        RequestRecord,
        SwapperRefundCommitment,
        SwapAmountOut,
        SwapAmountInMaximum,
        XcallEntryPointHash,
        XcallCommitment,
    )> {
        let one = c.constant(1u64);
        let zero = c.constant(0u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(swap_request.token_in.ne(0u64).message("tokenIn cannot be zero"));
            c.assert(swap_request.token_out.ne(0u64).message("tokenOut cannot be zero"));
            c.assert(swap_request.amount_out.gt(0u64).message("amountOut must be positive"));
            c.assert(swap_request.amount_in_maximum.gt(0u64).message("amountInMaximum must be positive"));
            // Every later mint uses the Uint<64> mint API, so bound both here,
            // BEFORE the burn.
            c.assert(swap_request.amount_out.le(u64::MAX).message("amountOut exceeds Uint<64> max"));
            c.assert(swap_request.amount_in_maximum.le(u64::MAX).message("amountInMaximum exceeds Uint<64> max"));
        });

        let amount_out = swap_request.amount_out.field();
        let amount_in_max = swap_request.amount_in_maximum.field();
        let token_in = swap_request.token_in.disclose_as::<SoldErc20>(c);
        assert_vault_coin(
            c,
            token_in.field(),
            amount_in_max,
            &coin,
            "Coin is not the vault token for tokenIn",
            "Coin value must equal amountInMaximum",
        );

        // exactOutputSingle((tokenIn, tokenOut, fee, vault, amountOut,
        // amountInMaximum, 0)): recipient is the vault EVM address so bought
        // tokens return to the pool.
        let token_out = swap_request.token_out.disclose_as::<BoughtErc20>(c);
        let word0 = signet::evm_address_abi_word(c, token_in.field().private());
        let word1 = signet::evm_address_abi_word(c, token_out.field().private());
        let word2 = signet::numeric_abi_word(c, swap_request.fee.field());
        let vault_evm = VAULT.vault_evm_address.read(c).stale(c);
        let word3 = signet::evm_address_abi_word(c, vault_evm.field().private());
        let word4 = signet::numeric_abi_word(c, amount_out);
        let word5 = signet::numeric_abi_word(c, amount_in_max);
        let word6 = B32::<Private> {
            hi: zero.private(),
            lo: zero.private(),
        };
        let calldata = calldata(
            c,
            &EXACT_OUTPUT_SINGLE_SELECTOR,
            [word0, word1, word2, word3, word4, word5, word6],
        );

        // Contract-FIXED gas envelope; to = the pinned router.
        let gas = fixed_gas(c, SWAP_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let router = VAULT.uniswap_router.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, router.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: SwapEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            SWAP_OUTPUT_SCHEMA,
            SWAP_RESPOND_SCHEMA,
        );
        let request_id = check_fresh_request(c, &request, &VAULT.swap_event_map);

        burn_surrendered_coin(c, one, coin);

        insert_request(c, &request, &VAULT.swap_event_map, &request_id);

        let sk = common::witness_sk(c);
        let rid_priv = request_id.private();
        let commitment = refund_commitment(c, &sk, &rid_priv).disclose_as::<SwapperRefundCommitment>(c);
        let amount_out = amount_out.disclose_as::<SwapAmountOut>(c);
        let amount_in_max = amount_in_max.disclose_as::<SwapAmountInMaximum>(c);
        let view = SwapSettleView {
            commitment,
            token_in,
            token_out,
            amount_out: Uint::<64, Public>::from_field_checked(c, amount_out),
            amount_in_maximum: Uint::<64, Public>::from_field_checked(c, amount_in_max),
        };
        VAULT.swap_settle_views.insert(c, &request_id, &view);

        notify_signet(c, &request_id, &VAULT.swap_event_map);
        Discloses::of(())
    }

    /// `export circuit completeSwap(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<8>, mintNonce, changeNonce): []` — settles a
    /// SUCCESSFUL swap: mints the exact amountOut of tokenOut plus the unspent
    /// tokenIn as change. Swapper-gated, one settle per request.
    #[circuit]
    pub fn complete_swap(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<8>,
        mint_nonce: CoinNonce<Private>,
        change_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, SwapRecipient, SwapMintNonce, AttestedAmountIn, SwapChangeNonce)> {
        let output = serialized_output.field();
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_initialised(c);
        // The two mints need distinct nonces or their coins link.
        c.assert(
            not(b32_eq(&change_nonce.bytes(), &mint_nonce.bytes()))
                .message("changeNonce must differ from mintNonce"),
        );
        assert_attestation::<8>(c, &request_id, &respond_bidirectional_event, &[output]);

        let view = c.region("event map consume", |c| {
            let pending = VAULT.swap_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Swap not found"));
            let view = VAULT.swap_settle_views.lookup(c, &request_id);
            VAULT.swap_event_map.remove(c, &request_id);
            view
        });
        assert_refund_commitment(c, &request_id, &view.commitment, "Not the swapper");
        VAULT.swap_settle_views.remove(c, &request_id);

        // const recipient = left(ownPublicKey())
        let recipient = own_public_key(c).disclose_as::<SwapRecipient>(c);

        // Mint the EXACT amountOut of tokenOut.
        let ds_out = vault_token_domain_separator(c, view.token_out.field());
        let mint_nonce = mint_nonce.disclose_as::<SwapMintNonce>(c);
        common::mint_shielded_token_to_key(c, &ds_out, view.amount_out, &mint_nonce, &recipient);

        // change <= amountInMaximum, so it fits Uint<64>; an exact spend mints
        // a 0-value coin. `sub` emits the underflow guard — the most dangerous
        // arithmetic in the contract.
        let amount_in = output.disclose_as::<AttestedAmountIn>(c);
        let change = view
            .amount_in_maximum
            .sub_with(c, Uint::<64, Public>::from_field_unchecked(amount_in), "Attested amountIn exceeds amountInMaximum");
        let ds_in = vault_token_domain_separator(c, view.token_in.field());
        let change_nonce = change_nonce.disclose_as::<SwapChangeNonce>(c);
        common::mint_shielded_token_to_key(c, &ds_in, change, &change_nonce, &recipient);
        Discloses::of(())
    }

    /// `export circuit refundSwap(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<5>, mintNonce): []` — swapper-only re-mint of the
    /// full amountInMaximum when the swap never executed.
    #[circuit]
    pub fn refund_swap(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<5>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, RefundMintNonce, RefundRecipient)> {
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_attested_failure_output(c, &request_id, &respond_bidirectional_event, serialized_output.field());

        let view = c.region("settle view", |c| {
            let pending = VAULT.swap_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Swap not found"));
            VAULT.swap_settle_views.lookup(c, &request_id)
        });
        assert_refund_commitment(c, &request_id, &view.commitment, "Not the swapper");
        VAULT.swap_event_map.remove(c, &request_id);
        VAULT.swap_settle_views.remove(c, &request_id);

        let mint_nonce = mint_nonce.disclose_as::<RefundMintNonce>(c);
        mint_to_own_key::<RefundRecipient>(c, view.token_in.field(), view.amount_in_maximum, &mint_nonce);
        Discloses::of(())
    }

    // ==== Supply (Aave, via the stataUSDC wrapper) =======================================

    /// `export circuit startSupply(evmNonce: Uint<64>, keyVersion: Uint<8>,
    /// amount: Uint<128>, coin: ShieldedCoinInfo): []` — burns the surrendered
    /// USDC vault coin and records `stataToken.deposit(amount, vault)`, signed
    /// by the VAULT account (exact-input, so no change).
    #[circuit]
    pub fn start_supply(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
        amount: Uint<128>,
        coin: ShieldedCoinArg,
    ) -> Discloses<(
        RequestId,
        SurrenderedCoinNonce,
        SurrenderedCoinColor,
        SurrenderedCoinValue,
        RequestRecord,
        SupplierRefundCommitment,
        SuppliedAmount,
        XcallEntryPointHash,
        XcallCommitment,
    )> {
        let one = c.constant(1u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(amount.gt(0u64).message("amount must be positive"));
            // refundSupply re-mints via the Uint<64> mint API.
            c.assert(amount.le(u64::MAX).message("amount exceeds Uint<64> max"));
        });

        let amount = amount.field();
        let stata_underlying = VAULT.stata_underlying.read(c);
        assert_vault_coin(
            c,
            stata_underlying.field(),
            amount,
            &coin,
            "Coin is not the vault token for the underlying",
            "Coin value must equal amount",
        );

        // deposit(amount, vaultEvmAddress) on the wrapper.
        let word0 = signet::numeric_abi_word(c, amount);
        let vault_evm = VAULT.vault_evm_address.read(c).stale(c);
        let word1 = signet::evm_address_abi_word(c, vault_evm.field().private());
        let calldata = calldata(c, &DEPOSIT_SELECTOR, [word0, word1]);
        let gas = fixed_gas(c, LENDING_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let stata_token = VAULT.stata_token.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, stata_token.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: SupplyEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            SUPPLY_OUTPUT_SCHEMA,
            SUPPLY_RESPOND_SCHEMA,
        );
        let request_id = check_fresh_request(c, &request, &VAULT.supply_event_map);

        burn_surrendered_coin(c, one, coin);

        insert_request(c, &request, &VAULT.supply_event_map, &request_id);

        let sk = common::witness_sk(c);
        let rid_priv = request_id.private();
        let commitment = refund_commitment(c, &sk, &rid_priv).disclose_as::<SupplierRefundCommitment>(c);
        let amount = amount.disclose_as::<SuppliedAmount>(c);
        let view = SupplySettleView {
            commitment,
            amount: Uint::<64, Public>::from_field_checked(c, amount),
        };
        VAULT.supply_settle_views.insert(c, &request_id, &view);

        notify_signet(c, &request_id, &VAULT.supply_event_map);
        Discloses::of(())
    }

    /// `export circuit completeSupply(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<8>, mintNonce): []` — settles a successful
    /// supply: mints shielded(stataToken) for the attested shares.
    /// Supplier-gated, one settle per request.
    #[circuit]
    pub fn complete_supply(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<8>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, AttestedShares, SupplyRecipient, SupplyMintNonce)> {
        let output = serialized_output.field();
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_initialised(c);
        assert_attestation::<8>(c, &request_id, &respond_bidirectional_event, &[output]);

        c.region("event map consume", |c| {
            let found = VAULT.supply_event_map.member(c, &request_id);
            c.assert(is_true(found).message("Supply not found"));
            VAULT.supply_event_map.remove(c, &request_id);
        });
        // assert(refundCommitment(callerSecretKey(), requestId)
        //   == supplySettleViews.lookup(requestId).commitment, "Not the supplier")
        c.region("supplier gate", |c| {
            let sk = common::witness_sk(c);
            let rid_priv = request_id.private();
            let mine = refund_commitment(c, &sk, &rid_priv);
            let view = VAULT.supply_settle_views.lookup(c, &request_id);
            c.assert(
                b32_eq(&mine.bytes(), &view.commitment.private().bytes()).message("Not the supplier"),
            );
        });
        VAULT.supply_settle_views.remove(c, &request_id);

        // const shares = disclose(deserialize<DepositReturnValue, 8>(output).shares)
        let shares = Uint::<64, Public>::from_field_unchecked(output.disclose_as::<AttestedShares>(c));
        let recipient = own_public_key(c).disclose_as::<SupplyRecipient>(c);
        let stata_token = VAULT.stata_token.read(c);
        let domain_sep = vault_token_domain_separator(c, stata_token.field());
        let mint_nonce = mint_nonce.disclose_as::<SupplyMintNonce>(c);
        common::mint_shielded_token_to_key(c, &domain_sep, shares, &mint_nonce, &recipient);
        Discloses::of(())
    }

    /// `export circuit refundSupply(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<5>, mintNonce): []` — supplier-only re-mint of
    /// the surrendered amount when the deposit never executed.
    #[circuit]
    pub fn refund_supply(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<5>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, RefundMintNonce, RefundRecipient)> {
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_attested_failure_output(c, &request_id, &respond_bidirectional_event, serialized_output.field());

        let view = c.region("settle view", |c| {
            let pending = VAULT.supply_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Supply not found"));
            VAULT.supply_settle_views.lookup(c, &request_id)
        });
        assert_refund_commitment(c, &request_id, &view.commitment, "Not the supplier");
        VAULT.supply_event_map.remove(c, &request_id);
        VAULT.supply_settle_views.remove(c, &request_id);

        let mint_nonce = mint_nonce.disclose_as::<RefundMintNonce>(c);
        let own_pk = own_public_key(c).disclose_as::<RefundRecipient>(c);
        let stata_underlying = VAULT.stata_underlying.read(c);
        let domain_sep = vault_token_domain_separator(c, stata_underlying.field());
        common::mint_shielded_token_to_key(c, &domain_sep, view.amount, &mint_nonce, &own_pk);
        Discloses::of(())
    }

    // ==== Redeem (Aave, via the stataUSDC wrapper) =======================================

    /// `export circuit startRedeem(evmNonce: Uint<64>, keyVersion: Uint<8>,
    /// shares: Uint<128>, coin: ShieldedCoinInfo): []` — burns the surrendered
    /// stataToken vault coin and records `stataToken.redeem(shares, vault,
    /// vault)`, signed by the VAULT account.
    ///
    /// CAUTION (upstream's): the bound is on `shares`, not the assets that come
    /// back — Aave's exchange rate only grows, and `completeRedeem` mints
    /// assets through the same `Uint<64>` API after the coin is already burned.
    #[circuit]
    pub fn start_redeem(
        c: &mut Circuit3,
        evm_nonce: Uint<64>,
        key_version: Uint<8>,
        shares: Uint<128>,
        coin: ShieldedCoinArg,
    ) -> Discloses<(
        RequestId,
        SurrenderedCoinNonce,
        SurrenderedCoinColor,
        SurrenderedCoinValue,
        RequestRecord,
        RedeemerRefundCommitment,
        RedeemedShares,
        XcallEntryPointHash,
        XcallCommitment,
    )> {
        let one = c.constant(1u64);
        c.region("guards", |c| {
            assert_initialised(c);
            c.assert(shares.gt(0u64).message("shares must be positive"));
            c.assert(shares.le(u64::MAX).message("shares exceeds Uint<64> max"));
        });

        let shares = shares.field();
        let stata_token = VAULT.stata_token.read(c);
        assert_vault_coin(
            c,
            stata_token.field(),
            shares,
            &coin,
            "Coin is not the vault token for the wrapper",
            "Coin value must equal shares",
        );

        // redeem(shares, vaultEvmAddress, vaultEvmAddress) — the cell is read
        // once per word, as the source spells it.
        let word0 = signet::numeric_abi_word(c, shares);
        let vault_evm = VAULT.vault_evm_address.read(c).stale(c);
        let word1 = signet::evm_address_abi_word(c, vault_evm.field().private());
        let vault_evm = VAULT.vault_evm_address.read(c).stale(c);
        let word2 = signet::evm_address_abi_word(c, vault_evm.field().private());
        let calldata = calldata(c, &REDEEM_SELECTOR, [word0, word1, word2]);
        let gas = fixed_gas(c, LENDING_GAS);
        let chain_id = VAULT.evm_chain_id.read(c).stale(c);
        let stata_token = VAULT.stata_token.read(c).stale(c);
        let tx = tx_params(c, chain_id, evm_nonce.field(), gas, stata_token.field().private(), calldata);

        let path = common::SigningPath::vault_path(c).private();
        let request: RedeemEvent<Private> = assemble_request(
            c,
            key_version.field(),
            path,
            tx,
            REDEEM_OUTPUT_SCHEMA,
            REDEEM_RESPOND_SCHEMA,
        );
        let request_id = check_fresh_request(c, &request, &VAULT.redeem_event_map);

        burn_surrendered_coin(c, one, coin);

        insert_request(c, &request, &VAULT.redeem_event_map, &request_id);

        let sk = common::witness_sk(c);
        let rid_priv = request_id.private();
        let commitment = refund_commitment(c, &sk, &rid_priv).disclose_as::<RedeemerRefundCommitment>(c);
        let shares = shares.disclose_as::<RedeemedShares>(c);
        let view = RedeemSettleView {
            commitment,
            shares: Uint::<64, Public>::from_field_checked(c, shares),
        };
        VAULT.redeem_settle_views.insert(c, &request_id, &view);

        notify_signet(c, &request_id, &VAULT.redeem_event_map);
        Discloses::of(())
    }

    /// `export circuit completeRedeem(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<8>, mintNonce): []` — settles a successful
    /// redeem: mints shielded(stataUnderlying) for the attested assets
    /// (principal + accrued interest). Redeemer-gated, one settle per request.
    #[circuit]
    pub fn complete_redeem(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<8>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, AttestedAssets, RedeemRecipient, RedeemMintNonce)> {
        let output = serialized_output.field();
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_initialised(c);
        assert_attestation::<8>(c, &request_id, &respond_bidirectional_event, &[output]);

        c.region("event map consume", |c| {
            let found = VAULT.redeem_event_map.member(c, &request_id);
            c.assert(is_true(found).message("Redeem not found"));
            VAULT.redeem_event_map.remove(c, &request_id);
        });
        c.region("redeemer gate", |c| {
            let sk = common::witness_sk(c);
            let rid_priv = request_id.private();
            let mine = refund_commitment(c, &sk, &rid_priv);
            let view = VAULT.redeem_settle_views.lookup(c, &request_id);
            c.assert(
                b32_eq(&mine.bytes(), &view.commitment.private().bytes()).message("Not the redeemer"),
            );
        });
        VAULT.redeem_settle_views.remove(c, &request_id);

        // const assets = disclose(deserialize<RedeemReturnValue, 8>(output).assets)
        let assets = Uint::<64, Public>::from_field_unchecked(output.disclose_as::<AttestedAssets>(c));
        let recipient = own_public_key(c).disclose_as::<RedeemRecipient>(c);
        let stata_underlying = VAULT.stata_underlying.read(c);
        let domain_sep = vault_token_domain_separator(c, stata_underlying.field());
        let mint_nonce = mint_nonce.disclose_as::<RedeemMintNonce>(c);
        common::mint_shielded_token_to_key(c, &domain_sep, assets, &mint_nonce, &recipient);
        Discloses::of(())
    }

    /// `export circuit refundRedeem(requestId, respondBidirectionalEvent,
    /// serializedOutput: Bytes<5>, mintNonce): []` — redeemer-only re-mint of
    /// the surrendered shares when the redeem never executed.
    #[circuit]
    pub fn refund_redeem(
        c: &mut Circuit3,
        request_id: signet::RequestId<Private>,
        #[arg(name = "respond")] respond_bidirectional_event: RespondSignature,
        serialized_output: Bytes<5>,
        mint_nonce: CoinNonce<Private>,
    ) -> Discloses<(SettleRequestId, RefundMintNonce, RefundRecipient)> {
        let request_id = request_id.disclose_as::<SettleRequestId>(c);
        assert_attested_failure_output(c, &request_id, &respond_bidirectional_event, serialized_output.field());

        let view = c.region("settle view", |c| {
            let pending = VAULT.redeem_settle_views.member(c, &request_id);
            c.assert(is_true(pending).message("Redeem not found"));
            VAULT.redeem_settle_views.lookup(c, &request_id)
        });
        assert_refund_commitment(c, &request_id, &view.commitment, "Not the redeemer");
        VAULT.redeem_event_map.remove(c, &request_id);
        VAULT.redeem_settle_views.remove(c, &request_id);

        let mint_nonce = mint_nonce.disclose_as::<RefundMintNonce>(c);
        let own_pk = own_public_key(c).disclose_as::<RefundRecipient>(c);
        let stata_token = VAULT.stata_token.read(c);
        let domain_sep = vault_token_domain_separator(c, stata_token.field());
        common::mint_shielded_token_to_key(c, &domain_sep, view.shares, &mint_nonce, &own_pk);
        Discloses::of(())
    }
}
