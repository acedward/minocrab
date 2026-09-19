//! `manager.compact` (acedward/AA-midnight-evm-experiment-v3) — an
//! account-abstraction custody contract: dual-mode authorization (a Midnight
//! witness secret, or an Ethereum EOA signing EIP-712), family-separated
//! shielded/unshielded custody, and ONE write gateway (`execute`) whose
//! `selector` picks among seven actions. Pinned in `corpus/sources.json`;
//! the compiled artifacts live under
//! `corpus/zkir/aa-midnight-evm-experiment/contracts/manager/`.
//!
//! THE PORT IS SEMANTIC, NOT INSTRUCTION-MIRRORING: the ledger-op stream —
//! the PI contract — reproduces compactc's exactly (read off the vm-code in
//! the compiled `contract/index.js`, function by function), while the
//! in-circuit arithmetic uses this workspace's own lowerings: the keccak
//! chip's in-chip byte packing where compactc splices `Bytes<N>` values byte
//! by byte, `div_mod` shifts for the big-endian ABI words where compactc
//! reverses byte vectors, and shared std gadgets (`send_shielded`,
//! `merge_coin_immediate`, the claims) that M17 proved equal to compactc's
//! stdlib instruction for instruction. Equivalence criterion is M3's:
//! same typed I/O schema + equal `pis`/`pi_skips` on a shared
//! `ProofPreimage` (tests/manager_differential.rs).
//!
//! Ledger block (declaration order = field index):
//! ```text
//! export ledger pools:              Map<Bytes<32>, QualifiedShieldedCoinInfo>;  // 0
//! export ledger accounts:           Set<Bytes<32>>;                             // 1
//! export ledger shieldedBalances:   Map<Bytes<32>, Uint<128>>;                  // 2
//! export ledger unshieldedBalances: Map<Bytes<32>, Uint<128>>;                  // 3
//! export ledger accountModes:       Map<Bytes<32>, Uint<8>>;                    // 4
//! export ledger evmOwners:          Map<Bytes<32>, Bytes<20>>;                  // 5
//! export ledger evmNonces:          Map<Bytes<32>, Uint<64>>;                   // 6
//! export ledger deploymentDomain:   Bytes<32>;                                  // 7
//! witness localOwnerSecret(): Bytes<32>;
//! ```
//!
//! Of the contract's 22 exported circuits only NINE read ledger state and
//! are provable (emit `.zkir`): `execute`, `depositShielded`,
//! `depositUnshielded`, `isRegistered`, `accountRecord`,
//! `shieldedAccountBalance`, `unshieldedAccountBalance`, `poolValue`,
//! `poolHasColour`. The pure exports (the EIP-712 codec oracles, the zswap
//! transcriptions, the semantic commitment) emit no artifact and are ported
//! only where a provable circuit calls them.

use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::{Alignment, AlignmentAtom, AlignmentSegment, Fr, Private, Public};
use minocrab_std::v3::kernel;
use minocrab_std::v3::kernel::SelfAddress;
use minocrab_std::v3::{
    Assumed,
    CoinColor, CoinNonce,
    contract, coin_commitment_to_contract, coin_nullifier_contract, ge, greater_than as gt, is_true, label, le,
    Bool, Bytes, CircuitArg, CoinRecipient, ContractAddress, Disclose, Discloses, Either, Ledger,
    LedgerCell, LedgerMap, LedgerRepr, LedgerSet, QualifiedShieldedCoinInfo3, Secp256k1Point, Secp256k1Scalar,
    ShieldedCoinInfo3, Uint, UserAddress, B32,
};

use crate::common;

label! {
    Payload = "execute payload";
    NativeAccount = "native account commitment";
    DepositCoin = "deposited coin";
    CreditAccount = "credit account";
    DepositColour = "deposited colour";
    DepositAmount = "deposited amount";
    QueriedAccount = "queried account";
    QueriedColour = "queried colour";
}

/// THE LEDGER BLOCK — declaration order is the field index, matching the
/// Compact `export ledger` block one for one.
#[derive(Ledger)]
pub struct Manager {
    pub pools: LedgerMap<CoinColor<Public>, QualifiedShieldedCoinInfo3<Public>>,
    pub accounts: LedgerSet<B32<Public>>,
    pub shielded_balances: LedgerMap<B32<Public>, Uint<128, Public>>,
    pub unshielded_balances: LedgerMap<B32<Public>, Uint<128, Public>>,
    pub account_modes: LedgerMap<B32<Public>, Uint<8, Public>>,
    pub evm_owners: LedgerMap<B32<Public>, Bytes<20, Public>>,
    pub evm_nonces: LedgerMap<B32<Public>, Uint<64, Public>>,
    pub deployment_domain: LedgerCell<B32<Public>>,
}

/// The contract's ledger block.
pub const MANAGER: Manager = Manager::new();

pub const POOLS: u8 = MANAGER.pools.index();
pub const ACCOUNTS: u8 = MANAGER.accounts.index();
pub const SHIELDED_BALANCES: u8 = MANAGER.shielded_balances.index();
pub const UNSHIELDED_BALANCES: u8 = MANAGER.unshielded_balances.index();
pub const ACCOUNT_MODES: u8 = MANAGER.account_modes.index();
pub const EVM_OWNERS: u8 = MANAGER.evm_owners.index();
pub const EVM_NONCES: u8 = MANAGER.evm_nonces.index();
pub const DEPLOYMENT_DOMAIN: u8 = MANAGER.deployment_domain.index();

// --- FROZEN DOMAIN SEPARATORS (consensus-critical byte constants) -----------

/// `persistentCommit<Bytes<21>>`'s tag — must be EXACTLY 21 bytes.
pub const OWNER_TAG: &[u8; 21] = b"aa:manager:owner:v1.0";
/// `pad(32, "aa:manager:shielded:v1")`.
pub const SHIELDED_FAMILY_TAG: &str = "aa:manager:shielded:v1";
/// `pad(32, "aa:manager:unshielded:v1")`.
pub const UNSHIELDED_FAMILY_TAG: &str = "aa:manager:unshielded:v1";

/// The frozen EIP-712 constants — keccak256 digests of the type strings,
/// byte-for-byte from the Compact source.
pub const ACCOUNT_TAG: [u8; 32] = [
    0x55, 0xbc, 0x94, 0x0f, 0x83, 0x53, 0x37, 0xf1, 0x22, 0x4c, 0x18, 0x11, 0x10, 0xb2, 0xb7,
    0x7f, 0x57, 0xed, 0x69, 0x4c, 0xae, 0x0c, 0x4b, 0xf8, 0xff, 0x6b, 0xb3, 0xe0, 0x3b, 0xe6,
    0xa9, 0x88,
];
pub const DOMAIN_TYPE: [u8; 32] = [
    0x36, 0xc2, 0x5d, 0xe3, 0xe5, 0x41, 0xd5, 0xd9, 0x70, 0xf6, 0x6e, 0x42, 0x10, 0xd7, 0x28,
    0x72, 0x12, 0x20, 0xff, 0xf5, 0xc0, 0x77, 0xcc, 0x6c, 0xd0, 0x08, 0xb3, 0xa0, 0xc6, 0x2a,
    0xda, 0xb7,
];
pub const DOMAIN_NAME: [u8; 32] = [
    0xb2, 0xa1, 0x61, 0xc1, 0xe1, 0xfe, 0x09, 0xf6, 0x31, 0x58, 0x5b, 0x3b, 0xda, 0x0e, 0x4a,
    0x22, 0xf3, 0x17, 0xd7, 0xc6, 0x63, 0xc5, 0x82, 0xa0, 0x7c, 0x1d, 0x68, 0x3e, 0x61, 0xfd,
    0xcd, 0xb1,
];
pub const DOMAIN_VERSION: [u8; 32] = [
    0xc8, 0x9e, 0xfd, 0xaa, 0x54, 0xc0, 0xf2, 0x0c, 0x7a, 0xdf, 0x61, 0x28, 0x82, 0xdf, 0x09,
    0x50, 0xf5, 0xa9, 0x51, 0x63, 0x7e, 0x03, 0x07, 0xcd, 0xcb, 0x4c, 0x67, 0x2f, 0x29, 0x8b,
    0x8b, 0xc6,
];
pub const REGISTER_TYPE: [u8; 32] = [
    0xe6, 0xac, 0xe6, 0xc7, 0x0a, 0x9d, 0x92, 0xef, 0x85, 0x1c, 0x2e, 0x2a, 0x67, 0xb2, 0x30,
    0x90, 0x17, 0xb0, 0x51, 0xd3, 0x9e, 0x05, 0x54, 0xc7, 0x46, 0x27, 0x4a, 0x17, 0x69, 0x59,
    0xac, 0x4f,
];
pub const WITHDRAW_SHIELDED_TYPE: [u8; 32] = [
    0x71, 0x7e, 0x1e, 0x74, 0x12, 0x98, 0x52, 0xbd, 0x43, 0x67, 0x44, 0xa5, 0xa1, 0x10, 0x8f,
    0x0d, 0xb9, 0x02, 0x92, 0x70, 0x31, 0xf5, 0xe7, 0x79, 0x96, 0x18, 0xec, 0x12, 0x93, 0x66,
    0xd6, 0x1e,
];
pub const WITHDRAW_UNSHIELDED_TYPE: [u8; 32] = [
    0xb6, 0x01, 0x29, 0xea, 0x6c, 0xa4, 0xc1, 0xb5, 0x1d, 0x86, 0x60, 0x77, 0xd1, 0x1c, 0xdb,
    0x02, 0x30, 0xe6, 0x06, 0x58, 0x76, 0xa5, 0x42, 0x06, 0xfe, 0xce, 0x04, 0x41, 0x3e, 0xda,
    0xba, 0x9d,
];
pub const TRANSFER_SHIELDED_TYPE: [u8; 32] = [
    0x06, 0xbe, 0xb8, 0x3e, 0xc8, 0xde, 0xd3, 0xa8, 0x08, 0x0b, 0xfa, 0xb5, 0x91, 0xd8, 0x9a,
    0x1b, 0x86, 0xed, 0x9e, 0x3f, 0x8d, 0xf6, 0xc1, 0x0e, 0xd3, 0x67, 0x74, 0x16, 0xd0, 0xa5,
    0x60, 0x64,
];
pub const TRANSFER_UNSHIELDED_TYPE: [u8; 32] = [
    0x46, 0xe9, 0x6f, 0x44, 0x96, 0xc1, 0x82, 0xe9, 0x83, 0x95, 0xb6, 0x89, 0x70, 0x1a, 0x94,
    0x5c, 0xbd, 0xb4, 0x75, 0x43, 0x57, 0x42, 0x42, 0xcc, 0x17, 0xf9, 0xb6, 0x44, 0x8c, 0x04,
    0x9a, 0x07,
];
pub const OPEN_SWAP_TYPE: [u8; 32] = [
    0xf7, 0x87, 0xd7, 0xf9, 0x63, 0xe8, 0x9e, 0xfc, 0xda, 0x8e, 0x6a, 0x54, 0x6b, 0xaf, 0xff,
    0x33, 0x38, 0x8c, 0xbd, 0xf4, 0x4b, 0x81, 0xf6, 0xf5, 0x95, 0x0c, 0x4b, 0xd3, 0xb0, 0x66,
    0x58, 0x48,
];

// --- small helpers -----------------------------------------------------------

fn atom(n: u32) -> AlignmentSegment {
    AlignmentSegment::Atom(AlignmentAtom::Bytes { length: n })
}

/// A frozen 32-byte constant as a `B32<Public>` (two constant limbs).
fn b32_const(c: &mut Circuit3, bytes: &[u8; 32]) -> B32<Public> {
    B32 {
        hi: c.constant(Fr::from(u64::from(bytes[31]))),
        lo: c.constant(Fr::from_le_bytes(&bytes[..31]).expect("31 bytes fit")),
    }
}

/// `a == b` on two `B32`s of any (equal) visibility — limb equality, joined.
fn b32_eq<V: minocrab_std::v3::Vis3>(
    c: &mut Circuit3,
    a: &B32<V>,
    b: &B32<V>,
) -> Wire3<FieldT, V> {
    let eq_hi = c.test_eq(a.hi, b.hi);
    let eq_lo = c.test_eq(a.lo, b.lo);
    c.mul(eq_hi, eq_lo)
}

/// `b == default<Bytes<32>>` — both limbs zero.
fn b32_is_zero<V: minocrab_std::v3::Vis3>(c: &mut Circuit3, b: &B32<V>) -> Wire3<FieldT, V> {
    let hi0 = c.test_eq(b.hi, 0u64);
    let lo0 = c.test_eq(b.lo, 0u64);
    c.mul(hi0, lo0)
}

/// `right<ZswapCoinPublicKey, ContractAddress>(addr)` as the tag-and-arms
/// shape the coin gadgets select over.
fn contract_recipient(c: &mut Circuit3, me: SelfAddress) -> CoinRecipient<Public> {
    let zero = c.constant(0u64);
    CoinRecipient {
        is_left: zero,
        left: minocrab_std::v3::ZswapCoinPublicKey(B32 { hi: zero, lo: zero }),
        right: me.address(),
    }
}

/// `persistentHash<Vector<3, Bytes<32>>>([acct, colour, tag])` — the
/// family-scoped storage key with the tag already selected.
fn family_key(
    c: &mut Circuit3,
    acct: &B32<Public>,
    colour: &CoinColor<Public>,
    tag: &B32<Public>,
) -> B32<Public> {
    let alignment = Alignment(vec![atom(32), atom(32), atom(32)]);
    let digest = c.persistent_hash(
        alignment,
        &[
            acct.hi.erase(),
            acct.lo.erase(),
            colour.bytes().hi.erase(),
            colour.bytes().lo.erase(),
            tag.hi.erase(),
            tag.lo.erase(),
        ],
    );
    B32::from_typed(c, digest)
}

/// `shieldedKey(acct, colour)`.
fn shielded_key(c: &mut Circuit3, acct: &B32<Public>, colour: &CoinColor<Public>) -> B32<Public> {
    let tag = B32::pad(c, SHIELDED_FAMILY_TAG);
    family_key(c, acct, colour, &tag)
}

/// `unshieldedKey(acct, colour)`.
fn unshielded_key(c: &mut Circuit3, acct: &B32<Public>, colour: &CoinColor<Public>) -> B32<Public> {
    let tag = B32::pad(c, UNSHIELDED_FAMILY_TAG);
    family_key(c, acct, colour, &tag)
}

/// A missing cell reads 0: `map.member(k) ? map.lookup(k) : 0`, the lookup
/// guarded by the member result. A skipped read's wires already hold zero,
/// which is compactc's own lowering of this shape (no select) — the member
/// result already carries whatever ambient guard is in scope, so no further
/// conjunction is LOGICALLY needed.
///
/// Not spelled as `c.when(member, |c| map.lookup(c, k)).or_default()`: this
/// call NESTS under an outer `c.when` at its one non-straight-line call site
/// (`custody_dispatch`'s debit read), and the scope conjoins once on entry
/// (`Circuit3::when`'s doc) where the old `_guarded` primitives conjoined
/// PER EFFECT (`Circuit3::effect_guard`, once per read and once for the
/// Impact op) — fewer rows, so not zero-movement. This calls the same core
/// primitives the deleted `LedgerMap::lookup_guarded` did, so the row count
/// is unchanged whether or not an outer scope is active.
fn balance_at(
    c: &mut Circuit3,
    map: &LedgerMap<B32<Public>, Uint<128, Public>>,
    k: &B32<Public>,
) -> Assumed<Wire3<FieldT, Public>> {
    let member = map.member(c, k).field();
    let key = k.ledger_value(c);
    let atoms = <Uint<128, Public> as LedgerRepr>::atoms();
    Assumed::of_read(guarded_map_lookup_field(c, member, map.index(), &key, atoms))
}

/// The one Impact op [`LedgerMap::lookup`] emits, under an EXPLICIT guard
/// resolved against the ambient scope PER EFFECT — [`Circuit3::
/// public_transcript_input_guarded`] for each limb, [`Circuit3::impact_mixed`]
/// for the op — exactly what the deleted `map_lookup_guarded_at` did. Kept
/// as the one caller ([`balance_at`]) that nests an explicit data-dependent
/// guard under another scope and needs the per-effect conjunction, not the
/// once-on-entry one `c.when` gives.
fn guarded_map_lookup_field(
    c: &mut Circuit3,
    guard: Wire3<FieldT, Public>,
    index: u8,
    key: &minocrab_ledger::LedgerValue,
    atoms: Vec<AlignmentAtom>,
) -> Wire3<FieldT, Public> {
    let limbs: usize = atoms.iter().map(minocrab_ledger::atom_limbs).sum();
    let wires: Vec<Wire3<FieldT, Public>> = (0..limbs)
        .map(|_| c.public_transcript_input_guarded::<FieldT, Public>(guard))
        .collect();
    let value = minocrab_ledger::LedgerValue::new(
        atoms,
        wires.iter().map(|&w| minocrab::v3::ImpactElem::Wire(w)).collect(),
    );
    let path = [minocrab_ledger::LedgerKey::Field(index)];
    for op in [
        minocrab_ledger::dup(0),
        minocrab_ledger::idx_path(false, false, &path),
        minocrab_ledger::idx_key(key),
        minocrab_ledger::popeq(false, &value),
    ] {
        c.impact_mixed(guard, &op.0);
    }
    wires[0]
}

/// `ownerCommitment(sk)` — `persistentCommit<Bytes<21>>(OWNER_TAG, sk)`:
/// one `persistent_hash` whose preimage is sk-then-tag, alignment
/// `[bytes 32, bytes 21]` (the stdlib's `persistentCommit` is
/// rand-then-value; here the VALUE is the 21-byte tag and the RAND the
/// secret).
fn owner_commitment(c: &mut Circuit3, sk: &common::SecretKey<Private>) -> B32<Private> {
    let sk = sk.bytes();
    let tag = c.constant(Fr::from_le_bytes(OWNER_TAG).expect("21 bytes fit"));
    let alignment = Alignment(vec![atom(32), atom(21)]);
    let digest = c.persistent_hash(
        alignment,
        &[sk.hi.erase(), sk.lo.erase(), tag.private().erase()],
    );
    B32::from_typed(c, digest)
}

// --- the EIP-712 byte codec --------------------------------------------------
//
// Every preimage is assembled as an ALIGNMENT plus the values' limbs — the
// keccak chip packs the bytes in-chip, so a preimage of k 32-byte words
// costs the words' construction and nothing per byte. compactc builds each
// `Bytes<N>` by byte explosion and rebuild before hashing it, which is the
// dominant cost of its `execute` (see the row comparison in the report).

/// `uint*Word(value)` — the value as a 32-byte big-endian ABI word.
fn numeric_word<V: minocrab_std::v3::Vis3>(
    c: &mut Circuit3,
    value: Wire3<FieldT, V>,
) -> B32<V> {
    crate::signet::numeric_abi_word(c, value)
}

/// `addressWord(addr)` — the 20-byte address at bytes 12..31 of a word.
fn address_word<V: minocrab_std::v3::Vis3>(
    c: &mut Circuit3,
    addr: Wire3<FieldT, V>,
) -> B32<V> {
    crate::signet::evm_address_abi_word(c, addr)
}

/// keccak256 over a list of 32-byte words.
fn keccak_words<V: minocrab_std::v3::Vis3>(c: &mut Circuit3, words: &[&B32<V>]) -> B32<V> {
    let alignment = Alignment(words.iter().map(|_| atom(32)).collect());
    let mut limbs = Vec::with_capacity(words.len() * 2);
    for w in words {
        limbs.push(w.hi.erase());
        limbs.push(w.lo.erase());
    }
    let digest = c.keccak256(alignment, &limbs);
    B32::from_typed(c, digest)
}

/// `evmAccountIdFor(manager, owner, salt)` —
/// `keccak256<Bytes<128>>(accountTag ‖ manager ‖ addressWord(owner) ‖ salt)`.
fn evm_account_id_for(
    c: &mut Circuit3,
    manager: &B32<Public>,
    owner: Wire3<FieldT, Public>,
    salt: &B32<Public>,
) -> B32<Public> {
    c.region("eip712: account id", |c| {
        let tag = b32_const(c, &ACCOUNT_TAG);
        let owner_word = address_word(c, owner);
        keccak_words(c, &[&tag, manager, &owner_word, salt])
    })
}

/// `evmDomainSeparatorFor(manager, domain)`: the contract-address ALIAS is
/// the low 20 bytes of `keccak256(manager)` — bytes 12..31 of the digest,
/// recovered algebraically (`div_mod` at bit 96 of the low limb, the high
/// byte rejoined at 2^152) — then
/// `keccak256<Bytes<160>>(domainType ‖ domainName ‖ domainVersion ‖
/// addressWord(alias) ‖ domain)`.
fn evm_domain_separator_for(
    c: &mut Circuit3,
    manager: &B32<Public>,
    domain: &B32<Public>,
) -> B32<Public> {
    c.region("eip712: domain separator", |c| {
        let addr_digest = keccak_words(c, &[manager]);
        // slice<20>(digest, 12): bytes 12..30 come off the low limb, byte 31
        // is the high limb, rejoined at byte position 19 of the alias.
        let (_low12, rest) = {
            let (q, _r) = c.div_mod_power_of_two(addr_digest.lo, 96);
            ((), q)
        };
        let shift152 = c.constant(Fr::from_le_bytes(&pow2_bytes(19)).expect("2^152 fits"));
        let hi_shifted = c.mul(addr_digest.hi, shift152);
        let alias = c.add(rest, hi_shifted);
        let alias_word = address_word(c, alias);

        let dt = b32_const(c, &DOMAIN_TYPE);
        let dn = b32_const(c, &DOMAIN_NAME);
        let dv = b32_const(c, &DOMAIN_VERSION);
        keccak_words(c, &[&dt, &dn, &dv, &alias_word, domain])
    })
}

/// `2^(8*bytes)` as little-endian bytes for a field constant.
fn pow2_bytes(bytes: usize) -> Vec<u8> {
    let mut v = vec![0u8; bytes + 1];
    v[bytes] = 1;
    v
}

/// `eip712Digest(domain, structHash)` —
/// `keccak256<Bytes<66>>(0x19 ‖ 0x01 ‖ domain ‖ structHash)`.
fn eip712_digest(
    c: &mut Circuit3,
    domain: &B32<Public>,
    struct_hash: &B32<Public>,
) -> B32<Public> {
    let alignment = Alignment(vec![atom(2), atom(32), atom(32)]);
    // Bytes 0x19, 0x01 in string order: LE limb value 0x19 + 0x01·256.
    let prefix = c.constant(Fr::from(0x0119u64));
    let digest = c.keccak256(
        alignment,
        &[
            prefix.erase(),
            domain.hi.erase(),
            domain.lo.erase(),
            struct_hash.hi.erase(),
            struct_hash.lo.erase(),
        ],
    );
    B32::from_typed(c, digest)
}

// --- the payload -------------------------------------------------------------

/// `ExecutePayload` — the single fixed-width action/auth envelope. Field
/// order is the wire contract (24 slots).
#[derive(CircuitArg)]
struct ExecutePayloadArg {
    selector: Uint<8>,
    auth_mode: Uint<8>,
    account: B32<Private>,
    owner: Bytes<20>,
    account_salt: B32<Private>,
    nonce: Uint<64>,
    valid_until: Uint<64>,
    primary_color: CoinColor<Private>,
    primary_amount: Uint<128>,
    recipient_kind: Uint<8>,
    recipient: B32<Private>,
    to_account: B32<Private>,
    want_nonce: CoinNonce<Private>,
    want_color: CoinColor<Private>,
    want_amount: Uint<128>,
    credit_account: B32<Private>,
}

/// `Secp256k1EcdsaSignature { r: Secp256k1Scalar, s: Secp256k1Scalar }`.
#[derive(CircuitArg)]
struct SignatureArg {
    r: Secp256k1Scalar<Private>,
    s: Secp256k1Scalar<Private>,
}

/// The whole payload, DISCLOSED (`const p = disclose(payload)`) — every
/// field crosses the gate under the one [`Payload`] label, and the public
/// copies are what the guards, keys and ledger ops read.
struct PublicPayload {
    selector: Wire3<FieldT, Public>,
    auth_mode: Wire3<FieldT, Public>,
    account: B32<Public>,
    owner: Wire3<FieldT, Public>,
    account_salt: B32<Public>,
    nonce: Wire3<FieldT, Public>,
    valid_until: Wire3<FieldT, Public>,
    primary_color: CoinColor<Public>,
    primary_amount: Wire3<FieldT, Public>,
    recipient_kind: Wire3<FieldT, Public>,
    recipient: B32<Public>,
    to_account: B32<Public>,
    want_nonce: CoinNonce<Public>,
    want_color: CoinColor<Public>,
    want_amount: Wire3<FieldT, Public>,
    credit_account: B32<Public>,
}

impl ExecutePayloadArg {
    fn disclose(self, c: &mut Circuit3) -> PublicPayload {
        PublicPayload {
            selector: self.selector.disclose_as::<Payload>(c).field(),
            auth_mode: self.auth_mode.disclose_as::<Payload>(c).field(),
            account: self.account.disclose_as::<Payload>(c),
            owner: self.owner.disclose_as::<Payload>(c).field(),
            account_salt: self.account_salt.disclose_as::<Payload>(c),
            nonce: self.nonce.disclose_as::<Payload>(c).field(),
            valid_until: self.valid_until.disclose_as::<Payload>(c).field(),
            primary_color: self.primary_color.disclose_as::<Payload>(c),
            primary_amount: self.primary_amount.disclose_as::<Payload>(c).field(),
            recipient_kind: self.recipient_kind.disclose_as::<Payload>(c).field(),
            recipient: self.recipient.disclose_as::<Payload>(c),
            to_account: self.to_account.disclose_as::<Payload>(c),
            want_nonce: self.want_nonce.disclose_as::<Payload>(c),
            want_color: self.want_color.disclose_as::<Payload>(c),
            want_amount: self.want_amount.disclose_as::<Payload>(c).field(),
            credit_account: self.credit_account.disclose_as::<Payload>(c),
        }
    }
}

// --- readers -----------------------------------------------------------------

#[contract]
impl Manager {
    /// `export circuit isRegistered(owner: Bytes<32>): Boolean`.
    #[circuit(output = "registered")]
    pub fn is_registered(
        c: &mut Circuit3,
        owner: B32<Private>,
    ) -> Discloses<(QueriedAccount,), Bool<Public>> {
        let owner = owner.disclose_as::<QueriedAccount>(c);
        Discloses::of(*MANAGER.accounts.member(c, &owner))
    }

    /// `export circuit accountRecord(account: Bytes<32>): AccountRecord` — one
    /// policy query covering registration, mode, EVM owner and next nonce.
    /// Unknown accounts return the all-zero inactive record; native records
    /// return zero owner/nonce WITHOUT reading the EVM maps' values (only their
    /// membership, asserted absent).
    #[circuit(output = "record")]
    pub fn account_record(
        c: &mut Circuit3,
        account: B32<Private>,
    ) -> Discloses<(QueriedAccount,), AccountRecordOut> {
        let acct = account.disclose_as::<QueriedAccount>(c);

        let registered = MANAGER.accounts.member(c, &acct).field();

        // The mode read carries `registered`, and a SKIPPED read's zero IS the
        // inactive record's mode — no select anywhere in this circuit, which is
        // compactc's own shape for the early-return ladder.
        let mode = c
            .when(registered, |c| MANAGER.account_modes.lookup(c, &acct))
            .or_default()
            .field();
        let is_native = c.test_eq(mode, 0u64);

        // Native record: no EVM state may exist. The second membership read
        // short-circuits on the first's result, exactly as `&&` evaluates.
        let g_native = c.mul(registered, is_native);
        c.when(g_native, |c| {
            let m5 = MANAGER.evm_owners.member(c, &acct).field();
            let n5 = c.not(m5);
            let zero = c.constant(0u64);
            let mut m6 = zero;
            c.when(n5, |c| {
                m6 = MANAGER.evm_nonces.member(c, &acct).field();
            });
            let n6 = c.not(m6);
            let both = c.mul(n5, n6);
            c.assert_with(both, Some("native record carries EVM state"));
        });

        // EVM record: both halves must exist; the lookups' wires are zero on
        // every other path, which is the record's inactive form already.
        let is_evm = c.not(is_native);
        let g_evm = c.mul(registered, is_evm);
        let zero = c.constant(0u64);
        let mut owner_v = zero;
        let mut nonce_v = zero;
        c.when(g_evm, |c| {
            let is_one = c.test_eq(mode, 1u64);
            c.assert_with(is_one, Some("unknown account authorization mode"));
            let m5 = MANAGER.evm_owners.member(c, &acct).field();
            let mut m6 = zero;
            c.when(m5, |c| {
                m6 = MANAGER.evm_nonces.member(c, &acct).field();
            });
            let both = c.mul(m5, m6);
            c.assert_with(both, Some("EVM record is incomplete"));
            owner_v = MANAGER.evm_owners.lookup(c, &acct).field();
            nonce_v = MANAGER.evm_nonces.lookup(c, &acct).field();
        });

        Discloses::of(AccountRecordOut {
            registered: Bool::from_field_unchecked(registered),
            mode: Uint::from_field_unchecked(mode),
            owner: Bytes::from_field_unchecked(owner_v),
            next_nonce: Uint::from_field_unchecked(nonce_v),
        })
    }

    /// `export circuit shieldedAccountBalance(owner, colour): Uint<128>`.
    #[circuit(output = "balance")]
    pub fn shielded_account_balance(
        c: &mut Circuit3,
        owner: B32<Private>,
        colour: CoinColor<Private>,
    ) -> Discloses<(QueriedAccount, QueriedColour), Uint<128, Public>> {
        let owner = owner.disclose_as::<QueriedAccount>(c);
        let colour = colour.disclose_as::<QueriedColour>(c);
        let k = shielded_key(c, &owner, &colour);
        let v = balance_at(c, &MANAGER.shielded_balances, &k);
        Discloses::of(Uint::from_field_unchecked(*v))
    }

    /// `export circuit unshieldedAccountBalance(owner, colour): Uint<128>`.
    #[circuit(output = "balance")]
    pub fn unshielded_account_balance(
        c: &mut Circuit3,
        owner: B32<Private>,
        colour: CoinColor<Private>,
    ) -> Discloses<(QueriedAccount, QueriedColour), Uint<128, Public>> {
        let owner = owner.disclose_as::<QueriedAccount>(c);
        let colour = colour.disclose_as::<QueriedColour>(c);
        let k = unshielded_key(c, &owner, &colour);
        let v = balance_at(c, &MANAGER.unshielded_balances, &k);
        Discloses::of(Uint::from_field_unchecked(*v))
    }

    /// `export circuit poolValue(colour): Uint<128>` — the pooled coin's value,
    /// 0 for a colour this contract has never seen.
    #[circuit(output = "value")]
    pub fn pool_value(
        c: &mut Circuit3,
        colour: CoinColor<Private>,
    ) -> Discloses<(QueriedColour,), Uint<128, Public>> {
        let col = colour.disclose_as::<QueriedColour>(c);
        let member = MANAGER.pools.member(c, &col).field();
        let v = c.when(member, |c| MANAGER.pools.lookup(c, &col)).or_default().value;
        Discloses::of(Uint::from_field_unchecked(v))
    }

    /// `export circuit poolHasColour(colour): Boolean`.
    #[circuit(output = "present")]
    pub fn pool_has_colour(
        c: &mut Circuit3,
        colour: CoinColor<Private>,
    ) -> Discloses<(QueriedColour,), Bool<Public>> {
        let col = colour.disclose_as::<QueriedColour>(c);
        Discloses::of(*MANAGER.pools.member(c, &col))
    }

    /// `export circuit depositShielded(coin: ShieldedCoinInfo, account:
    /// Bytes<32>): []` — claim an incoming shielded coin and credit it to
    /// `account` under the coin's own colour, merging into the colour's single
    /// pooled coin (created here on first credit).
    #[circuit]
    pub fn deposit_shielded(
        c: &mut Circuit3,
        coin: ShieldedCoinArg,
        account: B32<Private>,
    ) -> Discloses<(DepositCoin, CreditAccount)> {
        let coin_value = coin.value;
        let coin = ShieldedCoinInfo3 {
            nonce: coin.nonce.disclose_as::<DepositCoin>(c),
            color: coin.color.disclose_as::<DepositCoin>(c),
            value: coin_value.disclose_as::<DepositCoin>(c).field(),
        };
        let acct = account.disclose_as::<CreditAccount>(c);

        // Kept even though guard threading no longer uses it: dropping this
        // `Copy` would renumber every later identifier, moving the ZKIR
        // (notes/edsl-trim.org §B, the removal's zero-movement gate).
        let _ = c.constant(1u64);

        // assert(c.value > 0, "deposit must be positive")
        c.assert(
            gt(
                Uint::<128, Public>::from_field_unchecked(coin.value),
                0u64,
            )
            .message("deposit must be positive"),
        );

        // assert(accounts.member(acct), "credit account is not registered")
        let known = MANAGER.accounts.member(c, &acct);
        c.assert(is_true(known).message("credit account is not registered"));

        // receiveShielded(c) — allocates the Merkle-tree index; must precede
        // insertCoin.
        common::receive_shielded(c, &coin);

        // Merge-on-deposit: one pooled coin per colour.
        let member = MANAGER.pools.member(c, &coin.color).field();
        c.when(member, |c| {
            let pooled = MANAGER.pools.lookup(c, &coin.color);
            let merged = kernel::merge_coin_immediate(c, &pooled, &coin);
            let me = kernel::self_address(c);
            let recipient = contract_recipient(c, me);
            MANAGER.pools.insert_coin(c, &coin.color, &merged, &recipient);
        });
        let fresh = c.not(member);
        c.when(fresh, |c| {
            let me = kernel::self_address(c);
            let recipient = contract_recipient(c, me);
            MANAGER.pools.insert_coin(c, &coin.color, &coin, &recipient);
        });

        // shieldedBalances.insert(shieldedKey(acct, c.color),
        //   (shieldedBalanceOf(acct, c.color) + c.value) as Uint<128>)
        let k = shielded_key(c, &acct, &coin.color);
        let prior = balance_at(c, &MANAGER.shielded_balances, &k).stale(c);
        let sum = c.add(prior, coin.value);
        let new_balance = Uint::<128, Public>::from_field_unchecked(sum);
        new_balance.constrain_input(c);
        MANAGER.shielded_balances.insert(c, &k, &new_balance);

        Discloses::of(())
    }

    /// `export circuit depositUnshielded(colour, amount, account): []` — credit
    /// `amount` of `colour` to `account`, unshielded family; the ledger's
    /// balancing enforces the deposit's honesty.
    #[circuit]
    pub fn deposit_unshielded(
        c: &mut Circuit3,
        colour: CoinColor<Private>,
        amount: Uint<128>,
        account: B32<Private>,
    ) -> Discloses<(DepositColour, DepositAmount, CreditAccount)> {
        let col = colour.disclose_as::<DepositColour>(c);
        let amt = amount.disclose_as::<DepositAmount>(c);
        let acct = account.disclose_as::<CreditAccount>(c);

        c.assert(gt(amt, 0u64).message("deposit must be positive"));
        let known = MANAGER.accounts.member(c, &acct);
        c.assert(is_true(known).message("credit account is not registered"));

        kernel::receive_unshielded(c, col, amt);

        let k = unshielded_key(c, &acct, &col);
        let prior = balance_at(c, &MANAGER.unshielded_balances, &k).stale(c);
        let sum = c.add(prior, amt.field());
        let new_balance = Uint::<128, Public>::from_field_unchecked(sum);
        new_balance.constrain_input(c);
        MANAGER.unshielded_balances.insert(c, &k, &new_balance);

        Discloses::of(())
    }

    /// `export circuit execute(payload, sig, pk): []` — THE gateway: validate
    /// the envelope, compute the EIP-712 digest (all four struct-hash branches
    /// — a circuit has no control flow), run the ECDSA check straight-line,
    /// resolve the acting account through the witness choke point, enforce the
    /// deadline, then register OR dispatch custody, then write the nonce.
    #[circuit]
    pub fn execute(
        c: &mut Circuit3,
        payload: ExecutePayloadArg,
        sig: SignatureArg,
        pk: Secp256k1Point,
    ) -> Discloses<(Payload, NativeAccount)> {
        // const p = disclose(payload)
        let p = payload.disclose(c);
        let f = Flags::of(c, &p);

        assert_action_envelope(c, &p, &f);

        // const manager = kernel.self().bytes
        let manager = kernel::self_address(c).bytes();

        // const digest = p.selector == 0 ? default<Bytes<32>>
        //   : evmDigestFor(manager, deploymentDomain, p)
        // — the deploymentDomain READ is guarded by the branch; the keccak
        // chain runs unconditionally (a circuit has no control flow).
        let not_native_reg = c.not(f.is0);
        let domain = {
            let mut d = B32 {
                hi: c.constant(0u64),
                lo: c.constant(0u64),
            };
            c.when(not_native_reg, |c| {
                d = *MANAGER.deployment_domain.read(c);
            });
            d
        };
        let domain_separator = evm_domain_separator_for(c, &manager, &domain);
        let struct_hash = evm_struct_hash_for(c, &manager, &p, &f);
        let evm_digest = eip712_digest(c, &domain_separator, &struct_hash);
        let zero = c.constant(0u64);
        let digest = B32 {
            hi: c.cond_select(f.is0, zero, evm_digest.hi),
            lo: c.cond_select(f.is0, zero, evm_digest.lo),
        };

        // const signatureOk = secp256k1EcdsaVerify(digest, sig, pk)
        // const signer = secp256k1EthereumAddress(pk)
        // STRAIGHT-LINE, exactly as the source demands (the pinned proving
        // backend cannot lower guarded secp256k1 operations).
        let signature = minocrab_std::v3::Secp256k1EcdsaSignature {
            r: sig.r.scalar(),
            s: sig.s.scalar(),
        };
        let digest_priv = B32 {
            hi: digest.hi.private(),
            lo: digest.lo.private(),
        };
        let signature_ok = minocrab_std::v3::secp256k1_ecdsa_verify(c, &digest_priv, &signature, pk.point());
        let signer = minocrab_std::v3::secp256k1_ethereum_address(c, pk.point());

        let is_evm_action = c.mul(f.is_evm_authorized, f.is_action);

        // const nativeAccount = ownerCommitment(localOwnerSecret())
        let sk = common::witness_sk(c);
        let native_account_priv = owner_commitment(c, &sk);
        let native_account = native_account_priv.disclose_as::<NativeAccount>(c);

        // const evmRegistrationAccount = evmAccountIdFor(manager, owner, salt)
        let evm_registration_account = evm_account_id_for(c, &manager, p.owner, &p.account_salt);

        // assert(!isEvmRegistration || evmRegistrationAccount == p.account)
        c.when(f.is1, |c| {
            let same = b32_eq(c, &evm_registration_account, &p.account);
            c.assert_with(same, Some("EVM registration account id mismatch"));
        });

        // const account = gatewayAccount(p, nativeAccount, evmRegistrationAccount)
        // — registration selects the account being created; every other
        // selector runs the authentication below, whose ledger reads carry the
        // action guard.
        let g_native_action = c.mul(f.is_action, f.is_native_authorized);
        c.when(g_native_action, |c| {
            // authenticatedNativeAccount(nativeAccount)
            let known = MANAGER.accounts.member(c, &native_account).field();
            c.assert_with(known, Some("caller's owner witness matches no registered account"));
            let has_mode = MANAGER.account_modes.member(c, &native_account).field();
            c.assert_with(has_mode, Some("registered account has no authorization mode"));
            let mode = MANAGER.account_modes.lookup(c, &native_account).field();
            let native_mode = c.test_eq(mode, 0u64);
            c.assert_with(native_mode, Some("EVM account cannot enter native authorization"));
            // …then the action-level checks.
            let same = b32_eq(c, &native_account, &p.account);
            c.assert_with(same, Some("native witness does not match supplied account transcript"));
            let mode_again = MANAGER.account_modes.lookup(c, &native_account).field();
            let mode_matches = c.test_eq(mode_again, p.auth_mode);
            c.assert_with(mode_matches, Some("authorization mode does not match account record"));
            // assert(!evmOwners.member && !evmNonces.member) — the second read
            // short-circuits on the first.
            let m5 = MANAGER.evm_owners.member(c, &native_account).field();
            let n5 = c.not(m5);
            let zero = c.constant(0u64);
            let mut m6 = zero;
            c.when(n5, |c| {
                m6 = MANAGER.evm_nonces.member(c, &native_account).field();
            });
            let n6 = c.not(m6);
            let both = c.mul(n5, n6);
            c.assert_with(both, Some("native account carries EVM state"));
        });
        let g_evm_action = c.mul(f.is_action, f.is_evm_authorized);
        c.when(g_evm_action, |c| {
            let known = MANAGER.accounts.member(c, &p.account).field();
            c.assert_with(known, Some("gateway account is not registered"));
            let has_mode = MANAGER.account_modes.member(c, &p.account).field();
            c.assert_with(has_mode, Some("registered account has no authorization mode"));
            let mode = MANAGER.account_modes.lookup(c, &p.account).field();
            let evm_mode = c.test_eq(mode, 1u64);
            c.assert_with(evm_mode, Some("authorization mode does not match account record"));
            // assert(evmOwners.member && evmNonces.member) — short-circuit.
            let m5 = MANAGER.evm_owners.member(c, &p.account).field();
            let zero = c.constant(0u64);
            let mut m6 = zero;
            c.when(m5, |c| {
                m6 = MANAGER.evm_nonces.member(c, &p.account).field();
            });
            let both = c.mul(m5, m6);
            c.assert_with(both, Some("EVM account record is incomplete"));
            let stored_owner = MANAGER.evm_owners.lookup(c, &p.account).field();
            let owner_matches = c.test_eq(p.owner, stored_owner);
            c.assert_with(owner_matches, Some("signed owner does not match stored owner"));
            let stored_nonce = MANAGER.evm_nonces.lookup(c, &p.account).field();
            let nonce_matches = c.test_eq(p.nonce, stored_nonce);
            c.assert_with(nonce_matches, Some("EVM nonce mismatch"));
        });
        let action_account = B32::cond_select(c, f.is_native_authorized, &native_account, &p.account);
        let reg_account = B32::cond_select(c, f.is0, &native_account, &evm_registration_account);
        let account = B32::cond_select(c, f.is_registration, &reg_account, &action_account);

        // if (isEvmAuthorized) { assertLiveDeadline(p.validUntil) }
        c.when(f.is_evm_authorized, |c| {
            let until = Uint::<64, Public>::from_field_unchecked(p.valid_until);
            let horizon = gt(until, 3600u64).eval(c).field();
            c.assert_with(horizon, Some("EVM authorization deadline cannot satisfy the horizon"));
            // Compact's subtraction guard, folded with this branch.
            let no_underflow = ge(until, 3600u64).eval(c).field();
            c.assert_with(no_underflow, Some("result of subtraction would be negative"));
            // HAZARD kept as-is from the source: on a NATIVE call this
            // subtraction underflows into a negative field element — safe only
            // because its single consumer is the guarded blockTimeGte below.
            let minus = c.constant(3600u64);
            let neg = c.neg(minus);
            let earliest = c.add(p.valid_until, neg);
            let not_expired_early = kernel::block_time_gte(c, Uint::from_field_unchecked(earliest));
            c.assert(
                is_true(not_expired_early)
                    .message("EVM authorization deadline exceeds 3600-second horizon"),
            );
            let not_expired = kernel::block_time_lt(c, until);
            c.assert(is_true(not_expired).message("EVM authorization has expired"));
        });

        // The signature bindings, guard-folded per mode.
        c.when(f.is1, |c| {
            c.assert_with(signature_ok, Some("EVM registration signature does not verify"));
            let same = c.test_eq(signer, p.owner.private());
            c.assert_with(same, Some("EVM registration signer does not match owner"));
        });
        c.when(is_evm_action, |c| {
            c.assert_with(signature_ok, Some("EVM signature does not verify"));
            let same = c.test_eq(signer, p.owner.private());
            c.assert_with(same, Some("EVM signer does not control account"));
        });

        // if (isRegistration) { registerAccount(account, mode) }
        c.when(f.is_registration, |c| {
            let acct0 = b32_is_zero(c, &account);
            let acct_set = c.not(acct0);
            c.assert_with(acct_set, Some("account id must be nonzero"));
            let taken = MANAGER.accounts.member(c, &account).field();
            let free = c.not(taken);
            c.assert_with(free, Some("account already registered"));
            let mode_taken = MANAGER.account_modes.member(c, &account).field();
            let mode_free = c.not(mode_taken);
            c.assert_with(mode_free, Some("account mode collision"));
            MANAGER.accounts.insert(c, &account);
            let mode = Uint::<8, Public>::from_field_unchecked(f.is1);
            MANAGER.account_modes.insert(c, &account, &mode);
        });

        // if (isEvmRegistration) { evmOwners.insert(account, p.owner) }
        c.when(f.is1, |c| {
            let owner = Bytes::<20, Public>::from_field_unchecked(p.owner);
            MANAGER.evm_owners.insert(c, &account, &owner);
        });

        // if (!isRegistration) { custodyDispatch(p, account) }
        c.when(f.is_action, |c| {
            custody_dispatch(c, &p, &f, &account);
        });

        // The checked nonce write, AFTER the custody dispatch.
        let one_c = c.constant(1u64);
        let incremented = c.add(p.nonce, one_c);
        let inc_u64 = Uint::<64, Public>::from_field_unchecked(incremented);
        inc_u64.constrain_input(c);
        c.when(is_evm_action, |c| {
            let grows = gt(inc_u64, Uint::<64, Public>::from_field_unchecked(p.nonce))
                .eval(c)
                .field();
            c.assert_with(grows, Some("EVM nonce overflow"));
        });
        let stored_nonce = c.cond_select(f.is1, zero, incremented);
        c.when(f.is_evm_authorized, |c| {
            let value = Uint::<64, Public>::from_field_unchecked(stored_nonce);
            MANAGER.evm_nonces.insert(c, &account, &value);
        });

        Discloses::of(())
    }
}

/// `AccountRecord { registered, mode, owner, nextNonce }` as circuit
/// outputs — four slots in declaration order.
pub struct AccountRecordOut {
    pub registered: Bool<Public>,
    pub mode: Uint<8, Public>,
    pub owner: Bytes<20, Public>,
    pub next_nonce: Uint<64, Public>,
}

impl minocrab_std::v3::CircuitOut for AccountRecordOut {
    const SLOTS: usize = 4;

    fn emit(self, c: &mut Circuit3, label: &str) {
        self.registered.emit(c, &format!("{label} registered"));
        self.mode.emit(c, &format!("{label} mode"));
        self.owner.emit(c, &format!("{label} owner"));
        self.next_nonce.emit(c, &format!("{label} nextNonce"));
    }
}

// --- deposits ----------------------------------------------------------------

/// `ShieldedCoinInfo` as an argument.
#[derive(CircuitArg)]
struct ShieldedCoinArg {
    nonce: CoinNonce<Private>,
    color: CoinColor<Private>,
    value: Uint<128>,
}

// --- the gateway -------------------------------------------------------------

/// The selector/mode flags every `execute` stage muxes on. All Public — the
/// payload is disclosed before anything reads it.
struct Flags {
    is0: Wire3<FieldT, Public>,
    is1: Wire3<FieldT, Public>,
    is2: Wire3<FieldT, Public>,
    is3: Wire3<FieldT, Public>,
    is4: Wire3<FieldT, Public>,
    is5: Wire3<FieldT, Public>,
    is6: Wire3<FieldT, Public>,
    is_registration: Wire3<FieldT, Public>,
    is_action: Wire3<FieldT, Public>,
    is_evm_authorized: Wire3<FieldT, Public>,
    is_native_authorized: Wire3<FieldT, Public>,
}

impl Flags {
    fn of(c: &mut Circuit3, p: &PublicPayload) -> Flags {
        let is0 = c.test_eq(p.selector, 0u64);
        let is1 = c.test_eq(p.selector, 1u64);
        let is2 = c.test_eq(p.selector, 2u64);
        let is3 = c.test_eq(p.selector, 3u64);
        let is4 = c.test_eq(p.selector, 4u64);
        let is5 = c.test_eq(p.selector, 5u64);
        let is6 = c.test_eq(p.selector, 6u64);
        let is_registration = c.add(is0, is1);
        let is_action = c.not(is_registration);
        let is_evm_authorized = c.test_eq(p.auth_mode, 1u64);
        let is_native_authorized = c.not(is_evm_authorized);
        Flags {
            is0,
            is1,
            is2,
            is3,
            is4,
            is5,
            is6,
            is_registration,
            is_action,
            is_evm_authorized,
            is_native_authorized,
        }
    }
}

/// `assertActionEnvelope(p)` — canonical-zero envelope validation: ONE
/// selector implies ONE field set; everything inactive is constrained to
/// its canonical zero before authentication or custody logic runs. Pure
/// arithmetic (no ledger reads), so it is exactly its assert list, each
/// folded with its branch's guard.
fn assert_action_envelope(c: &mut Circuit3, p: &PublicPayload, f: &Flags) {
    let sel = Uint::<8, Public>::from_field_unchecked(p.selector);
    let auth = Uint::<8, Public>::from_field_unchecked(p.auth_mode);
    let kind = Uint::<8, Public>::from_field_unchecked(p.recipient_kind);
    let until = Uint::<64, Public>::from_field_unchecked(p.valid_until);
    let amount = Uint::<128, Public>::from_field_unchecked(p.primary_amount);
    let want = Uint::<128, Public>::from_field_unchecked(p.want_amount);

    c.assert(le(sel, 6u64).message("unknown execute selector"));
    c.assert(le(auth, 1u64).message("unknown authorization mode"));

    // Reusable zero-form tests.
    let acct0 = b32_is_zero(c, &p.account);
    let salt0 = b32_is_zero(c, &p.account_salt);
    let owner0 = c.test_eq(p.owner, 0u64);
    let nonce0 = c.test_eq(p.nonce, 0u64);
    let until0 = c.test_eq(p.valid_until, 0u64);
    let color0 = b32_is_zero(c, &p.primary_color.bytes());
    let amount0 = c.test_eq(p.primary_amount, 0u64);
    let kind0 = c.test_eq(p.recipient_kind, 0u64);
    let rcpt0 = b32_is_zero(c, &p.recipient);
    let to0 = b32_is_zero(c, &p.to_account);
    let wnonce0 = b32_is_zero(c, &p.want_nonce.bytes());
    let wcolor0 = b32_is_zero(c, &p.want_color.bytes());
    let wamount0 = c.test_eq(p.want_amount, 0u64);
    let credit0 = b32_is_zero(c, &p.credit_account);

    // selector 0 — native registration.
    c.when(f.is0, |c| {
        let native = c.test_eq(p.auth_mode, 0u64);
        c.assert_with(native, Some("native registration requires native authorization"));
        c.assert_with(acct0, Some("native registration account is derived"));
        let both = c.mul(owner0, salt0);
        c.assert_with(both, Some("native registration EVM fields must be inactive"));
        let both = c.mul(nonce0, until0);
        c.assert_with(both, Some("native registration replay fields must be inactive"));
        let both = c.mul(color0, amount0);
        c.assert_with(both, Some("native registration action fields must be inactive"));
        let both = c.mul(kind0, rcpt0);
        c.assert_with(both, Some("native registration recipient must be inactive"));
        let both = c.mul(to0, wnonce0);
        c.assert_with(both, Some("native registration targets must be inactive"));
        let both = c.mul(wcolor0, wamount0);
        let all = c.mul(both, credit0);
        c.assert_with(all, Some("native registration swap fields must be inactive"));
    });

    // selector 1 — EVM registration.
    c.when(f.is1, |c| {
        let evm = c.test_eq(p.auth_mode, 1u64);
        c.assert_with(evm, Some("EVM registration requires EVM authorization"));
        let acct_set = c.not(acct0);
        c.assert_with(acct_set, Some("EVM registration account must be supplied"));
        let owner_set = c.not(owner0);
        c.assert_with(owner_set, Some("EVM registration owner must be nonzero"));
        let salt_set = c.not(salt0);
        c.assert_with(salt_set, Some("EVM registration salt must be nonzero"));
        let live = gt(until, 0u64).eval(c).field();
        let both = c.mul(nonce0, live);
        c.assert_with(both, Some("EVM registration replay fields are noncanonical"));
        let both = c.mul(color0, amount0);
        c.assert_with(both, Some("EVM registration action fields must be inactive"));
        let both = c.mul(kind0, rcpt0);
        c.assert_with(both, Some("EVM registration recipient must be inactive"));
        let both = c.mul(to0, wnonce0);
        c.assert_with(both, Some("EVM registration targets must be inactive"));
        let both = c.mul(wcolor0, wamount0);
        let all = c.mul(both, credit0);
        c.assert_with(all, Some("EVM registration swap fields must be inactive"));
    });

    // selectors 2..6 — the actions' shared envelope.
    c.when(f.is_action, |c| {
        let acct_set = c.not(acct0);
        c.assert_with(acct_set, Some("action account must be supplied"));
        c.assert_with(salt0, Some("action account salt must be inactive"));
        c.when(f.is_native_authorized, |c| {
            c.assert_with(owner0, Some("native action owner must be inactive"));
            let both = c.mul(nonce0, until0);
            c.assert_with(both, Some("native action replay fields must be inactive"));
        });
        c.when(f.is_evm_authorized, |c| {
            let owner_set = c.not(owner0);
            c.assert_with(owner_set, Some("EVM action owner must be nonzero"));
            let live = gt(until, 0u64).eval(c).field();
            c.assert_with(live, Some("EVM action deadline must be nonzero"));
        });

        let is_withdraw = c.add(f.is2, f.is3);
        c.when(is_withdraw, |c| {
            let positive = gt(amount, 0u64).eval(c).field();
            c.assert_with(positive, Some("withdraw amount must be positive"));
            let in_range = le(kind, 1u64).eval(c).field();
            c.assert_with(in_range, Some("withdraw recipient kind is invalid"));
            // Kind 1 is the CONTRACT recipient — refused (the ledger's
            // effects check makes it unsatisfiable at these pins).
            c.assert_with(kind0, Some("withdraw to a contract recipient is not supported"));
            let rcpt_set = c.not(rcpt0);
            c.assert_with(rcpt_set, Some("withdraw recipient must be nonzero"));
            c.assert_with(to0, Some("withdraw transfer target must be inactive"));
            let both = c.mul(wnonce0, wcolor0);
            c.assert_with(both, Some("withdraw swap fields must be inactive"));
            let both = c.mul(wamount0, credit0);
            c.assert_with(both, Some("withdraw swap target must be inactive"));
        });

        let is_transfer = c.add(f.is4, f.is5);
        c.when(is_transfer, |c| {
            let positive = gt(amount, 0u64).eval(c).field();
            c.assert_with(positive, Some("internal transfer must be positive"));
            let both = c.mul(kind0, rcpt0);
            c.assert_with(both, Some("internal transfer recipient must be inactive"));
            let to_set = c.not(to0);
            c.assert_with(to_set, Some("internal transfer target must be supplied"));
            let both = c.mul(wnonce0, wcolor0);
            c.assert_with(both, Some("internal transfer swap fields must be inactive"));
            let both = c.mul(wamount0, credit0);
            c.assert_with(both, Some("internal transfer swap target must be inactive"));
        });

        let handled = c.add(is_withdraw, is_transfer);
        let is_swap_arm = c.not(handled);
        c.when(is_swap_arm, |c| {
            c.assert_with(f.is6, Some("unknown execute selector"));
            let positive = gt(amount, 0u64).eval(c).field();
            c.assert_with(positive, Some("swap must give a positive amount"));
            let in_range = le(kind, 2u64).eval(c).field();
            c.assert_with(in_range, Some("swap recipient kind is invalid"));
            // Kind 2 is the CONTRACT taker — refused.
            let user_only = le(kind, 1u64).eval(c).field();
            c.assert_with(user_only, Some("swap to a contract taker is not supported"));
            c.when(kind0, |c| {
                c.assert_with(rcpt0, Some("open swap recipient must be zero"));
            });
            let named = c.not(kind0);
            c.when(named, |c| {
                let rcpt_set = c.not(rcpt0);
                c.assert_with(rcpt_set, Some("named swap recipient must be nonzero"));
            });
            c.assert_with(to0, Some("swap transfer target must be inactive"));
            let want_positive = gt(want, 0u64).eval(c).field();
            c.assert_with(want_positive, Some("swap must want a positive amount"));
            let same = b32_eq(c, &p.primary_color.bytes(), &p.want_color.bytes());
            let distinct = c.not(same);
            c.assert_with(distinct, Some("swap legs must be different colours"));
            let credit_set = c.not(credit0);
            c.assert_with(credit_set, Some("swap credit account must be supplied"));
        });
    });
}

/// `evmStructHashFor(manager, payload)` — one branch per action shape, each
/// opening with its own frozen type hash. A circuit has no control flow, so
/// ALL FOUR keccak preimages are computed and the digest selected; the
/// `assert(p.selector == 6)` of the fall-through arm binds only when the
/// call reaches it (selector not in 0..5).
fn evm_struct_hash_for(
    c: &mut Circuit3,
    manager: &B32<Public>,
    p: &PublicPayload,
    f: &Flags,
) -> B32<Public> {
    c.region("eip712: struct hash", |c| {
        let owner_word = address_word(c, p.owner);
        let nonce_word = numeric_word(c, p.nonce);
        let until_word = numeric_word(c, p.valid_until);
        let amount_word = numeric_word(c, p.primary_amount);
        let kind_word = numeric_word(c, p.recipient_kind);
        let want_word = numeric_word(c, p.want_amount);

        // selector 1: Register(manager, account, owner, salt, validUntil).
        let register_type = b32_const(c, &REGISTER_TYPE);
        let sh_register = keccak_words(
            c,
            &[
                &register_type,
                manager,
                &p.account,
                &owner_word,
                &p.account_salt,
                &until_word,
            ],
        );

        // selectors 2/3: Withdraw*(manager, account, owner, nonce,
        // validUntil, color, amount, recipientKind, recipient).
        let ws = b32_const(c, &WITHDRAW_SHIELDED_TYPE);
        let wu = b32_const(c, &WITHDRAW_UNSHIELDED_TYPE);
        let withdraw_type = B32::cond_select(c, f.is2, &ws, &wu);
        let sh_withdraw = keccak_words(
            c,
            &[
                &withdraw_type,
                manager,
                &p.account,
                &owner_word,
                &nonce_word,
                &until_word,
                &p.primary_color.bytes(),
                &amount_word,
                &kind_word,
                &p.recipient,
            ],
        );

        // selectors 4/5: Transfer*(manager, account, owner, nonce,
        // validUntil, toAccount, color, amount).
        let ts = b32_const(c, &TRANSFER_SHIELDED_TYPE);
        let tu = b32_const(c, &TRANSFER_UNSHIELDED_TYPE);
        let transfer_type = B32::cond_select(c, f.is4, &ts, &tu);
        let sh_transfer = keccak_words(
            c,
            &[
                &transfer_type,
                manager,
                &p.account,
                &owner_word,
                &nonce_word,
                &until_word,
                &p.to_account,
                &p.primary_color.bytes(),
                &amount_word,
            ],
        );

        // selector 6: OpenSwap(manager, account, owner, nonce, validUntil,
        // color, amount, recipientKind, recipient, wantNonce, wantColor,
        // wantAmount, creditAccount).
        let open_swap_type = b32_const(c, &OPEN_SWAP_TYPE);
        let sh_swap = keccak_words(
            c,
            &[
                &open_swap_type,
                manager,
                &p.account,
                &owner_word,
                &nonce_word,
                &until_word,
                &p.primary_color.bytes(),
                &amount_word,
                &kind_word,
                &p.recipient,
                &p.want_nonce.bytes(),
                &p.want_color.bytes(),
                &want_word,
                &p.credit_account,
            ],
        );

        // The fall-through assert: binds when the digest chain is evaluated
        // (selector != 0) and no earlier branch matched.
        let is_withdraw = c.add(f.is2, f.is3);
        let is_transfer = c.add(f.is4, f.is5);
        let matched = {
            let a = c.add(f.is1, is_withdraw);
            c.add(a, is_transfer)
        };
        let fell_through = c.not(matched);
        let evaluated = c.not(f.is0);
        let binds = c.mul(evaluated, fell_through);
        c.when(binds, |c| {
            c.assert_with(f.is6, Some("EIP-712 selector must be 1..6"));
        });

        // digest = the branch that matched.
        let after_transfer = B32::cond_select(c, is_transfer, &sh_transfer, &sh_swap);
        let after_withdraw = B32::cond_select(c, is_withdraw, &sh_withdraw, &after_transfer);
        B32::cond_select(c, f.is1, &sh_register, &after_withdraw)
    })
}

/// `custodyDispatch(p, account)` — selectors 2..6 as ONE debit leg, ONE
/// credit leg and shared sends, with family, recipient, account and colour
/// muxed in. Emitted under the caller's `!isRegistration` guard (ambient).
fn custody_dispatch(c: &mut Circuit3, p: &PublicPayload, f: &Flags, account: &B32<Public>) {
    let is_transfer = c.add(f.is4, f.is5);
    let debit_shielded = {
        let a = c.add(f.is2, f.is4);
        c.add(a, f.is6)
    };
    let debit_unshielded = c.not(debit_shielded);
    let credit_shielded = c.add(f.is4, f.is6);
    let has_credit = c.add(is_transfer, f.is6);
    let needs_pool = c.add(f.is2, f.is6);

    let val = p.primary_amount;
    let val_u128 = Uint::<128, Public>::from_field_unchecked(val);

    // --- 0. swap parameter sanity ---
    c.when(f.is6, |c| {
        let positive = gt(val_u128, 0u64).eval(c).field();
        c.assert_with(positive, Some("swap must give a positive amount"));
        let want_positive = gt(
            Uint::<128, Public>::from_field_unchecked(p.want_amount),
            0u64,
        )
        .eval(c)
        .field();
        c.assert_with(want_positive, Some("swap must want a positive amount"));
        let same = b32_eq(c, &p.primary_color.bytes(), &p.want_color.bytes());
        let distinct = c.not(same);
        c.assert_with(distinct, Some("swap legs must be different colours"));
    });

    // --- 1. internal-transfer destination checks ---
    c.when(is_transfer, |c| {
        let known = MANAGER.accounts.member(c, &p.to_account).field();
        c.assert_with(known, Some("destination account is not registered"));
        let same = b32_eq(c, account, &p.to_account);
        let different = c.not(same);
        c.assert_with(different, Some("internal transfer to the same account"));
        let positive = gt(val_u128, 0u64).eval(c).field();
        c.assert_with(positive, Some("internal transfer must be positive"));
    });

    // --- 2. THE PER-(ACCOUNT, COLOUR) GUARD ---
    let shielded_tag = B32::pad(c, SHIELDED_FAMILY_TAG);
    let unshielded_tag = B32::pad(c, UNSHIELDED_FAMILY_TAG);
    let debit_tag = B32::cond_select(c, debit_shielded, &shielded_tag, &unshielded_tag);
    let debit_key = family_key(c, account, &p.primary_color, &debit_tag);
    // Each family's read fires under its arm and reads back ZERO on the
    // other, so the mux is one `add` of two values at most one of which is
    // live — no select chain.
    let zero = c.constant(0u64);
    let mut s_balance = zero;
    c.when(debit_shielded, |c| {
        s_balance = balance_at(c, &MANAGER.shielded_balances, &debit_key).stale(c);
    });
    let mut u_balance = zero;
    c.when(debit_unshielded, |c| {
        u_balance = balance_at(c, &MANAGER.unshielded_balances, &debit_key).stale(c);
    });
    let debit_balance = c.add(s_balance, u_balance);
    let covered = ge(
        Uint::<128, Public>::from_field_unchecked(debit_balance),
        val_u128,
    )
    .eval(c)
    .field();
    c.assert_with(covered, Some("account colour balance too low"));

    // --- 3. the pool guard and the shielded give leg (selectors 2 and 6) ---
    c.when(needs_pool, |c| {
        let pooled_present = MANAGER.pools.member(c, &p.primary_color).field();
        c.assert_with(pooled_present, Some("no pooled coin for this colour"));
        let pooled = MANAGER.pools.lookup(c, &p.primary_color);
        let pool_covers = ge(
            Uint::<128, Public>::from_field_unchecked(pooled.value),
            val_u128,
        )
        .eval(c)
        .field();
        c.assert_with(pool_covers, Some("pooled colour balance too low"));

        // THE CLAMP: on a run that reaches this block `safeGive == val`; on
        // a guarded-off run the zeroed pool read makes `pooled.value - val`
        // negative, and both change computations below must stay in range.
        let safe_give = c.cond_select(pool_covers, val, 0u64);

        // --- 4. the swap credit target, after the pool guard ---
        c.when(f.is6, |c| {
            let known = MANAGER.accounts.member(c, &p.credit_account).field();
            c.assert_with(known, Some("credit account is not registered"));
        });

        // The named-recipient send vs the open offer.
        let kind_named = {
            let k0 = c.test_eq(p.recipient_kind, 0u64);
            c.not(k0)
        };
        let send_arm = {
            let named = c.mul(f.is6, kind_named);
            c.add(f.is2, named)
        };
        c.when(send_arm, |c| {
            // ONE sendShielded shared by the withdrawal and the named-swap
            // shape; the recipient discriminant is muxed (withdraw kind 0 =
            // user key; named swap kind 1 = user key). Both arms carry the
            // same 32 recipient bytes, so the unused arm needs no zeroing.
            let k0 = c.test_eq(p.recipient_kind, 0u64);
            let k1 = c.test_eq(p.recipient_kind, 1u64);
            let use_left = c.cond_select(f.is2, k0, k1);
            // `p.recipient` is genuinely dual-use — a wallet key or a
            // contract address, selected by the kind bit — so BOTH arms
            // carry the same limbs and the wrap is per-arm.
            let recipient = CoinRecipient {
                is_left: use_left,
                left: minocrab_std::v3::ZswapCoinPublicKey(p.recipient),
                right: minocrab_std::v3::ContractAddress(p.recipient),
            };
            let result = kernel::send_shielded(
                c,
                &pooled,
                &recipient,
                Uint::<128, Public>::from_field_unchecked(safe_give),
            );
            // repoolOrRemove(col, result.change)
            let has_change = result.change.is_some.field();
            c.when(has_change, |c| {
                let me = kernel::self_address(c);
                let recipient = contract_recipient(c, me);
                MANAGER
                    .pools
                    .insert_coin(c, &p.primary_color, &result.change.value, &recipient);
            });
            let spent = c.not(has_change);
            c.when(spent, |c| {
                MANAGER.pools.remove(c, &p.primary_color);
            });
        });
        let open_arm = c.not(send_arm);
        c.when(open_arm, |c| {
            // THE OPEN OFFER: consume the pooled coin as a zswap input,
            // claim its nullifier, and create only the change back to this
            // contract — the released value stands as a positive imbalance.
            let me = kernel::self_address(c);
            // createZswapInput(pooled) — a Void witness native, nothing
            // in-circuit.
            let spent_coin = pooled.downcast();
            let nul = coin_nullifier_contract(c, &spent_coin, &me.bytes());
            kernel::claim_zswap_nullifier(c, &nul);

            // changeValue = (pooled.value - safeGive) as Uint<128>, with
            // Compact's subtraction guard folded into this branch.
            let in_range = ge(
                Uint::<128, Public>::from_field_unchecked(pooled.value),
                Uint::<128, Public>::from_field_unchecked(safe_give),
            )
            .eval(c)
            .field();
            c.assert_with(in_range, Some("result of subtraction would be negative"));
            let neg = c.neg(safe_give);
            let change_value = c.add(pooled.value, neg);

            let change0 = c.test_eq(change_value, 0u64);
            c.when(change0, |c| {
                MANAGER.pools.remove(c, &p.primary_color);
            });
            let has_change = c.not(change0);
            c.when(has_change, |c| {
                // changeCoin.nonce = evolveNonce(2, pooled.nonce) —
                // transientHash<Vector<3, Field>>([tag, 2, degrade(nonce)]).
                let tag = c.constant(
                    Fr::from_le_bytes(b"midnight:kernel:nonce_evolve").expect("28 bytes fit"),
                );
                let two = c.constant(2u64);
                let evolved = c.transient_hash(&[tag, two, pooled.nonce.bytes().lo]);
                let (_overflow, lo) = c.div_mod_power_of_two(evolved, 248);
                let zero = c.constant(0u64);
                let change_coin = ShieldedCoinInfo3 {
                    nonce: CoinNonce(B32 { hi: zero, lo }),
                    color: p.primary_color,
                    value: change_value,
                };
                // createZswapOutput(changeCoin, right(self)) — Void witness.
                let cm = coin_commitment_to_contract(c, &change_coin, &me.bytes());
                kernel::claim_zswap_coin_spend(c, &cm);
                kernel::claim_zswap_coin_receive(c, &cm);
                // repoolOrRemove(col, some(changeCoin)) — its own self read.
                let me2 = kernel::self_address(c);
                let recipient = contract_recipient(c, me2);
                MANAGER
                    .pools
                    .insert_coin(c, &p.primary_color, &change_coin, &recipient);
            });
        });
    });

    // --- the unshielded give leg (selector 3) ---
    c.when(f.is3, |c| {
        let funded = kernel::unshielded_balance_gte(c, p.primary_color, val_u128);
        c.assert(is_true(funded).message("contract unshielded balance too low"));
        // sendUnshielded's recipient is Either<ContractAddress, UserAddress>:
        // LEFT = contract, RIGHT = user; envelope kind 0 = user key. The
        // UNUSED arm must be the type default (zero) — the claim embeds both
        // arms' bytes in the effects transcript, so this is PI-visible.
        let k0 = c.test_eq(p.recipient_kind, 0u64);
        let is_left = c.not(k0);
        let zero = c.constant(0u64);
        let left = B32 {
            hi: c.cond_select(k0, zero, p.recipient.hi),
            lo: c.cond_select(k0, zero, p.recipient.lo),
        };
        let right = B32 {
            hi: c.cond_select(k0, p.recipient.hi, zero),
            lo: c.cond_select(k0, p.recipient.lo, zero),
        };
        let recipient = Either {
            is_left: Bool::from_field_unchecked(is_left),
            left: ContractAddress(left),
            right: UserAddress(right),
        };
        kernel::send_unshielded(c, p.primary_color, val_u128, &recipient);
    });

    // --- ONE debit write, into the muxed family ---
    let covered_again = ge(
        Uint::<128, Public>::from_field_unchecked(debit_balance),
        val_u128,
    )
    .eval(c)
    .field();
    c.assert_with(covered_again, Some("result of subtraction would be negative"));
    let neg_val = c.neg(val);
    let new_debit_raw = c.add(debit_balance, neg_val);
    let new_debit = Uint::<128, Public>::from_field_unchecked(new_debit_raw);
    new_debit.constrain_input(c);
    c.when(debit_shielded, |c| {
        MANAGER.shielded_balances.insert(c, &debit_key, &new_debit);
    });
    c.when(debit_unshielded, |c| {
        MANAGER.unshielded_balances.insert(c, &debit_key, &new_debit);
    });

    // --- the swap WANT leg: claim wantCoin into custody ---
    c.when(f.is6, |c| {
        let want_coin = ShieldedCoinInfo3 {
            nonce: p.want_nonce,
            color: p.want_color,
            value: p.want_amount,
        };
        // Kept even though guard threading no longer uses it: dropping this
        // `Copy` would renumber every later identifier, moving the ZKIR
        // (notes/edsl-trim.org §B, the removal's zero-movement gate).
        let _ = c.constant(1u64);
        common::receive_shielded(c, &want_coin);
        let member = MANAGER.pools.member(c, &p.want_color).field();
        c.when(member, |c| {
            let pooled = MANAGER.pools.lookup(c, &p.want_color);
            let merged = kernel::merge_coin_immediate(c, &pooled, &want_coin);
            let me = kernel::self_address(c);
            let recipient = contract_recipient(c, me);
            MANAGER
                .pools
                .insert_coin(c, &p.want_color, &merged, &recipient);
        });
        let fresh = c.not(member);
        c.when(fresh, |c| {
            let me = kernel::self_address(c);
            let recipient = contract_recipient(c, me);
            MANAGER
                .pools
                .insert_coin(c, &p.want_color, &want_coin, &recipient);
        });
    });

    // --- ONE credit write (selectors 4, 5, 6) ---
    c.when(has_credit, |c| {
        let credit_acct = B32::cond_select(c, f.is6, &p.credit_account, &p.to_account);
        let credit_colour = CoinColor::cond_select(c, f.is6, &p.want_color, &p.primary_color);
        let credit_tag = B32::cond_select(c, credit_shielded, &shielded_tag, &unshielded_tag);
        let credit_key = family_key(c, &credit_acct, &credit_colour, &credit_tag);
        let credit_value = c.cond_select(f.is6, p.want_amount, val);
        c.when(credit_shielded, |c| {
            let prior = balance_at(c, &MANAGER.shielded_balances, &credit_key).stale(c);
            let sum = c.add(prior, credit_value);
            let new_credit = Uint::<128, Public>::from_field_unchecked(sum);
            new_credit.constrain_input(c);
            MANAGER.shielded_balances.insert(c, &credit_key, &new_credit);
        });
        let credit_unshielded = c.not(credit_shielded);
        c.when(credit_unshielded, |c| {
            let prior = balance_at(c, &MANAGER.unshielded_balances, &credit_key).stale(c);
            let sum = c.add(prior, credit_value);
            let new_credit = Uint::<128, Public>::from_field_unchecked(sum);
            new_credit.constrain_input(c);
            MANAGER
                .unshielded_balances
                .insert(c, &credit_key, &new_credit);
        });
    });
}
