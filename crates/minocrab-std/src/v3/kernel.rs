//! Compact's `kernel` ADT, and the token stdlib circuits built on it (M17,
//! notes/kernel-tokens.org).
//!
//! TWO LAYERS wearing one name, and the split is the milestone's main
//! structural finding:
//!
//! | layer | what it is | here |
//! |---|---|---|
//! | KERNEL PRIMITIVES | `declare-ledger-adt Kernel` functions with vm-code | [`mint_unshielded`](crate::v3::kernel::mint_unshielded) … [`block_time_greater_than`](crate::v3::kernel::block_time_greater_than) |
//! | STDLIB CIRCUITS | ordinary `export circuit`s written IN COMPACT, composed from those | [`send_unshielded`](crate::v3::kernel::send_unshielded) … [`unshielded_balance_lte`](crate::v3::kernel::unshielded_balance_lte) |
//!
//! The second layer is `standard-library.compact:113-350` transcribed. Each
//! function below carries the Compact it is a port of, and the bodies are
//! deliberately as close to it as Rust allows — these are the circuits whose
//! *composition* is the specification, and a reader should be able to check
//! them against the Compact source line by line.
//!
//! `kernel.checkpoint()` IS ABSENT. compactc's ZKIR-v3 backend cannot compile
//! it at all (`assemble1` has no `ckpt` case, so `--feature-zkir-v3` on a
//! contract calling it fails with `assert not-implemented`); the v2 backend
//! assembles it to `255`. It is a v2-only feature, so there is no artifact to
//! agree with and nothing here to agree with it — see
//! notes/kernel-tokens.org finding (a).
//!
//! THE BALANCE CAVEAT, which is Compact's own and worth repeating: the
//! balance these functions read is the contract's balance at the START of
//! execution. Unshielded sends, receives and mints inside the same circuit do
//! NOT feed back into it. `unshieldedBalance` also imposes exact-match
//! semantics at apply time, so the comparison forms are usually what a
//! contract wants.

use minocrab::v3::{AnyWire3, Circuit3, FieldT, Wire3};
use minocrab::{AlignmentAtom, Fr, Private, Public};
use minocrab_ledger::{
    emit, kernel_balance, kernel_block_time, kernel_claim_unshielded_coin_spend,
    kernel_claim_zswap_coin_receive, kernel_claim_zswap_coin_spend, kernel_claim_zswap_nullifier,
    kernel_inc_unshielded_inputs, kernel_inc_unshielded_outputs, kernel_mint_shielded,
    kernel_mint_unshielded, kernel_self, BalanceCmp, ImpactElem, LedgerValue,
};

use super::assumed::Assumed;
use super::hash;
use super::ledger::LedgerRepr;
use super::predicate::is_true;
use super::{Select, 
    coin_commitment_to, coin_commitment_to_contract, coin_nullifier_contract, Bool, CoinColor,
    CoinNonce, CoinRecipient, ContractAddress, Either, Maybe, QualifiedShieldedCoinInfo3,
    ShieldedCoinInfo3, ShieldedSendResult, TokenDomainSeparator, Uint, UserAddress, B32,
};

/// Compact's `TokenType` — `Either<Bytes<32>, Bytes<32>>`.
pub type TokenType<V = Public> = Either<B32<V>, B32<V>, V>;

/// Compact's `UnshieldedRecipient` — `Either<ContractAddress, UserAddress>`.
pub type UnshieldedRecipient<V = Public> = Either<ContractAddress<V>, UserAddress<V>, V>;

/// `left<Bytes<32>, Bytes<32>>(color)` — an unshielded token type, which is
/// the ONLY `TokenType` Compact's own stdlib ever builds.
///
/// A distinct type rather than a [`TokenType`], and the reason is the
/// instruction stream. Four of the five FAB limbs of `left(color)` are
/// CONSTANT — the `is_left` tag and the unused right arm's two — and compactc
/// inlines all four into the Impact `push`. Routing them through
/// [`LedgerRepr`] would name each with a `copy`, which is
/// the named-immediate gap M15 recorded for ledger VALUE positions and left
/// as dmd's call.
///
/// This closes it where it can be closed WITHOUT that API change: an
/// `UnshieldedToken` knows its own constants, so it builds its `LedgerValue`
/// with [`ImpactElem::Imm`] directly and never asks the trait for a wire that
/// does not exist. A `TokenType` whose tag is computed still goes the ordinary
/// way — the general `Either` impl is untouched.
#[derive(Clone, Copy)]
pub struct UnshieldedToken<V: super::Vis3 = Public>(pub B32<V>);

/// `left<Bytes<32>, Bytes<32>>(color)`.
pub fn unshielded(_c: &mut Circuit3, color: CoinColor<Public>) -> UnshieldedToken<Public> {
    UnshieldedToken(color.bytes())
}

impl UnshieldedToken<Public> {
    /// The five FAB limbs, three of them inline constants: `[1, hi, lo, 0, 0]`
    /// under `[bytes<1>, bytes<32>, bytes<32>]`.
    pub fn ledger_value(&self) -> LedgerValue {
        LedgerValue::new(
            vec![
                AlignmentAtom::Bytes { length: 1 },
                AlignmentAtom::Bytes { length: 32 },
                AlignmentAtom::Bytes { length: 32 },
            ],
            vec![
                ImpactElem::Imm(Fr::from(1u64)),
                ImpactElem::Wire(self.0.hi),
                ImpactElem::Wire(self.0.lo),
                ImpactElem::Imm(Fr::from(0u64)),
                ImpactElem::Imm(Fr::from(0u64)),
            ],
        )
    }
}

// ---- the kernel primitives --------------------------------------------------

/// The cached `kernel.self()` answer — populated ONLY by
/// [`cache_self_address`], parked in the circuit's gadget scratch state
/// under this private type so nothing outside this module can touch it.
struct CachedSelfAddress(SelfAddress);

/// `kernel.self()` as a PROOF OF SELF — a value only the three
/// `self_address*` readers produce, because `ContractAddress<Public>` is
/// Compact's value type and is built from any `B32` (recipients, `Either`
/// arms, call targets), so it cannot carry that meaning. A helper that
/// means "mint to / burn from / notify AS this contract" takes a
/// `SelfAddress`; anything that merely wants an address takes
/// `.address()`. Zero rows: the same two limbs. (External review §4.5 and
/// notes/api-safety-survey.org §3 item 5.)
#[derive(Clone, Copy)]
pub struct SelfAddress(ContractAddress<Public>);

impl SelfAddress {
    /// The address, as the value type every other API takes.
    pub fn address(self) -> ContractAddress<Public> {
        self.0
    }

    /// [`ContractAddress::bytes`].
    pub fn bytes(self) -> B32<Public> {
        self.0.bytes()
    }

    /// [`ContractAddress::private`] — forget it is public and self.
    pub fn private(self) -> ContractAddress<Private> {
        self.0.private()
    }
}

impl From<SelfAddress> for ContractAddress<Public> {
    fn from(me: SelfAddress) -> Self {
        me.0
    }
}

/// A guarded self-address read is still a self-address where the guard
/// held (and the zero address where it did not) — `Guarded::or` needs this.
impl Select<Public> for SelfAddress {
    fn select(c: &mut Circuit3, bit: Wire3<FieldT, Public>, a: Self, b: Self) -> Self {
        SelfAddress(Select::select(c, bit, a.0, b.0))
    }
}

/// `kernel.self()` — the contract's own address. Reads fresh, unless this
/// circuit earlier called [`cache_self_address`], in which case the cached
/// wires come back and no read is emitted.
///
/// A circuit that never caches CANNOT be affected: nothing else populates
/// the cache, so the compat ports' per-call-site reads (compactc parity)
/// are reproduced by construction, not by discipline.
pub fn self_address(c: &mut Circuit3) -> SelfAddress {
    if let Some(cached) = c.ext_get::<CachedSelfAddress>() {
        return cached.0;
    }
    let wires = kernel_self(c);
    SelfAddress(ContractAddress::from_limbs(never_stale(c, wires)))
}

/// The kernel's self read is a `popeq` on a value no transaction can change,
/// so it is acknowledged at the read and never wears `Assumed` (M42 B).
fn never_stale(c: &mut Circuit3, wires: [Wire3<FieldT, Public>; 2]) -> [Wire3<FieldT, Public>; 2] {
    c.acknowledge_stale(&[wires[0].val(), wires[1].val()]);
    wires
}

/// Read `kernel.self()` ONCE and make it the ambient answer for every
/// later [`self_address`] call in this circuit (M18).
///
/// The soundness paragraph is M10 rung i's, unchanged: the address is
/// constant for the transaction and read count is FRAMING, not protocol —
/// every read that IS emitted still reconciles through the ledger's
/// `process_read`. This is the typed CSE notes/ir-passes.org §3 assigns to
/// a gadget rather than a pass: the caller states the intent once, at the
/// top of the circuit, instead of threading the address through every
/// helper (`…_with` twins) — and a circuit whose helpers make their OWN
/// reads today must keep plain [`self_address`], because the cache would
/// swallow those reads and move the stream (the dump gate enforces this
/// per circuit).
///
/// A `kernel.self()` read inside [`Circuit3::when`] / [`Circuit3::when_private`]
/// picks up the ambient scope automatically and never consults the cache —
/// `c.when(g, |c| self_address(c)).or_default()` is the guarded read
/// (notes/edsl-trim.org §B).
pub fn cache_self_address(c: &mut Circuit3) -> SelfAddress {
    let wires = kernel_self(c);
    let me = SelfAddress(ContractAddress::from_limbs(never_stale(c, wires)));
    c.ext_insert(CachedSelfAddress(me));
    me
}

/// `kernel.mintShielded(domain_sep, amount)` — effects\[4\].
pub fn mint_shielded(c: &mut Circuit3, domain_sep: &TokenDomainSeparator<Public>, amount: Uint<64, Public>) {
    let (ds, amt) = (domain_sep.bytes().ledger_value(c), amount.ledger_value(c));
    emit(c, &kernel_mint_shielded(&ds, &amt));
}

/// `kernel.mintUnshielded(domain_sep, amount)` — effects\[5\], and the same
/// accumulator shape [`mint_shielded`] is.
pub fn mint_unshielded(c: &mut Circuit3, domain_sep: &TokenDomainSeparator<Public>, amount: Uint<64, Public>) {
    let (ds, amt) = (domain_sep.bytes().ledger_value(c), amount.ledger_value(c));
    emit(c, &kernel_mint_unshielded(&ds, &amt));
}

/// `kernel.incUnshieldedInputs(token_type, amount)` — effects\[6\]. Called when
/// the contract RECEIVES an unshielded token.
pub fn inc_unshielded_inputs(
    c: &mut Circuit3,
    token: &UnshieldedToken<Public>,
    amount: Uint<128, Public>,
) {
    let (t, amt) = (token.ledger_value(), amount.ledger_value(c));
    emit(c, &kernel_inc_unshielded_inputs(&t, &amt));
}

/// `kernel.incUnshieldedOutputs(token_type, amount)` — effects\[7\]. Called when
/// the contract SENDS one.
pub fn inc_unshielded_outputs(
    c: &mut Circuit3,
    token: &UnshieldedToken<Public>,
    amount: Uint<128, Public>,
) {
    let (t, amt) = (token.ledger_value(), amount.ledger_value(c));
    emit(c, &kernel_inc_unshielded_outputs(&t, &amt));
}

/// `kernel.claimUnshieldedCoinSpend(token_type, recipient, amount)` —
/// effects\[8\]. Authorizes a transfer; the key is the token type and the
/// recipient TOGETHER, so the two travel as one six-atom value.
pub fn claim_unshielded_coin_spend(
    c: &mut Circuit3,
    token: &UnshieldedToken<Public>,
    recipient: &UnshieldedRecipient<Public>,
    amount: Uint<128, Public>,
) {
    let key = concat_values(token.ledger_value(), recipient.ledger_value(c));
    let amt = amount.ledger_value(c);
    emit(c, &kernel_claim_unshielded_coin_spend(&key, &amt));
}

/// The two halves of `claimUnshieldedCoinSpend`'s key, side by side in one
/// `LedgerValue` — which is what the single `push` in its stream carries.
fn concat_values(a: LedgerValue, b: LedgerValue) -> LedgerValue {
    let mut atoms = a.atoms().to_vec();
    let mut elems = a.elems().to_vec();
    atoms.extend_from_slice(b.atoms());
    elems.extend_from_slice(b.elems());
    LedgerValue::new(atoms, elems)
}

/// `kernel.balance(token_type)` — the contract's balance of an unshielded
/// token, or ZERO if it has never held one. See the module docs for what
/// "balance" means here.
pub fn balance(c: &mut Circuit3, token: &UnshieldedToken<Public>) -> Assumed<Uint<128, Public>> {
    let t = token.ledger_value();
    Assumed::of_read(Uint::from_field_unchecked(kernel_balance(c, &t, BalanceCmp::Value, None)))
}

/// `kernel.balanceLessThan(token_type, amount)`.
pub fn balance_less_than(
    c: &mut Circuit3,
    token: &UnshieldedToken<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let (t, amt) = (token.ledger_value(), amount.ledger_value(c));
    Assumed::of_read(Bool::from_field_unchecked(kernel_balance(c, &t, BalanceCmp::LessThan, Some(&amt))))
}

/// `kernel.balanceGreaterThan(token_type, amount)`.
pub fn balance_greater_than(
    c: &mut Circuit3,
    token: &UnshieldedToken<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let (t, amt) = (token.ledger_value(), amount.ledger_value(c));
    Assumed::of_read(Bool::from_field_unchecked(kernel_balance(c, &t, BalanceCmp::GreaterThan, Some(&amt))))
}

/// `kernel.blockTimeLessThan(t)` — whether the block time is before `t`.
pub fn block_time_less_than(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    let t = time.ledger_value(c);
    Assumed::of_read(Bool::from_field_unchecked(kernel_block_time(c, &t, false)))
}

/// `kernel.blockTimeGreaterThan(t)`.
pub fn block_time_greater_than(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    let t = time.ledger_value(c);
    Assumed::of_read(Bool::from_field_unchecked(kernel_block_time(c, &t, true)))
}

// ---- the stdlib circuits ----------------------------------------------------
//
// standard-library.compact:275-350, transcribed. Each is a composition of the
// primitives above and nothing else.

/// `circuit blockTimeLt(time): Boolean { return kernel.blockTimeLessThan(time); }`
pub fn block_time_lt(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    block_time_less_than(c, time)
}

/// `circuit blockTimeGte(time): Boolean { return !blockTimeLt(time); }`
pub fn block_time_gte(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    let lt = block_time_lt(c, time);
    Assumed::of_read(not(c, lt.into_inner()))
}

/// `circuit blockTimeGt(time): Boolean { return kernel.blockTimeGreaterThan(time); }`
pub fn block_time_gt(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    block_time_greater_than(c, time)
}

/// `circuit blockTimeLte(time): Boolean { return !blockTimeGt(time); }`
pub fn block_time_lte(c: &mut Circuit3, time: Uint<64, Public>) -> Assumed<Bool<Public>> {
    let gt = block_time_gt(c, time);
    Assumed::of_read(not(c, gt.into_inner()))
}

/// Compact's `!b` on a Boolean, which compactc lowers to
/// `cond_select(b, 0, 1)` rather than to an arithmetic negation — the shape
/// the fixture's `sBlockTimeGte` shows.
fn not(c: &mut Circuit3, b: Bool<Public>) -> Bool<Public> {
    Bool::from_field_unchecked(c.cond_select(b.field(), 0u64, 1u64))
}

/// `circuit unshieldedBalance(color): Uint<128>`
pub fn unshielded_balance(c: &mut Circuit3, color: CoinColor<Public>) -> Assumed<Uint<128, Public>> {
    let token = unshielded(c, color);
    balance(c, &token)
}

/// `circuit unshieldedBalanceLt(color, amount): Boolean`
pub fn unshielded_balance_lt(
    c: &mut Circuit3,
    color: CoinColor<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let token = unshielded(c, color);
    balance_less_than(c, &token, amount)
}

/// `circuit unshieldedBalanceGte(color, amount): Boolean { return !…Lt(…); }`
pub fn unshielded_balance_gte(
    c: &mut Circuit3,
    color: CoinColor<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let lt = unshielded_balance_lt(c, color, amount);
    Assumed::of_read(not(c, lt.into_inner()))
}

/// `circuit unshieldedBalanceGt(color, amount): Boolean`
pub fn unshielded_balance_gt(
    c: &mut Circuit3,
    color: CoinColor<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let token = unshielded(c, color);
    balance_greater_than(c, &token, amount)
}

/// `circuit unshieldedBalanceLte(color, amount): Boolean { return !…Gt(…); }`
pub fn unshielded_balance_lte(
    c: &mut Circuit3,
    color: CoinColor<Public>,
    amount: Uint<128, Public>,
) -> Assumed<Bool<Public>> {
    let gt = unshielded_balance_gt(c, color, amount);
    Assumed::of_read(not(c, gt.into_inner()))
}

/// ```text
/// circuit receiveUnshielded(color, amount): [] {
///   kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
/// }
/// ```
pub fn receive_unshielded(c: &mut Circuit3, color: CoinColor<Public>, amount: Uint<128, Public>) {
    let token = unshielded(c, color);
    inc_unshielded_inputs(c, &token, amount);
}

/// `recipient.is_left && recipient.left.bytes == kernel.self().bytes` — the
/// AUTO-RECEIVE guard both [`send_unshielded`] and [`mint_unshielded_token`]
/// end with, and the reason each of them is more than a pair of effects.
///
/// Two things about its shape, both compactc's and both visible in the
/// fixture. The `kernel.self()` read is guarded by `is_left` ALONE — a
/// recipient that is a user address never needs the contract's own address,
/// so the read is skipped and its `public_input` gates yield the default.
/// And the conjunction is two `cond_select`s rather than a multiplication,
/// because that is how compactc lowers `&&` on Booleans.
fn is_self(c: &mut Circuit3, recipient: &UnshieldedRecipient<Public>) -> Wire3<FieldT, Public> {
    let is_left = recipient.is_left.field();
    let me = guarded_kernel_self(c, is_left);
    let me = never_stale(c, me);
    let left = recipient.left.bytes();
    let eq_hi = c.test_eq(left.hi, me[0]);
    let eq_lo = c.test_eq(left.lo, me[1]);
    let both = c.cond_select(eq_hi, eq_lo, 0u64);
    c.cond_select(is_left, both, 0u64)
}

/// [`minocrab_ledger::kernel_self`], guarded by an EXPLICIT wire rather than
/// the ambient scope.
///
/// Not spelled `c.when(is_left, |c| kernel_self(c)).or_default()`: both
/// [`send_unshielded`] and [`mint_unshielded_token`] are called from inside
/// another `c.when` at some corpus call sites (e.g. `manager.compact`'s
/// `execute`), and the scope conjoins the two guards ONCE on entry
/// (`Circuit3::when`'s doc) where the deleted `kernel_self_guarded` conjoined
/// PER EFFECT (`Circuit3::effect_guard`, once per read and once for the
/// Impact op) — fewer rows there, so not zero-movement. This reproduces the
/// same op sequence [`minocrab_ledger::kernel_self`] does, through the core
/// primitives that resolve the guard the same way regardless of nesting.
fn guarded_kernel_self(c: &mut Circuit3, guard: Wire3<FieldT, Public>) -> [Wire3<FieldT, Public>; 2] {
    let atoms = vec![AlignmentAtom::Bytes { length: 32 }];
    let limbs: usize = atoms.iter().map(minocrab_ledger::atom_limbs).sum();
    let wires: Vec<Wire3<FieldT, Public>> = (0..limbs)
        .map(|_| c.public_transcript_input_guarded::<FieldT, Public>(guard))
        .collect();
    let value = LedgerValue::new(atoms, wires.iter().map(|&w| ImpactElem::Wire(w)).collect());
    for op in [
        minocrab_ledger::dup(2),
        minocrab_ledger::idx_one(true, false, 0),
        minocrab_ledger::popeq(true, &value),
    ] {
        c.impact_mixed(guard, &op.0);
    }
    [wires[0], wires[1]]
}

/// Emit `ops` under an EXPLICIT guard, resolved against the ambient scope
/// PER OP — [`Circuit3::impact_mixed`] directly, once per op, which is what
/// the deleted `minocrab_ledger::emit(c, guard, ops)` did. See
/// [`guarded_kernel_self`] for why this is not `c.when(guard, |c| ..)`.
fn emit_guarded(c: &mut Circuit3, guard: Wire3<FieldT, Public>, ops: &[minocrab_ledger::ImpactOp]) {
    for op in ops {
        c.impact_mixed(guard, &op.0);
    }
}

/// ```text
/// circuit sendUnshielded(color, amount, recipient): [] {
///   kernel.incUnshieldedOutputs(left<Bytes<32>, Bytes<32>>(color), amount);
///   kernel.claimUnshieldedCoinSpend(left<Bytes<32>, Bytes<32>>(color), recipient, amount);
///   // Auto-receive when sending to self
///   if (recipient.is_left && recipient.left.bytes == kernel.self().bytes) {
///     kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
///   }
/// }
/// ```
pub fn send_unshielded(
    c: &mut Circuit3,
    color: CoinColor<Public>,
    amount: Uint<128, Public>,
    recipient: &UnshieldedRecipient<Public>,
) {
    let token = unshielded(c, color);
    inc_unshielded_outputs(c, &token, amount);
    claim_unshielded_coin_spend(c, &token, recipient, amount);
    let mine = is_self(c, recipient);
    let t = token.ledger_value();
    let amt = amount.ledger_value(c);
    emit_guarded(c, mine, &minocrab_ledger::kernel_inc_unshielded_inputs(&t, &amt));
}

/// ```text
/// circuit mintUnshieldedToken(domainSep, amount, recipient): Bytes<32> {
///   kernel.mintUnshielded(domainSep, amount);
///   const color = tokenType(domainSep, kernel.self());
///   kernel.claimUnshieldedCoinSpend(left<Bytes<32>, Bytes<32>>(color), recipient, amount);
///   // Auto-receive when minting to self
///   if (recipient.is_left && recipient.left.bytes == kernel.self().bytes) {
///     kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
///   }
///   return color;
/// }
/// ```
///
/// Note the amount is a `Uint<64>` at the mint and a `Uint<128>` at the
/// claim — Compact widens it, and so does this.
pub fn mint_unshielded_token(
    c: &mut Circuit3,
    domain_sep: &TokenDomainSeparator<Public>,
    amount: Uint<64, Public>,
    recipient: &UnshieldedRecipient<Public>,
) -> CoinColor<Public> {
    mint_unshielded(c, domain_sep, amount);
    let me = self_address(c);
    let color = super::token_type(c, domain_sep, &me.bytes());
    let token = unshielded(c, color);
    let wide = Uint::<128, Public>::from_field_unchecked(amount.field());
    claim_unshielded_coin_spend(c, &token, recipient, wide);
    let mine = is_self(c, recipient);
    let t = token.ledger_value();
    let amt = wide.ledger_value(c);
    emit_guarded(c, mine, &minocrab_ledger::kernel_inc_unshielded_inputs(&t, &amt));
    color
}

// ---- the SHIELDED half ------------------------------------------------------
//
// The zswap primitives and the three stdlib circuits built from them. What
// makes this half longer than the unshielded one is not the kernel — the three
// claims below are the same accumulator shape as the rest — but the COIN
// ALGEBRA between them: a nonce is evolved, a commitment is hashed, a value is
// split into what is sent and what comes back as change.
//
// Two shapes recur, and both are compactc's rather than ours:
//
//   - A coin paid to THIS contract is `right(kernel.self())`, a literal, so
//     its commitment has no recipient select at all
//     (`coin_commitment_to_contract`).
//   - `upgradeFromTransient(transientHash([<tag>, degradeToTransient(nonce)]))`
//     is how every derived nonce is made; the tag is inline and the two
//     `Copy`s are the casts (`hash::degrade_to_transient`).

/// `kernel.claimZswapNullifier(nul)` — effects\[0\]. Says this contract spent
/// the coin that nullifier names.
pub fn claim_zswap_nullifier(c: &mut Circuit3, nullifier: &B32<Public>) {
    let nul = nullifier.ledger_value(c);
    emit(c, &kernel_claim_zswap_nullifier(&nul));
}

/// `kernel.claimZswapCoinSpend(cm)` — effects\[2\]. Says this contract
/// AUTHORIZED the output that commitment names.
pub fn claim_zswap_coin_spend(c: &mut Circuit3, commitment: &B32<Public>) {
    let cm = commitment.ledger_value(c);
    emit(c, &kernel_claim_zswap_coin_spend(&cm));
}

/// `kernel.claimZswapCoinReceive(cm)` — effects\[1\]. Says this contract now
/// OWNS the coin that commitment names. Separate from the spend claim because
/// a contract paying itself makes both.
pub fn claim_zswap_coin_receive(c: &mut Circuit3, commitment: &B32<Public>) {
    let cm = commitment.ledger_value(c);
    emit(c, &kernel_claim_zswap_coin_receive(&cm));
}

/// The domain a coin's successor nonce is derived under, and the `/2` variant
/// `sendShielded` gives its CHANGE coin — two coins come out of one input, so
/// they cannot share a nonce.
const NONCE_EVOLVE: &[u8] = b"midnight:kernel:nonce_evolve";
const NONCE_EVOLVE_CHANGE: &[u8] = b"midnight:kernel:nonce_evolve/2";

/// `upgradeFromTransient(transientHash<Vector<2, Field>>([<domain> as Field,
/// degradeToTransient(nonce)]))` — the nonce of a coin derived from another.
///
/// Not the stdlib's `evolveNonce`, which hashes an INDEX as well; this is the
/// two-element form `sendShielded` and `mergeCoin` write inline.
fn derived_nonce(c: &mut Circuit3, domain: &[u8], nonce: &CoinNonce<Public>) -> CoinNonce<Public> {
    let degraded = hash::degrade_to_transient(c, &nonce.bytes());
    let h = c.transient_hash(&[
        AnyWire3::immediate(super::short_literal_imm(domain)),
        degraded.erase(),
    ]);
    CoinNonce(hash::upgrade_from_transient(c, h))
}

/// `a == b` on `Bytes<32>`, as compactc lowers it: a `test_eq` per limb and
/// the `&&` of the two, which is one `cond_select` and not a `mul`.
fn bytes_eq(c: &mut Circuit3, a: &B32<Public>, b: &B32<Public>) -> Wire3<FieldT, Public> {
    let hi = c.test_eq(a.hi, b.hi);
    let lo = c.test_eq(a.lo, b.lo);
    c.cond_select(hi, lo, 0u64)
}

/// Compact's `a - b` on a `Uint<128>`: the difference, and the assertion that
/// there is one — a subtraction that would go below zero is a failed proof,
/// not a wrap.
fn checked_sub(
    c: &mut Circuit3,
    a: Wire3<FieldT, Public>,
    b: Wire3<FieldT, Public>,
) -> Wire3<FieldT, Public> {
    let underflow = c.less_than(a, b, 128);
    let ok = not(c, Bool::from_field_unchecked(underflow));
    c.assert(is_true(ok).message("subtraction would underflow"));
    let neg = c.neg(b);
    c.add(a, neg)
}

/// Compact's `x as Uint<128>` on a value just computed: the range constraint,
/// then the `Copy` the cast names its result with.
fn as_uint128(c: &mut Circuit3, w: Wire3<FieldT, Public>) -> Wire3<FieldT, Public> {
    // Inside a `when` the checked value is the selected one; that is the
    // value the cast names and everything downstream (the commitment, the
    // ledger op) consumes — compactc's branch semantics, and what keeps the
    // hash preimage provably bounded for the taint lint.
    let checked = Uint::<128, Public>::from_field_checked(c, w);
    c.copy(checked.field())
}

/// ```text
/// circuit mergeCoin(a: QualifiedShieldedCoinInfo, b: QualifiedShieldedCoinInfo): ShieldedCoinInfo {
///   const selfAddr = kernel.self();
///   createZswapInput(a);
///   kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(a), selfAddr));
///   createZswapInput(b);
///   kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(b), selfAddr));
///   assert(a.color == b.color, "Can only merge coins of the same color");
///   const newCoin = ShieldedCoinInfo{
///     nonce: upgradeFromTransient(transientHash<Vector<2, Field>>([
///              "midnight:kernel:nonce_evolve" as Field, degradeToTransient(a.nonce)])),
///     color: a.color,
///     value: (a.value + b.value) as Uint<128>
///   };
///   createZswapOutput(newCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
///   const cm = coinCommitment(newCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
///   kernel.claimZswapCoinSpend(cm);
///   kernel.claimZswapCoinReceive(cm);
///   return newCoin;
/// }
/// ```
///
/// `createZswapInput`/`createZswapOutput` are Void witness natives — they tell
/// the off-circuit builder to put the coin in the transaction's offer and emit
/// NOTHING here, which is why two coins going in cost only their two
/// nullifiers.
pub fn merge_coin(
    c: &mut Circuit3,
    a: &QualifiedShieldedCoinInfo3<Public>,
    b: &QualifiedShieldedCoinInfo3<Public>,
) -> ShieldedCoinInfo3<Public> {
    merge(c, &a.downcast(), &b.downcast())
}

/// ```text
/// circuit mergeCoinImmediate(a: QualifiedShieldedCoinInfo, b: ShieldedCoinInfo): ShieldedCoinInfo {
///   return mergeCoin(a, upcastQualifiedCoin(b));
/// }
/// ```
///
/// `upcastQualifiedCoin` sets `mt_index: 0`, and NOTHING reads it — the index
/// is the ledger's business, and the merge only ever downcasts back. So this
/// is [`merge_coin`]'s body against `b` directly rather than a round trip
/// through a qualified coin with a fabricated index, and compactc's artifacts
/// agree: `sMergeCoinImmediate` is `sMergeCoin` minus `b`'s `mt_index`
/// constraint, instruction for instruction.
pub fn merge_coin_immediate(
    c: &mut Circuit3,
    a: &QualifiedShieldedCoinInfo3<Public>,
    b: &ShieldedCoinInfo3<Public>,
) -> ShieldedCoinInfo3<Public> {
    merge(c, &a.downcast(), b)
}

/// Everything both merges do, once the coins are downcast.
fn merge(
    c: &mut Circuit3,
    a: &ShieldedCoinInfo3<Public>,
    b: &ShieldedCoinInfo3<Public>,
) -> ShieldedCoinInfo3<Public> {
    let me = self_address(c).bytes();
    let nul_a = coin_nullifier_contract(c, a, &me);
    claim_zswap_nullifier(c, &nul_a);
    let nul_b = coin_nullifier_contract(c, b, &me);
    claim_zswap_nullifier(c, &nul_b);

    let same_colour = bytes_eq(c, &a.color.bytes(), &b.color.bytes());
    c.assert(
        is_true(Bool::from_field_unchecked(same_colour)).message("Can only merge coins of the same color"),
    );

    // Field order is evaluation order, and compactc's too: the derived nonce
    // before the sum.
    let nonce = derived_nonce(c, NONCE_EVOLVE, &a.nonce);
    let sum = c.add(a.value, b.value);
    let new_coin = ShieldedCoinInfo3 {
        nonce,
        color: a.color,
        value: as_uint128(c, sum),
    };
    let cm = coin_commitment_to_contract(c, &new_coin, &me);
    claim_zswap_coin_spend(c, &cm);
    claim_zswap_coin_receive(c, &cm);
    new_coin
}

/// ```text
/// circuit sendShielded(input: QualifiedShieldedCoinInfo,
///                      recipient: Either<ZswapCoinPublicKey, ContractAddress>,
///                      value: Uint<128>): ShieldedSendResult {
///   const selfAddr = kernel.self();
///   createZswapInput(input);
///   kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(input), selfAddr));
///   const change = input.value - value;
///   const output = ShieldedCoinInfo{ nonce: <derived>, color: input.color, value: value };
///   createZswapOutput(output, recipient);
///   kernel.claimZswapCoinSpend(coinCommitment(output, recipient));
///   // Auto-receive when sending to self
///   if (!recipient.is_left && recipient.right.bytes == selfAddr.bytes) {
///     kernel.claimZswapCoinReceive(coinCommitment(output, recipient));
///   }
///   if (change == 0) { return ShieldedSendResult{ change: none, sent: output }; }
///   else { <change coin, spent and received by this contract>; }
/// }
/// ```
///
/// THE `if (change == 0)` IS AN EXPRESSION, and it is written out here rather
/// than through [`Circuit3::when_value`](minocrab::v3::Circuit3::when_value)
/// for one reason worth stating: compactc FOLDS the `Maybe`'s tag into the
/// guard it already has. `none` and `some` differ in a tag that is `0` on one
/// side and `1` on the other, so selecting it yields `cond_select(change == 0,
/// 0, 1)` — which is the `else` arm's guard, already computed. A chain would
/// emit that select a second time. So the tag IS the guard here, named once,
/// and only the five payload slots are selected.
///
/// Both commitments of `output` are the same digest, hashed twice, because
/// that is what compactc's inlining of two `coinCommitment` calls produces;
/// the recipient select they share is hoisted (see [`coin_commitment_to`]).
pub fn send_shielded(
    c: &mut Circuit3,
    input: &QualifiedShieldedCoinInfo3<Public>,
    recipient: &CoinRecipient<Public>,
    value: Uint<128, Public>,
) -> ShieldedSendResult<Public> {
    let me = self_address(c).bytes();
    let spent = input.downcast();
    let nul = coin_nullifier_contract(c, &spent, &me);
    claim_zswap_nullifier(c, &nul);

    let change = checked_sub(c, input.value, value.field());

    let output = ShieldedCoinInfo3 {
        nonce: derived_nonce(c, NONCE_EVOLVE, &input.nonce),
        color: input.color,
        value: value.field(),
    };
    let to = B32::cond_select(c, recipient.is_left, &recipient.left.bytes(), &recipient.right.bytes());
    let cm = coin_commitment_to(c, &output, recipient.is_left.erase(), &to);
    claim_zswap_coin_spend(c, &cm);

    // Auto-receive when sending to self: `!recipient.is_left && …`, which is
    // one `cond_select` with the arms the other way round from `is_self`'s.
    // The address needs no guarded read — `selfAddr` is already to hand.
    let same = bytes_eq(c, &recipient.right.bytes(), &me);
    let mine = c.cond_select(recipient.is_left, 0u64, same);
    let cm_again = coin_commitment_to(c, &output, recipient.is_left.erase(), &to);
    let cm_again_val = cm_again.ledger_value(c);
    emit_guarded(c, mine, &minocrab_ledger::kernel_claim_zswap_coin_receive(&cm_again_val));

    let spent_it_all = c.test_eq(change, 0u64);
    let has_change = not(c, Bool::from_field_unchecked(spent_it_all)).field();
    let change_coin = ShieldedCoinInfo3 {
        nonce: derived_nonce(c, NONCE_EVOLVE_CHANGE, &input.nonce),
        color: input.color,
        value: change,
    };
    let change_cm = coin_commitment_to_contract(c, &change_coin, &me);
    c.when(has_change, |c| {
        claim_zswap_coin_spend(c, &change_cm);
        claim_zswap_coin_receive(c, &change_cm);
    });

    // `none<ShieldedCoinInfo>()` is the default coin, so the payload is the
    // change coin selected against zero — the tag is `has_change` above.
    let none_unless = |c: &mut Circuit3, w| c.cond_select(spent_it_all, 0u64, w);
    let change_value = ShieldedCoinInfo3 {
        nonce: CoinNonce(B32 {
            hi: none_unless(c, change_coin.nonce.bytes().hi),
            lo: none_unless(c, change_coin.nonce.bytes().lo),
        }),
        color: CoinColor(B32 {
            hi: none_unless(c, change_coin.color.bytes().hi),
            lo: none_unless(c, change_coin.color.bytes().lo),
        }),
        value: none_unless(c, change_coin.value),
    };
    ShieldedSendResult {
        change: Maybe {
            is_some: Bool::from_field_unchecked(has_change),
            value: change_value,
        },
        sent: output,
    }
}
