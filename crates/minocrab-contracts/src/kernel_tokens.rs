//! `kernel.compact` — the kernel primitives and token-stdlib circuits M4 left
//! (M17, notes/kernel-tokens.org).
//!
//! Not a corpus contract, for the fourth milestone running and the same
//! measured reason: across the three `--feature-zkir-v3` sources the
//! kernel/token surface used is `kernel.self`, `receiveShielded`,
//! `mintShieldedToken` and `sendImmediateShielded` — all SHIELDED, and not one
//! v3 use of an unshielded primitive, of `balance*`, of `blockTime*` or of
//! `mergeCoin`.
//!
//! `kernel.checkpoint()` is absent from the fixture and from this module
//! because compactc's ZKIR-v3 backend cannot compile it — see the fixture's
//! header for the exact failure, and notes/kernel-tokens.org finding (a).

use minocrab::v3::Circuit3;
use minocrab::{Private, Public};
use minocrab_std::v3::{
    CoinColor, TokenDomainSeparator,
    CoinNonce,
    contract, kernel, label, Bool, CircuitArg, CoinRecipient, Disclose, Discloses, Either,
    Ledger,
    LedgerCounter, QualifiedShieldedCoinInfo3, ShieldedCoinInfo3, ShieldedSendResult, Uint,
    UserAddress, ZswapCoinPublicKey,
};

label! {
    DomainSep = "domain separator";
    Amount = "amount";
    Color = "token colour";
    Recipient = "recipient";
    Time = "block time";
    CoinA = "coin a";
    CoinB = "coin b";
    InputCoin = "input coin";
}

/// THE LEDGER BLOCK — one counter, because a Compact circuit that touches
/// nothing produces no artifact to compare against.
#[derive(Ledger)]
pub struct KernelTokens {
    pub dummy: LedgerCounter,
}

/// The contract's ledger block.
pub const KT: KernelTokens = KernelTokens::new();

// THE CONTRACT — every circuit `kernel.compact` exports, as an `impl` of
// the state they run against (the `#[contract]` block below the argument
// types). `KernelTokens::CIRCUITS` is the derived set: the differential and
// the snapshots enumerate it instead of a hand-written list, so a circuit
// that exists here cannot be missed by them.
// ---- the SHIELDED compositions ----------------------------------------------

/// `QualifiedShieldedCoinInfo` as an argument — a coin the contract can spend,
/// which is [`ShieldedCoinArg`] plus its place in the commitment tree.
#[derive(CircuitArg)]
struct QualifiedCoinArg {
    nonce: CoinNonce<Private>,
    color: CoinColor<Private>,
    value: Uint<128>,
    mt_index: Uint<64>,
}

impl QualifiedCoinArg {
    /// Disclose the whole coin under one label — a coin is one logical value,
    /// and every field of it reaches the transcript together.
    fn disclose<L: minocrab_std::v3::DisclosureLabel>(
        self,
        c: &mut Circuit3,
    ) -> QualifiedShieldedCoinInfo3<Public> {
        QualifiedShieldedCoinInfo3 {
            nonce: self.nonce.disclose_as::<L>(c),
            color: self.color.disclose_as::<L>(c),
            value: self.value.disclose_as::<L>(c).field(),
            mt_index: self.mt_index.disclose_as::<L>(c).field(),
        }
    }
}

/// `ShieldedCoinInfo` as an argument.
#[derive(CircuitArg)]
struct ShieldedCoinArg {
    nonce: CoinNonce<Private>,
    color: CoinColor<Private>,
    value: Uint<128>,
}

impl ShieldedCoinArg {
    fn disclose<L: minocrab_std::v3::DisclosureLabel>(
        self,
        c: &mut Circuit3,
    ) -> ShieldedCoinInfo3<Public> {
        ShieldedCoinInfo3 {
            nonce: self.nonce.disclose_as::<L>(c),
            color: self.color.disclose_as::<L>(c),
            value: self.value.disclose_as::<L>(c).field(),
        }
    }
}

#[contract]
impl KernelTokens {
    // ---- the kernel primitives --------------------------------------------------

    /// `export circuit kMintUnshielded(ds: Bytes<32>, amount: Uint<64>): []`
    #[circuit]
    pub fn k_mint_unshielded(
        c: &mut Circuit3,
        ds: TokenDomainSeparator<Private>,
        amount: Uint<64>,
    ) -> Discloses<(DomainSep, Amount)> {
        let ds = ds.disclose_as::<DomainSep>(c);
        let amount = amount.disclose_as::<Amount>(c);
        kernel::mint_unshielded(c, &ds, amount);
        Discloses::of(())
    }

    /// `export circuit kClaimUnshieldedCoinSpend(color, addr, amount): []`
    #[circuit]
    pub fn k_claim_unshielded_coin_spend(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        addr: Either<minocrab_std::v3::ContractAddress<Private>, UserAddress<Private>, Private>,
        amount: Uint<128>,
    ) -> Discloses<(Color, Recipient, Amount)> {
        let color = color.disclose_as::<Color>(c);
        let addr = addr.disclose_as::<Recipient>(c);
        let amount = amount.disclose_as::<Amount>(c);
        let token = kernel::unshielded(c, color);
        kernel::claim_unshielded_coin_spend(c, &token, &addr, amount);
        Discloses::of(())
    }

    /// `export circuit kIncUnshieldedOutputs(color, amount): []`
    #[circuit]
    pub fn k_inc_unshielded_outputs(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        amount: Uint<128>,
    ) -> Discloses<(Color, Amount)> {
        let color = color.disclose_as::<Color>(c);
        let amount = amount.disclose_as::<Amount>(c);
        let token = kernel::unshielded(c, color);
        kernel::inc_unshielded_outputs(c, &token, amount);
        Discloses::of(())
    }

    /// `export circuit kIncUnshieldedInputs(color, amount): []`
    #[circuit]
    pub fn k_inc_unshielded_inputs(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        amount: Uint<128>,
    ) -> Discloses<(Color, Amount)> {
        let color = color.disclose_as::<Color>(c);
        let amount = amount.disclose_as::<Amount>(c);
        let token = kernel::unshielded(c, color);
        kernel::inc_unshielded_inputs(c, &token, amount);
        Discloses::of(())
    }

    /// `export circuit kBalance(color: Bytes<32>): Uint<128>`
    #[circuit(output = "balance")]
    pub fn k_balance(c: &mut Circuit3, color: CoinColor<Private>) -> Discloses<(Color,), Uint<128, Public>> {
        let color = color.disclose_as::<Color>(c);
        let token = kernel::unshielded(c, color);
        Discloses::of(*kernel::balance(c, &token))
    }

    /// `export circuit kBalanceLessThan(color, amount): Boolean`
    #[circuit(output = "less")]
    pub fn k_balance_less_than(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        amount: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let amount = amount.disclose_as::<Amount>(c);
        let token = kernel::unshielded(c, color);
        Discloses::of(*kernel::balance_less_than(c, &token, amount))
    }

    /// `export circuit kBalanceGreaterThan(color, amount): Boolean`
    #[circuit(output = "greater")]
    pub fn k_balance_greater_than(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        amount: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let amount = amount.disclose_as::<Amount>(c);
        let token = kernel::unshielded(c, color);
        Discloses::of(*kernel::balance_greater_than(c, &token, amount))
    }

    /// `export circuit kBlockTimeLessThan(t: Uint<64>): Boolean`
    #[circuit(output = "before")]
    pub fn k_block_time_less_than(
        c: &mut Circuit3,
        t: Uint<64>,
    ) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_less_than(c, t))
    }

    /// `export circuit kBlockTimeGreaterThan(t: Uint<64>): Boolean`
    #[circuit(output = "after")]
    pub fn k_block_time_greater_than(
        c: &mut Circuit3,
        t: Uint<64>,
    ) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_greater_than(c, t))
    }

    // ---- the stdlib circuits ----------------------------------------------------

    /// `export circuit sBlockTimeLt(t): Boolean { return blockTimeLt(t); }`
    #[circuit(output = "lt")]
    pub fn s_block_time_lt(c: &mut Circuit3, t: Uint<64>) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_lt(c, t))
    }

    /// `export circuit sBlockTimeGte(t): Boolean { return blockTimeGte(t); }`
    #[circuit(output = "gte")]
    pub fn s_block_time_gte(c: &mut Circuit3, t: Uint<64>) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_gte(c, t))
    }

    /// `export circuit sBlockTimeGt(t): Boolean { return blockTimeGt(t); }`
    #[circuit(output = "gt")]
    pub fn s_block_time_gt(c: &mut Circuit3, t: Uint<64>) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_gt(c, t))
    }

    /// `export circuit sBlockTimeLte(t): Boolean { return blockTimeLte(t); }`
    #[circuit(output = "lte")]
    pub fn s_block_time_lte(c: &mut Circuit3, t: Uint<64>) -> Discloses<(Time,), Bool<Public>> {
        let t = t.disclose_as::<Time>(c);
        Discloses::of(*kernel::block_time_lte(c, t))
    }

    /// `export circuit sUnshieldedBalance(color): Uint<128>`
    #[circuit(output = "balance")]
    pub fn s_unshielded_balance(
        c: &mut Circuit3,
        color: CoinColor<Private>,
    ) -> Discloses<(Color,), Uint<128, Public>> {
        let color = color.disclose_as::<Color>(c);
        Discloses::of(*kernel::unshielded_balance(c, color))
    }

    /// `export circuit sUnshieldedBalanceLt(color, a): Boolean`
    #[circuit(output = "lt")]
    pub fn s_unshielded_balance_lt(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        Discloses::of(*kernel::unshielded_balance_lt(c, color, a))
    }

    /// `export circuit sUnshieldedBalanceGte(color, a): Boolean`
    #[circuit(output = "gte")]
    pub fn s_unshielded_balance_gte(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        Discloses::of(*kernel::unshielded_balance_gte(c, color, a))
    }

    /// `export circuit sUnshieldedBalanceGt(color, a): Boolean`
    #[circuit(output = "gt")]
    pub fn s_unshielded_balance_gt(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        Discloses::of(*kernel::unshielded_balance_gt(c, color, a))
    }

    /// `export circuit sUnshieldedBalanceLte(color, a): Boolean`
    #[circuit(output = "lte")]
    pub fn s_unshielded_balance_lte(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
    ) -> Discloses<(Color, Amount), Bool<Public>> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        Discloses::of(*kernel::unshielded_balance_lte(c, color, a))
    }

    /// `export circuit sReceiveUnshielded(color, a): []`
    #[circuit]
    pub fn s_receive_unshielded(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
    ) -> Discloses<(Color, Amount)> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        kernel::receive_unshielded(c, color, a);
        Discloses::of(())
    }

    /// `export circuit sSendUnshielded(color, a, r): []`
    ///
    /// The first M17 circuit with a CONDITIONAL: its auto-receive runs only when
    /// the recipient is this contract, which is a guarded `kernel.self()` read
    /// feeding a guarded effect.
    #[circuit]
    pub fn s_send_unshielded(
        c: &mut Circuit3,
        color: CoinColor<Private>,
        a: Uint<128>,
        r: Either<minocrab_std::v3::ContractAddress<Private>, UserAddress<Private>, Private>,
    ) -> Discloses<(Color, Amount, Recipient)> {
        let color = color.disclose_as::<Color>(c);
        let a = a.disclose_as::<Amount>(c);
        let r = r.disclose_as::<Recipient>(c);
        kernel::send_unshielded(c, color, a, &r);
        Discloses::of(())
    }

    /// `export circuit sMintUnshieldedToken(ds, a, r): Bytes<32>`
    #[circuit(output = "color")]
    pub fn s_mint_unshielded_token(
        c: &mut Circuit3,
        ds: TokenDomainSeparator<Private>,
        a: Uint<64>,
        r: Either<minocrab_std::v3::ContractAddress<Private>, UserAddress<Private>, Private>,
    ) -> Discloses<(DomainSep, Amount, Recipient), CoinColor<Public>> {
        let ds = ds.disclose_as::<DomainSep>(c);
        let a = a.disclose_as::<Amount>(c);
        let r = r.disclose_as::<Recipient>(c);
        Discloses::of(kernel::mint_unshielded_token(c, &ds, a, &r))
    }

    /// `export circuit sMergeCoin(a, b: QualifiedShieldedCoinInfo): ShieldedCoinInfo`
    #[circuit(output = "coin")]
    pub fn s_merge_coin(
        c: &mut Circuit3,
        a: QualifiedCoinArg,
        b: QualifiedCoinArg,
    ) -> Discloses<(CoinA, CoinB), ShieldedCoinInfo3<Public>> {
        let a = a.disclose::<CoinA>(c);
        let b = b.disclose::<CoinB>(c);
        Discloses::of(kernel::merge_coin(c, &a, &b))
    }

    /// `export circuit sMergeCoinImmediate(a: QualifiedShieldedCoinInfo,
    /// b: ShieldedCoinInfo): ShieldedCoinInfo`
    #[circuit(output = "coin")]
    pub fn s_merge_coin_immediate(
        c: &mut Circuit3,
        a: QualifiedCoinArg,
        b: ShieldedCoinArg,
    ) -> Discloses<(CoinA, CoinB), ShieldedCoinInfo3<Public>> {
        let a = a.disclose::<CoinA>(c);
        let b = b.disclose::<CoinB>(c);
        Discloses::of(kernel::merge_coin_immediate(c, &a, &b))
    }

    /// `export circuit sSendShielded(input: QualifiedShieldedCoinInfo,
    /// r: Either<ZswapCoinPublicKey, ContractAddress>, v: Uint<128>):
    /// ShieldedSendResult`
    ///
    /// The largest M17 circuit, and the one with a conditional in both flavours:
    /// an effect branch (the self-send auto-receive) and a VALUE branch (change,
    /// or none).
    #[circuit(output = "result")]
    pub fn s_send_shielded(
        c: &mut Circuit3,
        input: QualifiedCoinArg,
        r: Either<ZswapCoinPublicKey<Private>, minocrab_std::v3::ContractAddress<Private>, Private>,
        v: Uint<128>,
    ) -> Discloses<(InputCoin, Recipient, Amount), ShieldedSendResult<Public>> {
        let input = input.disclose::<InputCoin>(c);
        let r = r.disclose_as::<Recipient>(c);
        let v = v.disclose_as::<Amount>(c);
        let recipient = CoinRecipient {
            is_left: r.is_left.field(),
            left: r.left,
            right: r.right,
        };
        Discloses::of(kernel::send_shielded(c, &input, &recipient, v))
    }
    }
