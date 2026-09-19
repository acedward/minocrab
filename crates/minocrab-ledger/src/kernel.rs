//! The kernel effects: `kernel_*`.

use midnight_base_crypto::fab::AlignmentAtom;
use midnight_onchain_vm::ops::{Key, Op};
use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::v3::ImpactElem;
use minocrab::{Fr, Public};

use crate::impact::*;
use crate::reads::*;
const U128_ATOM: AlignmentAtom = AlignmentAtom::Bytes { length: 16 };

// --- the context reads: balances and block time -----------------------------
//
// Both read the CONTEXT (stack slot 2) rather than the contract's state, and
// both are `popeqc`. They are the two shapes of notes/kernel-tokens.org
// finding (c) that the crate did not already have.

/// Comparison tail of a balance read.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BalanceCmp {
    /// `kernel.balance(t)` — the balance itself, a `Uint<128>`.
    Value,
    /// `kernel.balanceLessThan(t, n)` — `balance < n`.
    LessThan,
    /// `kernel.balanceGreaterThan(t, n)` — `balance > n`.
    GreaterThan,
}

/// `kernel.balance*(token_type[, amount])` (midnight-ledger.ss:427-540).
///
/// One shape for all three: fetch the context's unshielded-balances map
/// (context\[5\]), yield `map[token_type]` or ZERO if the key is absent, then
/// compare or not.
///
/// ```text
/// dup 2; idxc [5]; dup 0; push token_type; member
/// branch 3;  pop; push 0u128; jmp 1
///            idxc [token_type]
/// [push amount; lt|gt]
/// popeqc
/// ```
///
/// The zero default is why `unshieldedBalance` on a token the contract has
/// never held is `0` rather than a failure. Note the balance is the one at
/// the START of execution — the effect accumulator's entries do not feed back
/// into it, which is the caveat Compact's own stdlib comment carries.
pub fn kernel_balance(
    c: &mut Circuit3,
    token_type: &LedgerValue,
    cmp: BalanceCmp,
    amount: Option<&LedgerValue>,
) -> Wire3<FieldT, Public> {
    let result_atom = if cmp == BalanceCmp::Value {
        U128_ATOM
    } else {
        BOOL_ATOM
    };
    let (wires, value) = mint_read(c, vec![result_atom]);
    label_read(c, &value, "a kernel balance read", &[]);
    let zero = LedgerValue::new(vec![U128_ATOM], vec![ImpactElem::Imm(Fr::from(0u64))]);
    // `greaterThan` pushes the amount BEFORE the lookup and ends with a bare
    // `lt`, which is how compactc turns `<` into `>` without a `gt` opcode —
    // the same trick `blockTimeGreaterThan` uses. Hence the leading push and
    // the `dup 3` in that arm.
    let greater = cmp == BalanceCmp::GreaterThan;
    let mut ops = Vec::new();
    if greater {
        ops.push(push_cell(false, amount.expect("a comparison needs an amount")));
    }
    ops.extend([
        dup(if greater { 3 } else { 2 }),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Value(field_key(5))].into(),
        }),
        dup(0),
        push_cell(false, token_type),
        ImpactOp::constant(&Op::Member),
        ImpactOp::constant(&Op::Branch { skip: 3 }),
        ImpactOp::constant(&Op::Pop),
        push_cell(false, &zero),
        ImpactOp::constant(&Op::Jmp { skip: 1 }),
        idx_key_cached(token_type),
    ]);
    if cmp == BalanceCmp::LessThan {
        ops.push(push_cell(false, amount.expect("a comparison needs an amount")));
    }
    if cmp != BalanceCmp::Value {
        ops.push(ImpactOp::constant(&Op::Lt));
    }
    ops.push(popeq(true, &value));
    emit(c, &ops);
    wires[0]
}

/// `kernel.blockTimeLessThan(t)` / `kernel.blockTimeGreaterThan(t)`
/// (midnight-ledger.ss:513-540): five instructions, and the two differ ONLY
/// in the order the operands reach `lt` — which is how a `<` becomes a `>`.
///
/// ```text
/// less than:    dup 2; idxc [2]; push t; lt; popeqc
/// greater than: push t; dup 3; idxc [2]; lt; popeqc
/// ```
///
/// The `dup 3` rather than `dup 2` in the greater-than form is the pushed `t`
/// sitting on the stack already.
pub fn kernel_block_time(
    c: &mut Circuit3,
    time: &LedgerValue,
    greater: bool,
) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a kernel block-time comparison", &[]);
    let block_time = ImpactOp::constant(&Op::Idx {
        cached: true,
        push_path: false,
        path: vec![Key::Value(field_key(2))].into(),
    });
    let ops = if greater {
        vec![
            push_cell(false, time),
            dup(3),
            block_time,
            ImpactOp::constant(&Op::Lt),
            popeq(true, &value),
        ]
    } else {
        vec![
            dup(2),
            block_time,
            push_cell(false, time),
            ImpactOp::constant(&Op::Lt),
            popeq(true, &value),
        ]
    };
    emit(c, &ops);
    wires[0]
}

/// `kernel.self()` (midnight-ledger.ss:256-260): `dup 2` to reach the
/// context array, `idxc [0]` (cached, path not remembered), `popeqc` →
/// the contract's own address as `Bytes<32>` `[hi, lo]` wires.
pub fn kernel_self(c: &mut Circuit3) -> [Wire3<FieldT, Public>; 2] {
    let (wires, value) = mint_read(c, vec![AlignmentAtom::Bytes { length: 32 }]);
    label_read(c, &value, "the kernel self read", &[]);
    let idx_context = ImpactOp::constant(&Op::Idx {
        cached: true,
        push_path: false,
        path: vec![Key::Value(field_key(0))].into(),
    });
    emit(c, &[dup(2), idx_context, popeq(true, &value)]);
    [wires[0], wires[1]]
}

// --- kernel effects ops -----------------------------------------------------
//
// The zswap/kernel update ops operate on the EFFECTS array (not contract
// state): each sequence starts `swap 0` to bring effects to the top and
// ends `swap 0` to restore [context, effects, state]. Sequences are
// midnight-ledger.ss's Kernel vm-code verbatim; these ops write no popeq,
// so they return nothing.

/// `push` of `StateValue::Null` (the claim maps hold `Null` values).
fn push_null() -> ImpactOp {
    ImpactOp::constant(&Op::Push {
        storage: false,
        value: midnight_onchain_state::state::StateValue::Null,
    })
}

/// `kernel.mintShielded(domain_sep, amount)` (midnight-ledger.ss:216-254):
/// The EFFECT ACCUMULATOR, shared by five kernel operations
/// (notes/kernel-tokens.org finding (c)): `effects[slot][key] += amount`,
/// where a key not already present starts from zero.
///
/// ```text
/// swap 0; idxpc [slot]                       // reach the effects map
/// push key; dup 1; dup 1; member             // is the key there?
/// push amount; swap 0; neg; branch 4
///     dup 2; dup 2; idxc [stack]; add        // …if so, add what is there
/// insc 2; swap 0
/// ```
///
/// The `branch` is resolved on chain and the PI stream is identical on both
/// paths, so this costs the circuit nothing conditional. The five callers
/// differ ONLY in the slot, the key's type and the amount's width:
///
/// | operation | slot | key |
/// |---|---|---|
/// | `mintShielded` | 4 | `Bytes<32>` domain separator |
/// | `mintUnshielded` | 5 | `Bytes<32>` domain separator |
/// | `incUnshieldedInputs` | 6 | `TokenType` |
/// | `incUnshieldedOutputs` | 7 | `TokenType` |
/// | `claimUnshieldedCoinSpend` | 8 | `(TokenType, UnshieldedRecipient)` |
fn kernel_effect_add(slot: u8, key: &LedgerValue, amount: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: true,
            path: vec![Key::Value(field_key(slot))].into(),
        }),
        push_cell(false, key),
        ImpactOp::constant(&Op::Dup { n: 1 }),
        ImpactOp::constant(&Op::Dup { n: 1 }),
        ImpactOp::constant(&Op::Member),
        push_cell(false, amount),
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Neg),
        ImpactOp::constant(&Op::Branch { skip: 4 }),
        ImpactOp::constant(&Op::Dup { n: 2 }),
        ImpactOp::constant(&Op::Dup { n: 2 }),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Stack].into(),
        }),
        ImpactOp::constant(&Op::Add),
        ImpactOp::constant(&Op::Ins { cached: true, n: 2 }),
        ImpactOp::constant(&Op::Swap { n: 0 }),
    ]
}

/// `kernel.mintShielded(domain_sep, amount)` — `kernel_effect_add` at
/// effects\[4\], one of the five callers of that shape.
pub fn kernel_mint_shielded(domain_sep: &LedgerValue, amount: &LedgerValue) -> Vec<ImpactOp> {
    kernel_effect_add(4, domain_sep, amount)
}

/// `kernel.mintUnshielded(domain_sep, amount)` — effects\[5\], `Uint<64>`.
pub fn kernel_mint_unshielded(domain_sep: &LedgerValue, amount: &LedgerValue) -> Vec<ImpactOp> {
    kernel_effect_add(5, domain_sep, amount)
}

/// `kernel.incUnshieldedInputs(token_type, amount)` — effects\[6\],
/// `Uint<128>`. Called when RECEIVING an unshielded token.
pub fn kernel_inc_unshielded_inputs(
    token_type: &LedgerValue,
    amount: &LedgerValue,
) -> Vec<ImpactOp> {
    kernel_effect_add(6, token_type, amount)
}

/// `kernel.incUnshieldedOutputs(token_type, amount)` — effects\[7\],
/// `Uint<128>`. Called when SENDING one.
pub fn kernel_inc_unshielded_outputs(
    token_type: &LedgerValue,
    amount: &LedgerValue,
) -> Vec<ImpactOp> {
    kernel_effect_add(7, token_type, amount)
}

/// `kernel.claimUnshieldedCoinSpend(token_type, recipient, amount)` —
/// effects\[8\]. The key is the CONCATENATION of the token type and the
/// recipient, which is why the caller passes one `LedgerValue` of six atoms
/// rather than two of three.
pub fn kernel_claim_unshielded_coin_spend(
    token_and_recipient: &LedgerValue,
    amount: &LedgerValue,
) -> Vec<ImpactOp> {
    kernel_effect_add(8, token_and_recipient, amount)
}

/// The shared claim shape (claimZswapNullifier :162 / claimZswapCoinSpend
/// :173 / claimZswapCoinReceive :184): insert `note → Null` into the
/// claim map at `effects[index]`.
fn kernel_claim(effect_index: u8, note: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: true,
            path: vec![Key::Value(field_key(effect_index))].into(),
        }),
        push_cell(false, note),
        push_null(),
        ImpactOp::constant(&Op::Ins { cached: true, n: 2 }),
        ImpactOp::constant(&Op::Swap { n: 0 }),
    ]
}

/// `kernel.claimZswapNullifier(nul)` — effects\[0\].
pub fn kernel_claim_zswap_nullifier(nul: &LedgerValue) -> Vec<ImpactOp> {
    kernel_claim(0, nul)
}

/// `kernel.claimZswapCoinReceive(note)` — effects\[1\].
pub fn kernel_claim_zswap_coin_receive(note: &LedgerValue) -> Vec<ImpactOp> {
    kernel_claim(1, note)
}

/// `kernel.claimZswapCoinSpend(note)` — effects\[2\].
pub fn kernel_claim_zswap_coin_spend(note: &LedgerValue) -> Vec<ImpactOp> {
    kernel_claim(2, note)
}

/// `kernel.claimContractCall(addr, entry_point, comm)`
/// (midnight-ledger.ss:195-215): insert `size(claims) ‖ addr ‖ ep ‖ comm →
/// Null` into the claimed-contract-calls map at effects\[3\]. `addr_ep_comm`
/// is the single 3-atom `[bytes<32>, bytes<32>, field]` concatenation
/// (`rt-aligned-concat`); the size prefix (via `dup 0; size; concatc 160`)
/// keys repeated identical calls apart.
pub fn kernel_claim_contract_call(addr_ep_comm: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: true,
            path: vec![Key::Value(field_key(3))].into(),
        }),
        dup(0),
        ImpactOp::constant(&Op::Size),
        push_cell(false, addr_ep_comm),
        ImpactOp::constant(&Op::Concat {
            cached: true,
            n: 160,
        }),
        push_null(),
        ImpactOp::constant(&Op::Ins { cached: true, n: 2 }),
        ImpactOp::constant(&Op::Swap { n: 0 }),
    ]
}
