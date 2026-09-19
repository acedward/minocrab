//! The typed EVM call as a ledger slot: `Pending<Filing, Env, WORDS>`
//! (M37 rungs B and C, notes/evm-calls.org §§3-4; M38 rung A,
//! notes/evm-interfaces.org §2).
//!
//! [`crate::evm`] made the CALL a type — its name, its argument list, its
//! return, the interface that exposes it, its gas limit and the rule by
//! which its return says "it worked". This module makes the SLOT a type
//! over a FILING of that call: the call plus the response kind byte this
//! deployment files it under, which [`Kinded`](crate::evm::Kinded) supplies
//! in one line.
//!
//! ```ignore
//! type Transfer = Kinded<erc20::Transfer, 1>;
//!
//! #[derive(Ledger)]
//! pub struct Treasury {
//!     pub signet: Signet,
//!     pub transfers: Pending<Transfer, Owned<Amount>, 2>,
//! }
//! ```
//!
//! and everything else follows. What a contract author no longer writes:
//! the selector, the ABI words, the response type, the schema strings, the
//! gas envelope, the signing path, the notification path, the record format
//! version, the `&SELF.signet` argument (`#[derive(Ledger)]` threads the
//! block's Signet offset into every `Pending` field) and — with [`Owned`] —
//! the owner commitment's construction and opening.
//!
//! # The two tickets are SYMMETRIC
//!
//! [`Succeeded<F>`] and [`Failed<F>`], and nothing else settles a request
//! — and `F` is the FILING, so a ticket for `transfer` at one kind cannot
//! settle a slot that files `transfer` at another:
//!
//! - [`Pending::complete`] takes a `Succeeded`, asserts the attestation is
//!   this slot's kind, verifies it, consumes the entry — and then asserts
//!   the call's own [`EvmCall::succeeded`] predicate. A mined ERC-20 `transfer`
//!   that returned `false` therefore CANNOT complete, whoever presents it
//!   (notes/evm-calls.org §3: the spurious-completion hole the deployed
//!   vault leaves open by putting a refund branch inside its
//!   `completeWithdraw`).
//! - [`Pending::refund`] takes a `Failed`, and accepts EITHER the MPC's
//!   failure kind (reverted, never mined, or an undecodable return — §3.1)
//!   OR this slot's own kind with the success predicate false.
//!
//! So the two non-successes are one ticket, the success is the other, and
//! neither stands in for the other.
//!
//! # HAZARD, carried forward from §3.1
//!
//! The MPC resolves a request as FAILED when the receipt reverted, when the
//! transaction never mined, AND when the return data does not decode into
//! the declared output schema. A non-conforming ERC-20 that returns NOTHING
//! (USDT and friends) therefore produces an attested failure for a transfer
//! that MOVED the tokens — a spurious refund this API cannot see from the
//! attestation alone. Until the callee's return shape is declared per token
//! (a `Contract<Erc20NoReturn>` marker) or success is read off the
//! `Transfer` event, **a contract using this module needs a callee
//! allow-list**, exactly as the deployed vault has one in effect through its
//! configured ERC-20 addresses.
//!
//! # What `Failed<F>` costs
//!
//! The two accepted attestations have DIFFERENT PREIMAGES: the MPC's
//! failure output is one byte (the kind alone — `FailureResponse { kind: u8
//! }`, spec/borsh-subset.md §5), where an executed `transfer`'s is two (the
//! kind and the flag). Poseidon is not a stream, so one hash cannot cover
//! both lengths: [`Pending::refund`] hashes the preimage BOTH ways, selects
//! the field element by the kind byte and verifies ONCE. The extra cost is
//! one `transient_hash` and one `cond_select` beside the ~30k rows of the
//! ECDSA verification that follows — measured in
//! `tests/treasury.rs::the_refund_pays_one_extra_digest`.
//! (notes/evm-calls.org §3 predicted "cost: nil" on the belief that both
//! payloads are one limb; they are not — §10 records the correction.)
//!
//! # What does not compile
//!
//! A CALL SENT TO AN INTERFACE THAT DOES NOT EXPOSE IT — the first rung of
//! the ladder (notes/evm-interfaces.org §2.5). `erc20::Transfer::Callee` is
//! `Erc20`, and a Uniswap router is not one, so there is no `Extends` impl:
//!
//! ```compile_fail
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, uniswap_v3, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     // ERROR: the trait bound `UniswapV3Router: Extends<Erc20>` is not satisfied
//!     callee: Contract<uniswap_v3::UniswapV3Router>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     BLOCK.transfers.request(c, callee, (to, amount), key_version, nonce, |_, _| env);
//! }
//! ```
//!
//! THE SAME CODE WITH THE ONE CHANGE REVERTED compiles — the callee's
//! interface is the only difference, so the rejection is the interface:
//!
//! ```
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     callee: Contract<erc20::Erc20>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     BLOCK.transfers.request(c, callee, (to, amount), key_version, nonce, |_, _| env);
//! }
//! ```
//!
//! A ticket for one FILING handed to another's slot — and the two filings
//! here are the SAME Solidity call at two kinds, which is exactly the pair
//! the deployed vault has (`transfer` as a claim and as a withdrawal):
//!
//! ```compile_fail
//! use minocrab::v3::Circuit3;
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending, Succeeded};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn settle(c: &mut Circuit3, ticket: Succeeded<Kinded<erc20::Transfer, 2>>) {
//!     // ERROR: expected `Succeeded<Kinded<Transfer, 1>>`,
//!     //        found `Succeeded<Kinded<Transfer, 2>>`
//!     BLOCK.transfers.complete(c, ticket);
//! }
//! ```
//!
//! THE SAME CODE WITH THE ONE CHANGE REVERTED compiles:
//!
//! ```
//! use minocrab::v3::Circuit3;
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending, Succeeded};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn settle(c: &mut Circuit3, ticket: Succeeded<Kinded<erc20::Transfer, 1>>) {
//!     BLOCK.transfers.complete(c, ticket);
//! }
//! ```
//!
//! A `WORDS` that is not the call's argument-word count — `error[E0080]`
//! from the slot's constructor, which `#[derive(Ledger)]` calls:
//!
//! ```compile_fail
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     // error[E0080]: `Pending<F, Env, WORDS>` needs WORDS == …
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 3>,
//! }
//! const BLOCK: Block = Block::new();
//! const _: usize = BLOCK.transfers.record_path().depth() as usize;
//! ```
//!
//! TWO SLOTS OF ONE BLOCK AT ONE RESPONSE KIND — the derive's
//! `assert_distinct_kinds`, which now reads `Filing::KIND` through
//! [`LedgerWidth::KINDS`]. The MPC's kind byte could not tell the two
//! attestations apart, so it is `error[E0080]`:
//!
//! ```compile_fail
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     // error[E0080]: two slots of this ledger block settle under the same
//!     //               Signet response kind …
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//!     approvals: Pending<Kinded<erc20::Approve, 1>, Owned<Amount>, 2>,
//! }
//! ```
//!
//! THE SAME CODE WITH THE ONE BYTE CHANGED compiles — two filings of two
//! calls, at two kinds:
//!
//! ```
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//!     approvals: Pending<Kinded<erc20::Approve, 4>, Owned<Amount>, 2>,
//! }
//! ```
//!
//! A `Pending` slot in a block with no `Signet` field — the derive's own
//! error, because there would be no configuration to read the MPC key,
//! the nonce and the chain from:
//!
//! ```compile_fail
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending};
//! use minocrab_std::v3::{Ledger, LedgerCounter, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     initialized: LedgerCounter,
//!     // ERROR: a `Pending` slot needs the block's `Signet` field …
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//! }
//! ```
//!
//! TWO `Signet` fields — one contract, one MPC key, one nonce sequence:
//!
//! ```compile_fail
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Owned, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//! use minocrab::Public;
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     // ERROR: #[derive(Ledger)] wants EXACTLY ONE `Signet` field per block
//!     other: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Owned<Amount>, 2>,
//! }
//! ```
//!
//! ETHER ON A CALL THAT CANNOT TAKE IT — `Pending::request_payable` is
//! bounded by [`Payable`], and an ERC-20 `transfer`
//! has no impl, so an amount cannot be attached to a call that would
//! ignore it and leave the ether with the contract (M38 rung B):
//!
//! ```compile_fail
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     callee: Contract<erc20::Erc20>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     // ERROR: the trait bound `erc20::Transfer: Payable` is not satisfied
//!     BLOCK.transfers.request_payable(
//!         c, callee, (to, amount), amount, key_version, nonce, |_, _| env,
//!     );
//! }
//! ```
//!
//! THE SAME CALL THAT DOES TAKE ETHER compiles — WETH's `deposit()`, whose
//! ether IS its argument (it has no calldata beyond the selector, so the
//! slot's `WORDS` is zero):
//!
//! ```
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{weth, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     wraps: Pending<Kinded<weth::Deposit, 1>, Amount, 0>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn wrap(
//!     c: &mut Circuit3,
//!     callee: Contract<weth::Weth>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     BLOCK.wraps.request_payable(
//!         c, callee, (), amount, key_version, nonce, |_, _| env,
//!     );
//! }
//! ```
//!
//! A CONFORMING TOKEN'S CALL FILED AGAINST A NON-CONFORMING ONE, and the
//! other direction. `UsdtLike` is a SIBLING of `Erc20`, not a subtype:
//! neither `Extends` the other, so neither address takes the other's calls.
//! That is what stops a USDT address being handed to a slot that declares a
//! `bool` return, whose absent return the MPC would resolve as its FAILURE
//! kind — refunding a transfer that moved the tokens
//! (notes/evm-calls.org §3.1, the dangerous direction):
//!
//! ```compile_fail
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, usdt, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<usdt::Transfer, 1>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     // ERROR: the trait bound `Erc20: Extends<UsdtLike>` is not satisfied
//!     callee: Contract<erc20::Erc20>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     BLOCK.transfers.request(c, callee, (to, amount), key_version, nonce, |_, _| env);
//! }
//! ```
//!
//! ```compile_fail
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, usdt, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     transfers: Pending<Kinded<erc20::Transfer, 1>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     // ERROR: the trait bound `UsdtLike: Extends<Erc20>` is not satisfied
//!     callee: Contract<usdt::UsdtLike>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     env: Amount,
//! ) {
//!     BLOCK.transfers.request(c, callee, (to, amount), key_version, nonce, |_, _| env);
//! }
//! ```
//!
//! THE SAME CODE WITH EACH CALLEE MATCHED TO ITS OWN INTERFACE compiles,
//! and the two slots are the same two words on the wire — the difference is
//! entirely in what the MPC is asked to decode:
//!
//! ```
//! use minocrab::v3::Circuit3;
//! use minocrab::{Private, Public};
//! use minocrab_contracts::evm::{erc20, usdt, Kinded};
//! use minocrab_contracts::evm_flow::{Contract, Pending};
//! use minocrab_contracts::signet_flow::Signet;
//! use minocrab_std::v3::{Bytes, Ledger, LedgerRepr, Uint};
//!
//! #[derive(LedgerRepr)] struct Amount { amount: Uint<64, Public> }
//!
//! #[derive(Ledger)]
//! struct Block {
//!     signet: Signet,
//!     conforming: Pending<Kinded<erc20::Transfer, 1>, Amount, 2>,
//!     non_conforming: Pending<Kinded<usdt::Transfer, 2>, Amount, 2>,
//! }
//! const BLOCK: Block = Block::new();
//!
//! fn send(
//!     c: &mut Circuit3,
//!     token: Contract<erc20::Erc20>,
//!     tether: Contract<usdt::UsdtLike>,
//!     to: Bytes<20, Private>,
//!     amount: Uint<128, Private>,
//!     key_version: Uint<8>,
//!     nonce: Uint<64>,
//!     one: Amount,
//!     two: Amount,
//! ) {
//!     BLOCK.conforming.request(c, token, (to, amount), key_version, nonce, |_, _| one);
//!     BLOCK.non_conforming.request(c, tether, (to, amount), key_version, nonce, |_, _| two);
//! }
//! ```
//!
//! A callee where a recipient belongs — `Contract<I>` and `Bytes<20>` are
//! the same twenty bytes and do not unify:
//!
//! ```compile_fail
//! use minocrab::v3::{Circuit3, FieldT};
//! use minocrab::Private;
//! use minocrab_contracts::evm::erc20;
//! use minocrab_contracts::evm_flow::Contract;
//! use minocrab_std::v3::Bytes;
//!
//! fn f(c: &mut Circuit3, callee: Contract<erc20::Erc20>) -> Bytes<20, Private> {
//!     // ERROR: expected `Bytes<20>`, found `Contract<Erc20>`
//!     callee
//! }
//! ```

use core::marker::PhantomData;

use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::{Private, Public};
use minocrab_std::v3::borsh::CircuitBorsh;
use minocrab_std::v3::hash::{transient_hash_compact, upgrade_from_transient};
use minocrab_std::v3::{
    eq, is_true, label, not, own_public_key, repr_limbs, ArgPath, Bytes, CircuitAbi, CircuitArg,
    Assumed, Disclose, DisclosureLabel, FieldPath, LedgerMap, LedgerRepr, LedgerWidth, Prim,
    ProofWires, Uint, Vis3, ZswapCoinPublicKey, B32,
};
use minocrab::v3::Val;
use signet_signer_interface::{RequestId, Signature};

use crate::common::{self, SecretKey, SigningPath};
use crate::erc20_vault::REFUND_PAD;
use crate::evm::{
    build_tx_filed, build_tx_from_words, build_tx_payable_filed, build_tx_with, AbiArgs, AbiTuple,
    AbiType, Envelope, EvmCall, Extends, Filing, Interface, Payable,
};
use crate::signet::{self, EventRecordV2, Secp256k1SigLimbs, RECORD_FORMAT_VERSION};
use crate::signet_flow::{
    file_request, Attested, EvmTx, Outcome, RequestIdSettled, SignRequest, Signet,
};

/// THE MPC'S FAILURE KIND — byte 0 of the fixed output it attests when a
/// request reverted, never mined, or came back undecodable
/// (spec/borsh-subset.md §5, kind 3).
///
/// Response-only: no request is ever filed under it, so no slot claims it in
/// `LedgerWidth::KINDS` and every slot of a block may receive it.
pub const FAILURE_KIND: u8 = 3;

/// What an attested value must be: a circuit argument (it arrives on the
/// ticket) and a Borsh record (its limbs ARE the signed preimage).
///
/// `Copy` on top, because [`Pending::refund`] needs the value twice: once
/// for the outcome rule's predicate and once inside the digest it may or may
/// not hash it into. Every circuit leaf in this workspace is `Copy` — a wire
/// is a handle — so the bound costs nothing.
pub trait Attestable: Copy + CircuitArg + CircuitBorsh<Private> {}
impl<T: Copy + CircuitArg + CircuitBorsh<Private>> Attestable for T {}

/// A call's attested return value, as a circuit wire.
pub type Ret<C> = <<C as EvmCall>::Return as AbiType>::Wire<Private>;

/// The CALL a [`Filing`] files — `F::Call`, spelled once so a slot's
/// signatures read as sentences rather than as projections.
pub type Called<F> = <F as Filing>::Call;

/// The INTERFACE a filing's call must be sent to: the callee of `F`'s call.
/// A `Contract<I>` reaches it when `I: Extends<Callee<F>>`.
pub type Callee<F> = <Called<F> as EvmCall>::Callee;


// ---- the callee ---------------------------------------------------------------

/// THE ADDRESS OF A CONTRACT THAT CLAIMS INTERFACE `I` — a `Bytes<20>`
/// that knows what it answers.
///
/// Two things it buys, at no wire cost (the shape is a bare `Bytes<20>`,
/// one argument slot, the same schema):
///
/// - A callee and a recipient are both twenty bytes and mean opposite
///   things; `Contract<Erc20>` and `Bytes<20>` do not unify, so the two
///   cannot be swapped in a `request` call.
/// - A call goes only where its interface does. `request` takes a
///   `Contract<I>` with `I: Extends<Callee<F>>`, so an
///   [`erc20::Transfer`](crate::evm::erc20::Transfer) filed against a
///   `Contract<UniswapV3Router>` is a MISSING IMPL, and an
///   [`erc20::Approve`](crate::evm::erc20::Approve) against a
///   `Contract<Erc4626>` compiles because an ERC-4626 vault IS an ERC-20.
///
/// WHAT IT DOES NOT BUY: any check that the deployed address at the other
/// end really is that interface. The type records the CLAIM the contract
/// made when it built the value, which is why the callee-allow-list hazard
/// (this module's header) is about where the address came from.
pub struct Contract<I: Interface> {
    address: Bytes<20, Private>,
    _interface: PhantomData<fn() -> I>,
}

impl<I: Interface> Clone for Contract<I> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<I: Interface> Copy for Contract<I> {}

impl<I: Interface> Contract<I> {
    /// The callee from an address the contract already holds — a ledger
    /// cell's value, typically (the vault keeps its `stataToken` in one).
    ///
    /// `c` is taken and unused: reinterpreting a limb emits nothing, and the
    /// parameter is here so that adding a check (a non-zero assert, an
    /// allow-list membership) later does not move every call site.
    pub fn from_address<V: Vis3>(_c: &mut Circuit3, address: Bytes<20, V>) -> Self {
        Contract {
            address: Bytes::from_field_unchecked(address.field().private()),
            _interface: PhantomData,
        }
    }

    /// The twenty address bytes.
    pub fn address(&self) -> Bytes<20, Private> {
        self.address
    }
}

impl<I: Interface> CircuitAbi for Contract<I> {
    const SLOTS: usize = <Bytes<20, Private>>::SLOTS;

    fn push_atoms(atoms: &mut Vec<minocrab::AlignmentAtom>) {
        <Bytes<20, Private>>::push_atoms(atoms);
    }

    fn push_prims(prims: &mut Vec<Prim>) {
        <Bytes<20, Private>>::push_prims(prims);
    }
}

impl<I: Interface> CircuitArg for Contract<I> {
    fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
        Contract {
            address: <Bytes<20, Private>>::declare(c, path),
            _interface: PhantomData,
        }
    }

    fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
        self.address.push_slots(slots);
    }
}

// ---- the tickets --------------------------------------------------------------

/// Both tickets carry `(requestId, respond, serializedOutput)` — the wire
/// block `signet_flow::Settle` has, named for the CALL rather than for an
/// environment/response pair.
macro_rules! ticket {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        pub struct $name<F: Filing>
        where
            Ret<Called<F>>: Attestable,
        {
            /// The entry being settled.
            pub request_id: RequestId<Private>,
            /// The MPC's signature in circuit-input form (`bigR.x` and `s`
            /// little-endian; the reversal is the transaction builder's).
            pub respond: Signature<Private>,
            /// `serializedOutput`: the kind byte, then the attested value.
            pub output: Attested<Ret<Called<F>>>,
            _filing: PhantomData<fn() -> F>,
        }

        impl<F: Filing> CircuitAbi for $name<F>
        where
            Ret<Called<F>>: Attestable,
        {
            const SLOTS: usize = <RequestId<Private>>::SLOTS
                + <Signature<Private>>::SLOTS
                + <Attested<Ret<Called<F>>>>::SLOTS;

            fn push_atoms(atoms: &mut Vec<minocrab::AlignmentAtom>) {
                <RequestId<Private>>::push_atoms(atoms);
                <Signature<Private>>::push_atoms(atoms);
                <Attested<Ret<Called<F>>>>::push_atoms(atoms);
            }

            fn push_prims(prims: &mut Vec<Prim>) {
                <RequestId<Private>>::push_prims(prims);
                <Signature<Private>>::push_prims(prims);
                <Attested<Ret<Called<F>>>>::push_prims(prims);
            }
        }

        impl<F: Filing> CircuitArg for $name<F>
        where
            Ret<Called<F>>: Attestable,
        {
            fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
                $name {
                    request_id: <RequestId<Private>>::declare(c, &path.field("requestId")),
                    respond: <Signature<Private>>::declare(c, &path.field("respond")),
                    output: {
                        // Spelled out rather than `Attested::declare` so the
                        // attested value's slot can carry the FILING's own
                        // `RETURN_FIELD` — `success`, `amountIn`, `shares`,
                        // `assets` — where the response record names it.
                        let out = path.field("serializedOutput");
                        let value = out.field("output");
                        let value = match F::RETURN_FIELD {
                            None => value,
                            Some(name) => value.field(name),
                        };
                        Attested {
                            kind: <Uint<8>>::declare(c, &out.field("kind")),
                            output: <Ret<Called<F>>>::declare(c, &value),
                        }
                    },
                    _filing: PhantomData,
                }
            }

            fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
                self.request_id.push_slots(slots);
                self.respond.push_slots(slots);
                self.output.push_slots(slots);
            }
        }
    };
}

ticket!(
    Succeeded,
    "THE CALL EXECUTED AND SUCCEEDED — the only ticket [`Pending::complete`] \
     takes.\n\n\
     The claim is CHECKED, not believed: `complete` asserts the kind, the \
     signature, the record's own kind and version, and then the call's \
     [`EvmCall::succeeded`] predicate. What the ticket's TYPE buys is that a ticket \
     for filing `X` cannot be handed to a slot filed as `Y` — a different \
     call, or the SAME call at another kind — and that a [`Failed`] cannot \
     be handed to `complete` at all."
);

ticket!(
    Failed,
    "THE CALL DID NOT SUCCEED — the only ticket [`Pending::refund`] takes, \
     for both non-successes.\n\n\
     Either the MPC attested its failure kind ([`FAILURE_KIND`]: reverted, \
     never mined, or an undecodable return), or it attested THIS call's kind \
     with a return the call's [`EvmCall::succeeded`] says is not a success (an \
     ERC-20 `transfer` that mined and returned `false`). The wire shape is \
     [`Succeeded`]'s; in the first case the output slots carry the MPC's \
     padding and are not part of the signed preimage."
);

// ---- what survives privately, with a TYPED domain -----------------------------

/// A commitment's DOMAIN, as a type.
///
/// `signet_flow::Commit` takes the domain as a `&str` at both ends, so a
/// `to` and an `open` that disagree is a proof that never verifies — a
/// runtime symptom for a spelling mistake. Here the pad is carried by a
/// marker type, so the disagreement does not compile.
pub trait CommitTag {
    /// The 32-byte pad the digest starts with.
    const PAD: &'static str;
}

/// The owner commitment's domain: the vault's `"vault:refund:"`, so a record
/// and an environment written through [`Owned`] are byte-identical to the
/// ones the deployed lineage writes.
pub struct OwnerTag;

impl CommitTag for OwnerTag {
    const PAD: &'static str = REFUND_PAD;
}

/// A commitment to a private value, stored in an environment and OPENED on
/// the settle side with a fresh witness — the one way a secret crosses the
/// suspension.
///
/// `transientHash([pad(32, Tag::PAD), value, requestId])`, split into a
/// `Bytes<32>`: the construction `signet_flow::Commit` performs, with the
/// domain moved from an argument to a type parameter. Binding the REQUEST ID
/// in is what keeps two requests by one owner unlinkable.
///
/// # What does not compile
///
/// Opening a commitment under another tag — the two are different types:
///
/// ```compile_fail
/// use minocrab::v3::Circuit3;
/// use minocrab_contracts::common::{witness_sk, SecretKey};
/// use minocrab_contracts::evm_flow::{Commit, CommitTag};
/// use minocrab::Private;
/// use minocrab_std::v3::label;
///
/// struct Owner;
/// impl CommitTag for Owner { const PAD: &'static str = "a:"; }
/// struct Beneficiary;
/// impl CommitTag for Beneficiary { const PAD: &'static str = "b:"; }
/// label! { Digest = "digest"; }
///
/// fn f(c: &mut Circuit3, id: signet_signer_interface::RequestId<minocrab::Public>) {
///     let sk = witness_sk(c);
///     let made: Commit<SecretKey<Private>, Owner> = Commit::to::<Digest, _>(c, &sk, id);
///     // ERROR: expected `Commit<_, Beneficiary>`, found `Commit<_, Owner>`
///     let opened: Commit<SecretKey<Private>, Beneficiary> = made;
///     opened.open(c, &sk, id, "nope");
/// }
/// ```
pub struct Commit<T, Tag> {
    digest: B32<Public>,
    _t: PhantomData<fn() -> (T, Tag)>,
}

impl<T, Tag> Clone for Commit<T, Tag> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T, Tag> Copy for Commit<T, Tag> {}

/// WHAT A COMMITMENT IS BOUND TO — the value hashed in after the pad and the
/// committed value, so that one owner's two commitments differ.
///
/// [`RequestId`] is the binding a [`Pending`] request has, and the only one
/// there was until the outbox: the id exists at filing time, so the
/// commitment can name it. An [`Outbox`] request has no id when it is made
/// (the record, hence the id, is created at EMIT — notes/stream-design.org),
/// so it binds to its [`Handle`] instead: the content-derived key the
/// requester keeps.
///
/// The trait exists so that neither binding can be spelled where the other
/// belongs and still hash the same: each pushes its OWN limbs, and the two
/// are different types.
pub trait CommitBinding {
    /// The limbs this binding contributes to the commitment's preimage.
    fn push_binding(&self, inputs: &mut Vec<Wire3<FieldT, Private>>);
}

impl CommitBinding for RequestId<Public> {
    fn push_binding(&self, inputs: &mut Vec<Wire3<FieldT, Private>>) {
        let id = self.bytes();
        inputs.push(id.hi.private());
        inputs.push(id.lo.private());
    }
}

impl CommitBinding for Handle<Public> {
    fn push_binding(&self, inputs: &mut Vec<Wire3<FieldT, Private>>) {
        inputs.push(self.value().private());
    }
}

impl<T: CircuitArg, Tag: CommitTag> Commit<T, Tag> {
    fn digest_of<B: CommitBinding>(c: &mut Circuit3, value: &T, bind: B) -> B32<Private> {
        c.region("signet flow: commitment", |c| {
            let pad = B32::pad(c, Tag::PAD);
            let mut inputs = vec![pad.hi.private(), pad.lo.private()];
            value.push_slots(&mut inputs);
            bind.push_binding(&mut inputs);
            let f = c.transient_hash(&inputs);
            let (hi, lo) = c.div_mod_power_of_two(f, 248);
            B32 { hi, lo }
        })
    }

    /// Commit to `value` for this request, disclosing the digest under `L`
    /// (it is stored, so it is public — the label names it in the disclosure
    /// inventory).
    pub fn to<L: DisclosureLabel, B: CommitBinding>(
        c: &mut Circuit3,
        value: &T,
        bind: B,
    ) -> Self {
        let digest = Self::digest_of(c, value, bind).disclose_as::<L>(c);
        Commit {
            digest,
            _t: PhantomData,
        }
    }

    /// Assert that `value` (a FRESH witness on the settle side) is what this
    /// commitment was made to, for this request.
    pub fn open<B: CommitBinding>(
        &self,
        c: &mut Circuit3,
        value: &T,
        bind: B,
        message: &'static str,
    ) {
        let recomputed = Self::digest_of(c, value, bind);
        let stored = self.digest.private();
        c.assert(
            eq(recomputed.hi, stored.hi)
                .and(eq(recomputed.lo, stored.lo))
                .message(message),
        );
    }
}

impl<T, Tag> ProofWires for Commit<T, Tag> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        self.digest.push_wires(out)
    }
}

impl<T, Tag> LedgerRepr for Commit<T, Tag> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        <B32<Public> as LedgerRepr>::atoms()
    }

    fn push_limbs(&self, c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        LedgerRepr::push_limbs(&self.digest, c, limbs)
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        Commit {
            digest: B32::from_limbs(limbs),
            _t: PhantomData,
        }
    }
}

// ---- the owned environment ----------------------------------------------------

/// "ONLY THE ORIGINAL CALLER MAY REFUND", as an environment wrapper.
///
/// [`Pending::request_owned`] witnesses the caller's secret key and commits
/// it bound to the request id; [`Pending::refund_to_owner`] witnesses a
/// FRESH secret and opens the commitment. [`Pending::complete`] has no
/// method that consumes a secret at all — which is the point: the deployed
/// vault's Gap 2 (a `completeWithdraw` that hoists a secret witness for a
/// refund branch it may not take) is not writable on this API.
pub struct Owned<E> {
    /// The caller, as a commitment bound to this request.
    pub owner: Commit<SecretKey<Private>, OwnerTag>,
    /// Whatever else the settle side needs.
    pub inner: E,
}

impl<E: ProofWires> ProofWires for Owned<E> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        self.owner.push_wires(out);
        self.inner.push_wires(out);
    }
}

impl<E: LedgerRepr> LedgerRepr for Owned<E> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        let mut atoms = <Commit<SecretKey<Private>, OwnerTag> as LedgerRepr>::atoms();
        atoms.extend(E::atoms());
        atoms
    }

    fn push_limbs(&self, c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        LedgerRepr::push_limbs(&self.owner, c, limbs);
        LedgerRepr::push_limbs(&self.inner, c, limbs);
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        let mut limbs = limbs.into_iter();
        let owner = <Commit<SecretKey<Private>, OwnerTag> as LedgerRepr>::from_limbs(
            limbs
                .by_ref()
                .take(repr_limbs::<Commit<SecretKey<Private>, OwnerTag>>())
                .collect(),
        );
        Owned {
            owner,
            inner: E::from_limbs(limbs.collect()),
        }
    }
}

// ---- the slot -----------------------------------------------------------------

/// A suspended EVM CALL: two ledger fields (the MPC-facing record map and
/// the caller's environment map) plus the block's [`Signet`] configuration,
/// typed by the call it makes.
///
/// `F` IS THE FILING, not the call: the call plus this deployment's kind
/// byte and its name for the attested return
/// ([`Kinded<Call, KIND>`](crate::evm::Kinded) for the one-line case). Two
/// slots of one block may file the same Solidity function under two kinds,
/// which is what the deployed vault does with `transfer`, and their tickets
/// still do not unify.
///
/// `WORDS` is the record's calldata capacity. Stable Rust cannot write
/// `EventRecordV2<{ <Call::Args as AbiTuple>::WORDS }>`
/// (`generic_const_exprs`), so the number is NAMED and CHECKED — an
/// inline-`const` assert in the constructor makes a mismatch an
/// `error[E0080]` (notes/evm-calls.org §3).
///
/// The `Signet` handle is built by `#[derive(Ledger)]`, which finds the
/// block's one `Signet` field and threads its offset in
/// ([`Self::at_block_with_signet`]). That is why `request`, `complete` and
/// `refund` take no `&SELF.signet`.
pub struct Pending<F: Filing, Env, const WORDS: usize = 2> {
    records: LedgerMap<RequestId<Public>, EventRecordV2<WORDS>>,
    envs: LedgerMap<RequestId<Public>, Env>,
    signet: Signet,
    _filing: PhantomData<fn() -> F>,
}

impl<F: Filing, Env, const WORDS: usize> Pending<F, Env, WORDS> {
    /// The slot's two fields from flat index `start`, against the block's
    /// `Signet` at `signet_start` — what `#[derive(Ledger)]` emits for a
    /// field whose type is spelled `Pending`.
    pub const fn at_block_with_signet(total: usize, start: usize, signet_start: usize) -> Self {
        const {
            assert!(
                WORDS == <<Called<F> as EvmCall>::Args as AbiTuple>::WORDS,
                "`Pending<F, Env, WORDS>` needs WORDS == <F::Call::Args as \
                 AbiTuple>::WORDS — the record's calldata capacity IS the \
                 call's argument-word count. Stable Rust cannot infer it \
                 (generic_const_exprs), so name the number the argument \
                 tuple encodes to."
            )
        }
        Pending {
            records: LedgerMap::at_block(total, start),
            envs: LedgerMap::at_block(total, start + 1),
            signet: Signet::at_block(total, signet_start),
            _filing: PhantomData,
        }
    }

    /// The record map's ledger path: the notification's `depth ‖ path`.
    pub const fn record_path(&self) -> FieldPath {
        self.records.field_path()
    }
}

// ---- the fire-and-forget slot -------------------------------------------------

/// A CALL THAT IS NEVER SETTLED — Sig Network's fire-and-forget shape (the
/// vault's `approveRouter` and `approveStata`): ONE ledger field, the record
/// map, and [`Fired::request_with`] as its only operation.
///
/// No settle method exists, so "no circuit settles this kind" is a fact about
/// the type rather than a convention. The kind is still claimed in
/// [`LedgerWidth::KINDS`], so no settling slot of the block can share it and
/// an approve ATTESTATION is a kind nothing accepts.
pub struct Fired<F: Filing, const WORDS: usize = 2> {
    records: LedgerMap<RequestId<Public>, EventRecordV2<WORDS>>,
    signet: Signet,
    _filing: PhantomData<fn() -> F>,
}

impl<F: Filing, const WORDS: usize> Fired<F, WORDS> {
    /// The slot's one field at flat index `start`, against the block's
    /// `Signet` at `signet_start` — what `#[derive(Ledger)]` emits for a
    /// field whose type is spelled `Fired`.
    pub const fn at_block_with_signet(total: usize, start: usize, signet_start: usize) -> Self {
        const {
            assert!(
                WORDS == <<Called<F> as EvmCall>::Args as AbiTuple>::WORDS,
                "`Fired<F, WORDS>` needs WORDS == <F::Call::Args as \
                 AbiTuple>::WORDS — the record's calldata capacity IS the \
                 call's argument-word count. Stable Rust cannot infer it \
                 (generic_const_exprs), so name the number the argument \
                 tuple encodes to."
            )
        }
        Fired {
            records: LedgerMap::at_block(total, start),
            signet: Signet::at_block(total, signet_start),
            _filing: PhantomData,
        }
    }

    /// The record map's ledger path: the notification's `depth ‖ path`.
    pub const fn record_path(&self) -> FieldPath {
        self.records.field_path()
    }

    /// File the call and notify the MPC; nothing is kept for a settle.
    /// Discloses `signet_flow::Requested`.
    ///
    /// The shape is [`Pending::request_with`]'s minus the environment: the
    /// callee and the arguments are builders, so a ledger read emits where
    /// the circuit reads it, and `signer` answers whose key signs.
    #[allow(clippy::too_many_arguments)]
    pub fn request_with<I: Extends<Callee<F>>>(
        &self,
        c: &mut Circuit3,
        callee: impl FnOnce(&mut Circuit3) -> Contract<I>,
        args: impl AbiArgs<<Called<F> as EvmCall>::Args>,
        envelope: Envelope,
        key_version: Uint<8>,
        nonce: Uint<64>,
        signer: impl FnOnce(&mut Circuit3) -> SigningPath<Private>,
    ) -> RequestId<Public> {
        let tx = build_tx_with::<Called<F>, WORDS>(
            c,
            |c| callee(c).address,
            args,
            envelope,
            nonce.field(),
            F::GAS_LIMIT,
        );
        let path = signer(c);
        file_request(
            c,
            &self.signet,
            &self.records,
            SignRequest {
                key_version,
                path,
                tx,
            },
            F::KIND,
            |_, _| {},
        )
    }
}

impl<F: Filing, const WORDS: usize> LedgerWidth for Fired<F, WORDS> {
    const KINDS: &'static [u8] = &[F::KIND];
}

impl<F: Filing, Env, const WORDS: usize> LedgerWidth for Pending<F, Env, WORDS> {
    const WIDTH: usize = 2;
    const KINDS: &'static [u8] = &[F::KIND];
}

impl<F: Filing, Env: LedgerRepr, const WORDS: usize> Pending<F, Env, WORDS>
where
    Ret<Called<F>>: Attestable,
{
    /// FILE THE CALL. Builds `F::Call`'s transaction from the callee and the
    /// argument tuple, files the signing record under `F::KIND`, stores the
    /// environment beside it and notifies the singleton with this slot's own
    /// ledger path. Returns the disclosed request id, and discloses
    /// `signet_flow::Requested` plus whatever `env` discloses.
    ///
    /// THE CALLEE IS TYPED BY ITS INTERFACE: any `Contract<I>` whose `I`
    /// [`Extends`] the call's own [`EvmCall::Callee`] is accepted, and
    /// nothing else is.
    ///
    /// `key_version` and `nonce` are still the CALLER'S (the prover picks
    /// the EVM nonce; the MPC's key owns the sequence). Both want a home in
    /// the block or in an administrator-set policy cell — notes/evm-calls.org
    /// §7, the conversation queued after this build.
    pub fn request(
        &self,
        c: &mut Circuit3,
        callee: Contract<impl Extends<Callee<F>>>,
        args: <<Called<F> as EvmCall>::Args as AbiTuple>::Wires<Private>,
        key_version: Uint<8>,
        nonce: Uint<64>,
        env: impl FnOnce(&mut Circuit3, RequestId<Public>) -> Env,
    ) -> RequestId<Public> {
        let tx = build_tx_filed::<F, WORDS>(c, callee.address, args, nonce.field());
        self.file(c, tx, key_version, env)
    }

    /// FILE THE CALL WITH ETHER ATTACHED — [`Self::request`] for a
    /// [`Payable`] call, whose transaction's `value` field is a real amount
    /// rather than the constant zero.
    ///
    /// `Called<F>: Payable` is the gate, and it is a MISSING TRAIT IMPL for
    /// every other call in the library: an amount cannot be handed to an
    /// `erc20::Transfer`, which would ignore it and send the ether nowhere
    /// (notes/evm-interfaces.org §5). WETH's
    /// [`weth::Deposit`](crate::evm::weth::Deposit) is the one call that
    /// has the impl, and the ether IS its argument — `deposit()` has no
    /// calldata beyond the selector.
    ///
    /// Everything else is [`Self::request`]: the same callee bound, the
    /// same environment, the same record, the same disclosures. A payable
    /// call filed through `request` instead carries no ether, which is what
    /// Solidity means by payable — the type does not force an amount, it
    /// forbids one where there is nowhere for it to go.
    ///
    /// The ether comes from the CONTRACT's derived EVM account — the one the
    /// MPC signs for — so a contract that files this must have ether there,
    /// which this API can no more check than it can check a token balance.
    #[allow(clippy::too_many_arguments)]
    pub fn request_payable(
        &self,
        c: &mut Circuit3,
        callee: Contract<impl Extends<Callee<F>>>,
        args: <<Called<F> as EvmCall>::Args as AbiTuple>::Wires<Private>,
        value: Uint<128, Private>,
        key_version: Uint<8>,
        nonce: Uint<64>,
        env: impl FnOnce(&mut Circuit3, RequestId<Public>) -> Env,
    ) -> RequestId<Public>
    where
        Called<F>: Payable,
    {
        let tx = build_tx_payable_filed::<F, WORDS>(c, callee.address, args, value, nonce.field());
        self.file(c, tx, key_version, env)
    }

    /// The shared tail of [`Self::request`] and [`Self::request_payable`]:
    /// the contract's own signing path, the record filed under this slot's
    /// kind, and the environment stored beside it.
    fn file(
        &self,
        c: &mut Circuit3,
        tx: EvmTx<WORDS>,
        key_version: Uint<8>,
        env: impl FnOnce(&mut Circuit3, RequestId<Public>) -> Env,
    ) -> RequestId<Public> {
        let path = SigningPath::contract_path(c).private();
        file_request(
            c,
            &self.signet,
            &self.records,
            SignRequest {
                key_version,
                path,
                tx,
            },
            F::KIND,
            |c, request_id| {
                // The environment is built AFTER the id exists, so a
                // `Commit` in it binds to this request and no other.
                let env = env(c, request_id);
                self.envs.insert(c, &request_id, &env);
            },
        )
    }

    /// [`Self::request`] WITH THE THREE THINGS A DEPLOYED LINEAGE CANNOT LET
    /// THE SLOT CHOOSE — the shape the vault's seventeen circuits need, and
    /// the one `request` is the convenience wrapper over.
    ///
    /// - `callee` and `args` are BUILDERS ([`AbiArgs`]), not values, so a
    ///   ledger read emits exactly where the circuit reads it: `supply` reads
    ///   `vaultEvmAddress` between its two argument words, `approveStata`
    ///   reads its callee after the gas constants. Building them up front
    ///   would move those instructions.
    /// - `envelope` is the fee envelope: [`Envelope::fixed`] for a contract
    ///   that pays its own way, [`Envelope::caller`] for the vault's
    ///   `deposit`, whose transaction is paid from the DEPOSITOR's EVM
    ///   account and whose three gas numbers are therefore circuit arguments.
    /// - `signer` runs AFTER the transaction and BEFORE the record is filed,
    ///   and answers "whose key signs this": it returns the signing path and
    ///   whatever else the environment will need. That is where the vault
    ///   witnesses the secret its refund commitment is made to — after the
    ///   transaction, which is where its deployed stream has it — and where
    ///   `deposit` names the depositor's own commitment as the path instead
    ///   of the contract's.
    ///
    /// A REQUEST STILL CANNOT NAME AN ARBITRARY PATH FROM ITS INPUTS in any
    /// useful sense: the path is built by contract code here, not read off an
    /// argument. `deposit`'s per-user path is a commitment the same circuit
    /// just derived from a witnessed secret.
    #[allow(clippy::too_many_arguments)]
    pub fn request_with<S, I: Extends<Callee<F>>>(
        &self,
        c: &mut Circuit3,
        callee: impl FnOnce(&mut Circuit3) -> Contract<I>,
        args: impl AbiArgs<<Called<F> as EvmCall>::Args>,
        envelope: Envelope,
        key_version: Uint<8>,
        nonce: Uint<64>,
        signer: impl FnOnce(&mut Circuit3) -> (SigningPath<Private>, S),
        env: impl FnOnce(&mut Circuit3, RequestId<Public>, &S) -> Env,
    ) -> RequestId<Public> {
        let tx = build_tx_with::<Called<F>, WORDS>(
            c,
            |c| callee(c).address,
            args,
            envelope,
            nonce.field(),
            F::GAS_LIMIT,
        );
        let (path, carried) = signer(c);
        file_request(
            c,
            &self.signet,
            &self.records,
            SignRequest {
                key_version,
                path,
                tx,
            },
            F::KIND,
            |c, request_id| {
                // The environment is built AFTER the id exists, so a
                // `Commit` in it binds to this request and no other.
                let env = env(c, request_id, &carried);
                self.envs.insert(c, &request_id, &env);
            },
        )
    }

    /// SETTLE A SUCCESS. Asserts the attestation's kind is this slot's,
    /// verifies the MPC's signature over the Poseidon digest of
    /// `(requestId ‖ borsh(kind ‖ output))`, consumes record and
    /// environment, checks the record's own kind and format version — and
    /// then asserts the call's [`EvmCall::succeeded`] predicate.
    ///
    /// ANYONE MAY CALL IT: the attestation is the gate, and no secret is
    /// witnessed. Discloses `signet_flow::Settled`.
    pub fn complete(
        &self,
        c: &mut Circuit3,
        ticket: Succeeded<F>,
    ) -> Outcome<Env, <Called<F> as EvmCall>::Success, WORDS> {
        let request_id = ticket.request_id.disclose_as::<RequestIdSettled>(c);
        let attested = ticket.output;

        c.region("signet flow: attestation", |c| {
            c.assert(
                eq(attested.kind.field(), u64::from(F::KIND)).message("Wrong response kind"),
            );
            let key = self.signet.mpc_response_key.read(c);
            let valid = signet::verify_respond_bidirectional_event_borsh(
                c,
                &request_id.private(),
                &attested,
                &Secp256k1SigLimbs {
                    big_r_x: ticket.respond.big_r.x,
                    s: ticket.respond.s,
                },
                key.point().private(),
            );
            c.assert(valid);
        });

        let (record, env) = self.consume(c, request_id);
        let succeeded = <Called<F> as EvmCall>::succeeded(c, &attested.output);
        c.assert(succeeded.message("The attested call did not succeed"));

        Outcome {
            request_id,
            env,
            // The projection runs AFTER the assert, so nothing a caller can
            // read has escaped the check.
            output: <Called<F> as EvmCall>::map(c, attested.output),
            record,
        }
    }

    /// SETTLE A NON-SUCCESS. Accepts [`FAILURE_KIND`] (reverted, never
    /// mined, undecodable) OR this slot's kind with the [`EvmCall::succeeded`]
    /// predicate false. Discloses `signet_flow::Settled`.
    ///
    /// The two accepted attestations have different preimage LENGTHS (see
    /// the module docs), so the digest is hashed both ways and selected by
    /// the kind byte before the single signature check.
    pub fn refund(
        &self,
        c: &mut Circuit3,
        ticket: Failed<F>,
    ) -> Outcome<Env, Ret<Called<F>>, WORDS> {
        let request_id = ticket.request_id.disclose_as::<RequestIdSettled>(c);
        let attested = ticket.output;

        c.region("signet flow: attestation", |c| {
            // BOTH kinds are legal here, and they sign DIFFERENT preimages:
            // the MPC's failure output is the kind byte alone, this call's
            // output is the kind byte and the return value.
            let is_failure = c.test_eq(attested.kind.field(), u64::from(FAILURE_KIND));

            // Each preimage packed the way the MPC packs it — one byte
            // string, `signet::calculate_attestation_digest_borsh`'s rule
            // (2026-09-07, decisions.org T1) — hashed before the upgrade so
            // the select happens on the raw Poseidon output.
            let rid = request_id.private();
            let executed_digest = signet::attestation_transient_hash_borsh(c, &rid, &attested);
            let failed_digest = signet::attestation_transient_hash_borsh(c, &rid, &attested.kind);

            let digest = c.cond_select(is_failure, failed_digest, executed_digest);
            let digest = upgrade_from_transient(c, digest);

            let key = self.signet.mpc_response_key.read(c);
            let valid = signet::verify_attestation_signature(
                c,
                &digest,
                &Secp256k1SigLimbs {
                    big_r_x: ticket.respond.big_r.x,
                    s: ticket.respond.s,
                },
                key.point().private(),
            );
            c.assert(valid);

            // …and the kind is one of the two this slot accepts, with the
            // EXECUTED one accepted only when the call did not succeed.
            let failure_kind = eq(attested.kind.field(), u64::from(FAILURE_KIND));
            let this_kind = eq(attested.kind.field(), u64::from(F::KIND));
            let succeeded = <Called<F> as EvmCall>::succeeded(c, &attested.output);
            c.assert(
                failure_kind
                    .or(this_kind.and(not(succeeded)))
                    .message("Not a refundable outcome"),
            );
        });

        let (record, env) = self.consume(c, request_id);
        Outcome {
            request_id,
            env,
            output: attested.output,
            record,
        }
    }

    /// Read and remove the record and the environment, and bind the record
    /// to THIS slot (its kind byte and its format version).
    fn consume(
        &self,
        c: &mut Circuit3,
        request_id: RequestId<Public>,
    ) -> (Assumed<EventRecordV2<WORDS>>, Assumed<Env>) {
        c.region("signet flow: consume", |c| {
            let found = self.records.member(c, &request_id);
            c.assert(is_true(found).message("Request not found"));
            let record = self.records.lookup(c, &request_id);
            self.records.remove(c, &request_id);
            let env = self.envs.lookup(c, &request_id);
            self.envs.remove(c, &request_id);
            let kind_ok = c.test_eq(record.response_kind(), u64::from(F::KIND));
            c.assert(kind_ok);
            let version_ok = c.test_eq(record.format_version(), u64::from(RECORD_FORMAT_VERSION));
            c.assert(version_ok);
            (record, env)
        })
    }
}

impl<F: Filing, E: LedgerRepr, const WORDS: usize> Pending<F, Owned<E>, WORDS>
where
    Ret<Called<F>>: Attestable,
{
    /// [`Pending::request`] with the caller's identity committed into the
    /// environment: the secret key is witnessed here and bound to the
    /// request id, and only a prover who can re-witness it may
    /// [`Self::refund_to_owner`].
    ///
    /// `L` labels the commitment in the disclosure inventory (it is stored,
    /// so it is public).
    pub fn request_owned<L: DisclosureLabel>(
        &self,
        c: &mut Circuit3,
        callee: Contract<impl Extends<Callee<F>>>,
        args: <<Called<F> as EvmCall>::Args as AbiTuple>::Wires<Private>,
        key_version: Uint<8>,
        nonce: Uint<64>,
        inner: impl FnOnce(&mut Circuit3, RequestId<Public>) -> E,
    ) -> RequestId<Public> {
        let sk = common::witness_sk(c);
        self.request(c, callee, args, key_version, nonce, |c, request_id| Owned {
            owner: Commit::to::<L, _>(c, &sk, request_id),
            inner: inner(c, request_id),
        })
    }

    /// [`Pending::refund`] with the OWNER GATE: a fresh secret is witnessed
    /// and the stored commitment is opened against it, and the caller's own
    /// public key comes back as the recipient.
    ///
    /// `L` labels that public key. There is deliberately no `complete`
    /// counterpart — a completion never opens the commitment and never
    /// witnesses a secret.
    pub fn refund_to_owner<L: DisclosureLabel>(
        &self,
        c: &mut Circuit3,
        ticket: Failed<F>,
    ) -> (ZswapCoinPublicKey<Public>, Assumed<E>, Ret<Called<F>>) {
        let outcome = self.refund(c, ticket);
        let sk = common::witness_sk(c);
        outcome
            .env
            .owner
            .open(c, &sk, outcome.request_id, "Not the owner");
        let owner = own_public_key(c).disclose_as::<L>(c);
        (owner, outcome.env.map(|e| e.inner), outcome.output)
    }
}

// ---- the outbox: a request that does not choose its nonce -------------------------

label! {
    /// The pre-record a call files: the callee, the key version and the
    /// calldata words the emit will build a transaction from. Stored, so
    /// public — and no more public than a `Pending` request's calldata,
    /// which is disclosed into the record in the same way, one transaction
    /// later.
    pub QueuedRecordFiled = "queued pre-record";
}

/// Everything [`Outbox::call`] discloses, as one type — the label set a
/// call circuit declares, [`crate::signet_flow::Requested`]'s twin for the
/// write-side half of an outbox request. There is no notification and no
/// request id yet, so the record and the two cross-call labels are not in it.
pub type Inserted = (QueuedRecordFiled,);

/// THE OUTBOX KEY, and what the requester keeps: the Poseidon hash of the
/// pre-record (callee, key version, calldata words) — content-derived, so
/// unsquattable and computed by anyone who knows the request; the request
/// id MINUS the nonce (notes/stream-design.org, "emit restored").
///
/// Two byte-identical requests share a handle, so the second is refused
/// while the first is between call and emit and accepted after: the
/// spec's C1 behaviour for identical payloads, one phase earlier. It is NOT
/// a request id and does not unify with one: an attestation settles a
/// `RequestId`, which includes the nonce the emit assigned.
///
/// Visibility-generic like the leaves, and like them `Private` by default:
/// an `emit` circuit takes a `Handle` argument and discloses it; the ledger
/// keys on `Handle<Public>`.
#[derive(Clone, Copy)]
pub struct Handle<V: Vis3 = Private>(Wire3<FieldT, V>);

impl<V: Vis3> Handle<V> {
    /// The hash, as a field element.
    pub fn value(self) -> Wire3<FieldT, V> {
        self.0
    }

    /// A handle from a field element already in hand. UNCHECKED: nothing
    /// ties it to a pre-record; [`PreRecord::handle`] is the constructor
    /// that does.
    pub fn from_field_unchecked(w: Wire3<FieldT, V>) -> Self {
        Handle(w)
    }
}

impl ProofWires for Handle<Public> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        out.push(self.0.val());
    }
}

impl LedgerRepr for Handle<Public> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        vec![minocrab::AlignmentAtom::Field]
    }

    fn push_limbs(&self, _c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        limbs.push(self.0);
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        assert_eq!(limbs.len(), 1, "a handle is one field limb");
        Handle(limbs[0])
    }
}

impl<V: Vis3> CircuitAbi for Handle<V> {
    const SLOTS: usize = 1;

    fn push_atoms(atoms: &mut Vec<minocrab::AlignmentAtom>) {
        atoms.push(minocrab::AlignmentAtom::Field);
    }

    fn push_prims(prims: &mut Vec<Prim>) {
        prims.push(Prim::Field);
    }
}

impl CircuitArg for Handle<Private> {
    fn declare(c: &mut Circuit3, path: &ArgPath) -> Self {
        Handle(c.arg::<FieldT>(path.as_str()))
    }

    fn push_slots(&self, slots: &mut Vec<Wire3<FieldT, Private>>) {
        slots.push(self.0);
    }
}

impl Disclose for Handle<Private> {
    type Public = Handle<Public>;

    fn disclose_as<L: DisclosureLabel>(self, c: &mut Circuit3) -> Handle<Public> {
        Handle(self.0.disclose_as::<L>(c))
    }
}

/// THE TRANSACTION MINUS ITS NONCE — what a call files and an emit turns
/// into a record.
///
/// Three fields, and they are exactly the three an emit cannot derive from
/// the call type: the callee, the key version, and the encoded ABI words.
/// Everything else in the transaction is the CONTRACT'S — the selector, the
/// word count and the gas limit from [`EvmCall`], the fee envelope from the
/// contract (notes/nonce-admin.org §1.1: a requester picks neither a nonce
/// nor a fee, because an unminable transaction is a denial of service on
/// every later nonce of the path), the chain ids from the [`Signet`] block,
/// and the nonce from the outbox's accumulator, snapshotted at the call.
pub struct PreRecord<const WORDS: usize>(Vec<Wire3<FieldT, Public>>);

impl<const WORDS: usize> PreRecord<WORDS> {
    /// One limb for the callee, one for the key version, two per word.
    pub const LIMBS: usize = 2 + 2 * WORDS;

    /// Assemble and DISCLOSE the pre-record: it is about to be stored, so
    /// every limb is public, and the label names them in the inventory.
    fn file(
        c: &mut Circuit3,
        callee: Bytes<20, Private>,
        key_version: Uint<8>,
        words: &[B32<Private>],
    ) -> Self {
        let mut limbs = vec![callee.field(), key_version.field()];
        for word in words {
            limbs.push(word.hi);
            limbs.push(word.lo);
        }
        PreRecord(limbs.disclose_as::<QueuedRecordFiled>(c))
    }

    /// The [`Handle`]: a Poseidon hash over the disclosed limbs, computed
    /// once at the call (it has no k pressure) and again by whoever emits.
    pub fn handle(&self, c: &mut Circuit3) -> Handle<Public> {
        Handle(transient_hash_compact(c, &self.0))
    }

    fn callee(&self) -> Bytes<20, Private> {
        Bytes::from_field_unchecked(self.0[0].private())
    }

    fn key_version(&self) -> Uint<8> {
        Uint::from_field_unchecked(self.0[1].private())
    }

    fn words(&self) -> [B32<Private>; WORDS] {
        core::array::from_fn(|i| B32 {
            hi: self.0[2 + 2 * i].private(),
            lo: self.0[3 + 2 * i].private(),
        })
    }
}

impl<const WORDS: usize> ProofWires for PreRecord<WORDS> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        out.extend(self.0.iter().map(|w| w.val()));
    }
}

impl<const WORDS: usize> LedgerRepr for PreRecord<WORDS> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        let mut atoms = <Bytes<20, Public> as LedgerRepr>::atoms();
        atoms.extend(<Uint<8, Public> as LedgerRepr>::atoms());
        for _ in 0..WORDS {
            atoms.extend(<B32<Public> as LedgerRepr>::atoms());
        }
        atoms
    }

    fn push_limbs(&self, _c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        limbs.extend_from_slice(&self.0);
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        assert_eq!(
            limbs.len(),
            Self::LIMBS,
            "a {WORDS}-word pre-record takes {} limbs",
            Self::LIMBS
        );
        PreRecord(limbs)
    }
}

/// ONE QUEUE ENTRY: the pre-record and the environment, in one map value.
///
/// They are stored together because they are inserted together, emitted
/// together and removed together — one `insert`, one `lookup`, one `remove`
/// rather than three of each, and no state in which a pre-record has lost
/// its environment.
pub struct QueueEntry<Env, const WORDS: usize> {
    /// The transaction minus its nonce.
    pub pre: PreRecord<WORDS>,
    /// What the settle side will need, moved verbatim into the `Pending`
    /// environment map under the request id at flush.
    pub env: Env,
}

impl<Env: ProofWires, const WORDS: usize> ProofWires for QueueEntry<Env, WORDS> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        self.pre.push_wires(out);
        self.env.push_wires(out);
    }
}

impl<Env: LedgerRepr, const WORDS: usize> LedgerRepr for QueueEntry<Env, WORDS> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        let mut atoms = <PreRecord<WORDS> as LedgerRepr>::atoms();
        atoms.extend(Env::atoms());
        atoms
    }

    fn push_limbs(&self, c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        LedgerRepr::push_limbs(&self.pre, c, limbs);
        LedgerRepr::push_limbs(&self.env, c, limbs);
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        let mut limbs = limbs.into_iter();
        let pre = <PreRecord<WORDS> as LedgerRepr>::from_limbs(
            limbs.by_ref().take(PreRecord::<WORDS>::LIMBS).collect(),
        );
        QueueEntry {
            pre,
            env: Env::from_limbs(limbs.collect()),
        }
    }
}

/// [`Owned`] FOR AN OUTBOX REQUEST: the commitment binds to the HANDLE,
/// because there is no request id when the request is made.
///
/// The handle is stored beside the commitment for one reason: the settle
/// side has only the request id, and the commitment does not open under it.
/// Carrying the handle in the environment is what lets a refund happen with
/// the requester never present at the emit (notes/nonce-admin.org §4(ii)).
pub struct HandleOwned<E> {
    /// The outbox key this request was filed under.
    pub handle: Handle<Public>,
    /// The requester, as a commitment bound to that handle.
    pub owner: Commit<SecretKey<Private>, OwnerTag>,
    /// Whatever else the settle side needs.
    pub inner: E,
}

impl<E: ProofWires> ProofWires for HandleOwned<E> {
    fn push_wires(&self, out: &mut Vec<Val>) {
        self.handle.push_wires(out);
        self.owner.push_wires(out);
        self.inner.push_wires(out);
    }
}

impl<E: LedgerRepr> LedgerRepr for HandleOwned<E> {
    fn atoms() -> Vec<minocrab::AlignmentAtom> {
        let mut atoms = <Handle<Public> as LedgerRepr>::atoms();
        atoms.extend(<Commit<SecretKey<Private>, OwnerTag> as LedgerRepr>::atoms());
        atoms.extend(E::atoms());
        atoms
    }

    fn push_limbs(&self, c: &mut Circuit3, limbs: &mut Vec<Wire3<FieldT, Public>>) {
        LedgerRepr::push_limbs(&self.handle, c, limbs);
        LedgerRepr::push_limbs(&self.owner, c, limbs);
        LedgerRepr::push_limbs(&self.inner, c, limbs);
    }

    fn from_limbs(limbs: Vec<Wire3<FieldT, Public>>) -> Self {
        let mut limbs = limbs.into_iter();
        let handle = <Handle<Public> as LedgerRepr>::from_limbs(
            limbs.by_ref().take(repr_limbs::<Handle<Public>>()).collect(),
        );
        let owner = <Commit<SecretKey<Private>, OwnerTag> as LedgerRepr>::from_limbs(
            limbs
                .by_ref()
                .take(repr_limbs::<Commit<SecretKey<Private>, OwnerTag>>())
                .collect(),
        );
        HandleOwned {
            handle,
            owner,
            inner: E::from_limbs(limbs.collect()),
        }
    }
}

mod outbox;

pub use outbox::{Emitted, HandleEmitted, Outbox, OutboxSpec, Outstanding};
