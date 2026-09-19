//! L2.5 — ledger-op emission.
//!
//! A circuit's ledger operations surface as Impact instructions whose
//! elements are exactly `Op::field_repr` (midnight-onchain-vm
//! `src/ops.rs:460-525`) of the corresponding Impact-VM op — see
//! notes/ledger-abi.org §2. This crate builds those element streams:
//! fully-constant ops go through the real [`Op`] type and its
//! `field_repr` (never hand-encoded); ops embedding circuit-computed
//! values reproduce the same layout with wires spliced into the value
//! positions, and the constant header layout is unit-tested against
//! `field_repr` of real ops.
//!
//! Op sequences per ledger operation are compactc's vm-code
//! (corpus/src/compact/compiler/midnight-ledger.ss, assembled by
//! zkir-v3-passes/reduce-to-zkir.ss:484-633), with its suppression rules:
//! top-level Cell writes lose their idxp/insc wrapper; the first fetch of
//! a field is always the *uncached* idx variant.
//!
//! # Where this sits
//!
//! L2.5: above the [`minocrab`] eDSL (L2), whose wires it splices into op
//! element streams, and below `minocrab-std` (L3), whose `v3::ledger` and
//! `v3::kernel` types are one-line wrappers over the functions here. That
//! layering is deliberate — the ADTs sit *above* the ops, so this crate stays
//! the pure op layer and gains no dependency of its own. Contract code should
//! use the typed slots in `minocrab-std`; reach for this crate to emit an
//! operation those do not cover, or to read what the encoding actually is.
//!
//! # Start here
//!
//! - [`ImpactOp`] and [`ImpactElem`] — one Impact instruction, as the element
//!   stream `Op::field_repr` would produce
//! - [`LedgerValue`] — a FAB-aligned value whose limbs may be
//!   circuit-computed
//! - [`cell_write`], [`map_insert`], [`counter_increment`] — writes, as
//!   compactc's vm-code sequences them
//! - [`cell_read`], [`map_lookup`], [`counter_read`] — reads, which return
//!   wires and record their disclosure
//! - [`contract_call`] — a cross-contract call, and the labels it discloses
//!   ([`XcallEntryPointHash`], [`XcallCommitment`], [`XcallResult`])
//!
//! # Stability (M24 tier boundary)
//!
//! INTERNAL TIER, whole crate: the Impact op layer is the eDSL's
//! implementation detail (reached through `minocrab-std`'s typed ledger
//! surface) and carries no stability promise.
//!
//! [`Op`]: midnight_onchain_vm::ops::Op

mod calls;
mod impact;
mod kernel;
mod ops;
mod reads;
#[cfg(test)]
mod tests;

pub use calls::{
    bind_entry_points, call, contract_call, ep_hash, ep_limbs, BindEntryPoints, Callee,
    EntryPoint, XcallCommitment, XcallEntryPointHash, XcallResult,
};
pub use impact::{
    atom_limbs, default_value, dup, field_key, idx_key, idx_key_cached, idx_one, idx_path,
    push_array, push_cell, render_path, swap, ImpactOp, LedgerElem, LedgerKey, LedgerValue, VmOp,
};
pub use kernel::{
    kernel_balance, kernel_block_time, kernel_claim_contract_call,
    kernel_claim_unshielded_coin_spend, kernel_claim_zswap_coin_receive,
    kernel_claim_zswap_coin_spend, kernel_claim_zswap_nullifier, kernel_inc_unshielded_inputs,
    kernel_inc_unshielded_outputs, kernel_mint_shielded, kernel_mint_unshielded, kernel_self,
    BalanceCmp,
};
pub use ops::{
    branch, cell_add_at, cell_and_at, cell_copy_at, cell_max_at, cell_min_at, cell_or_at,
    cell_snapshot_into_map_at, cell_sub_at, cell_write_first_at, jmp, lt, map_move_entry_at,
    member, neg, pop, type_of,
    cell_write, cell_write_at, cell_write_coin, cell_write_coin_at, counter_increment,
    counter_increment_at, counter_reset, counter_reset_at, empty_counter,
    empty_historic_merkle_tree_value, empty_list, empty_map, empty_merkle_tree_value, emit_event,
    historic_merkle_tree_insert, historic_merkle_tree_insert_at, historic_merkle_tree_insert_index,
    historic_merkle_tree_insert_index_at, historic_merkle_tree_reset, historic_merkle_tree_reset_at,
    historic_merkle_tree_reset_history, historic_merkle_tree_reset_history_at, list_pop_front,
    list_pop_front_at, list_push_front, list_push_front_at, list_push_front_coin,
    list_push_front_coin_at, list_reset, list_reset_at, map_insert, map_insert_adt_default_at,
    map_insert_at, map_insert_coin, map_insert_coin_at, map_insert_default, map_insert_default_at,
    map_remove, map_remove_at, map_reset, map_reset_at, merkle_tree_insert, merkle_tree_insert_at,
    merkle_tree_insert_index, merkle_tree_insert_index_at, merkle_tree_reset, merkle_tree_reset_at,
    set_insert, set_insert_at, set_insert_coin, set_insert_coin_at, set_remove, set_remove_at,
    set_reset, set_reset_at,
};
pub use reads::{
    cell_read, cell_read_at, cell_read_embedded, cell_read_embedded_at,
    counter_less_than, counter_less_than_at, counter_read, counter_read_at,
    emit, historic_merkle_tree_check_root,
    historic_merkle_tree_check_root_at, list_head, list_head_at, list_is_empty, list_is_empty_at,
    list_length, list_length_at, map_is_empty, map_is_empty_at, map_lookup, map_lookup_at,
    map_member, map_member_at,
    map_size, map_size_at, merkle_tree_check_root, merkle_tree_check_root_at,
    merkle_tree_is_full, merkle_tree_is_full_at, mint_read, popeq, set_is_empty,
    set_is_empty_at, set_size, set_size_at,
};

pub use minocrab::v3::LimbConstraint;

pub use minocrab::v3::ImpactElem;
