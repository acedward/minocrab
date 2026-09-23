//! THE DISCRIMINATOR (notes/ledger-header.org): one generic, off-chain
//! function from a contract's ledger state to the 32 bytes at its first
//! leaf — the magic a standard (`#[derive(LedgerHeader)]`) claims `root[0]`
//! for — with no per-contract code.
//!
//! THE RULE, all of it:
//!
//! - From the root, follow index 0 while the node is an Array: at least one
//!   step (the root is the block, and its entries are the fields) and at
//!   most three (compactc nests a block at most twice, [`MAX_FIELD_PATH`]).
//! - The node reached must be a Cell whose alignment is exactly ONE
//!   `bytes<32>` atom, holding one atom of at most 32 bytes.
//! - The ledger stores a `Bytes<32>` with its trailing zero bytes dropped
//!   (FAB normal form: `pad32("mip-0099:ledger-header[v1]")` is stored as 26
//!   bytes), so the atom is right-padded back to 32. That is the
//!   discriminator.
//! - Anything else is `None`: a first leaf that is Null, a Map, a Merkle
//!   tree, an EMPTY List, a Cell of any other alignment (a Counter's
//!   `bytes<8>`, a `Bytes<16>`, a `Maybe` or a struct of several atoms), a
//!   root that is not an Array or is empty, or an Array still at the fourth
//!   step. A List that has been pushed to is `[head, tail, length]`, the
//!   shape of a three-field block, so the walk reads its head (below).
//!
//! One rule finds a minocrab header of either shape (`[0]` magic-only,
//! `[0, 0]` with fields) and a plain Compact contract that declares or
//! imports a `Bytes<32>` magic first, at every size (`[0]`, `[0, 0]`,
//! `[0, 0, 0]`). The reader keeps no registry: a contract whose first leaf
//! happens to be some other 32-byte cell — an owner key, or 32 zero bytes
//! never written — yields that value, and matching it against known magics
//! is the caller's ([`implements`] does it for one standard).
//!
//! A DISCRIMINATOR IS A CLAIM, NOT PROOF.
//! - The deploy state is the deployer's own claim: the ledger checks that
//!   it is a valid state tree, not which values it holds or where, and no
//!   proof covers it. Anyone can deploy any magic.
//! - A maintenance authority can install a circuit that writes `root[0]`
//!   later. A reader that relies on the magic re-reads after every
//!   `ContractUpdate`, or requires a frozen authority (an empty committee
//!   with a threshold of at least one — the ledger's default).
//! - A first leaf that a circuit can write — a public `Bytes<32>` cell, the
//!   head of a `List<Bytes<32>>`, or a standard's magic named by a
//!   hand-written path — is controlled by whoever may call that circuit.
//!   So on a contract that is not headed, [`implements`] says nothing about
//!   its code, and on a headed one only as much as its circuits allow.
//! - What says a contract RUNS the standard's code is its verifier keys:
//!   pair this read with a verifier-key comparison where it matters.
//!
//! Pure and off-chain: nothing here emits a circuit instruction, and nothing
//! here writes.

use midnight_onchain_state::state::{ContractState, StateValue};
use midnight_storage::db::{InMemoryDB, DB};
use minocrab::{AlignmentAtom, AlignmentSegment};

use super::header::{assert_magic, LedgerHeader};
use super::ledger::MAX_FIELD_PATH;

/// The most index-0 steps the reader takes — FROZEN at three as part of the
/// rule every reader implements (FR-008), not as a mirror of the layout's
/// [`MAX_FIELD_PATH`]. The two are the same fact today; if the layout's
/// bound ever moves, the assertion below stops the build so the reader's
/// rule is changed on purpose or not at all.
const MAX_STEPS: usize = 3;

const _: () = assert!(
    MAX_STEPS == MAX_FIELD_PATH,
    "the discriminator's step bound is frozen at three: a field path of another length needs a \
     decision about the reader's rule (notes/ledger-header.org), not a silent change"
);

/// The 32 bytes at `state`'s first leaf, by the rule in the module docs, or
/// `None` when the first leaf is not a single `bytes<32>` Cell.
///
/// ```
/// use minocrab_std::v3::{discriminator, pad32, Ledger, LedgerCounter, LedgerHeader};
///
/// #[derive(LedgerHeader)]
/// struct Mip0099;
/// impl LedgerHeader for Mip0099 {
///     const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
/// }
///
/// #[derive(Ledger)]
/// struct Headed {
///     count: LedgerCounter,
///     std: Mip0099,
/// }
/// #[derive(Ledger)]
/// struct Plain {
///     count: LedgerCounter,
/// }
///
/// assert_eq!(discriminator(&Headed::initial_state().build()), Some(Mip0099::MAGIC));
/// assert_eq!(discriminator(&Plain::initial_state().build()), None); // a Counter first
/// ```
pub fn discriminator<D: DB>(state: &StateValue<D>) -> Option<[u8; 32]> {
    let mut node = state;
    let mut steps = 0;
    while let StateValue::Array(items) = node {
        if steps == MAX_STEPS {
            return None;
        }
        node = items.get(0)?;
        steps += 1;
    }
    if steps == 0 {
        return None;
    }
    let StateValue::Cell(cell) = node else {
        return None;
    };
    let [AlignmentSegment::Atom(AlignmentAtom::Bytes { length: 32 })] = cell.alignment.0.as_slice()
    else {
        return None;
    };
    let [atom] = cell.value.0.as_slice() else {
        return None;
    };
    if atom.0.len() > 32 {
        return None;
    }
    let mut padded = [0u8; 32];
    padded[..atom.0.len()].copy_from_slice(&atom.0);
    Some(padded)
}

/// [`discriminator`] of a SERIALIZED, TAGGED `ContractState` — the bytes the
/// node's `midnight_contractState` and the indexer's `state` field carry
/// (hex-decoded), a deploy's initial state or a later one. The pinned
/// ledger's own `tagged_deserialize` reads them, so the tag
/// (`midnight:contract-state[v8]:` on ledger 9) and every storage invariant
/// are checked, and trailing bytes are refused.
///
/// `Err` when the bytes are not a `ContractState` of this ledger version;
/// `Ok(None)` when they are one whose `data` has no discriminator.
pub fn contract_state_discriminator(bytes: &[u8]) -> std::io::Result<Option<[u8; 32]>> {
    let contract: ContractState<InMemoryDB> = midnight_serialize::tagged_deserialize(bytes)?;
    Ok(discriminator(contract.data.get_ref()))
}

/// Whether `state` carries the standard `S`'s magic at its first leaf:
/// [`discriminator`] equal to `S::MAGIC`. The stored atom is compared padded
/// back to 32 bytes, so a magic that ends in zero bytes (the ledger stores
/// it trimmed) matches exactly when its trimmed bytes are what is stored.
///
/// True means the contract CLAIMS the standard (see the module docs), not
/// that it implements it.
///
/// `S::MAGIC` all zero is E0080 here too, however `S` was written: 32 zero
/// bytes are what a never-written `Bytes<32>` first field holds, so such an
/// `S` would be "implemented" by every contract that starts with one. The
/// check is an inline `const` evaluated when the call is monomorphized, so
/// the error surfaces in `cargo build` / `cargo test`, not in `cargo check`,
/// clippy or rust-analyzer (the placement check, which `#[derive(Ledger)]`
/// evaluates in a free `const`, surfaces in `cargo check` too).
pub fn implements<S: LedgerHeader>(state: &StateValue<impl DB>) -> bool {
    const { assert_magic(&S::MAGIC) };
    discriminator(state) == Some(S::MAGIC)
}
