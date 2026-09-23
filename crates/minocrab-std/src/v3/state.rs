//! THE DEPLOY STATE (notes/ledger-header.org): a `#[derive(Ledger)]`
//! block's initial ledger state, built off-chain from its layout.
//!
//! compactc's generated `initialState` builds a contract's deploy state in
//! two phases (notes/ledger-abi.org "Initial state"): a SKELETON of nested
//! Arrays of Null, one entry per field at its segmented path, then every
//! field's `resetToDefault` run through the Impact VM. [`StateBuilder`] is
//! the same thing without the VM: every slot of a block contributes its
//! initial value at its own path ([`InitialState`]), and
//! [`StateBuilder::build`] assembles the tree — each Array as long as its
//! highest index plus one, every entry nothing contributed to Null.
//! compactc's layouts are dense, so that IS its skeleton, and each value is
//! the one its reset writes:
//!
//! | slot | initial value | from `minocrab_ledger` |
//! |---|---|---|
//! | `LedgerCell<T>` | `T`'s default, stored ([`super::LedgerRepr::default_stored`]) | [`stored_cell`] |
//! | `LedgerCounter` | `cell 0u64` | `empty_counter` |
//! | `LedgerMap`, `LedgerSet` | the empty map | `empty_map` |
//! | `LedgerList` | `[null, null, cell 0u64]` | `empty_list` |
//! | `LedgerMerkleTree<D, _>` | `[blank tree of height D, cell 0u64]` | `empty_merkle_tree_value` |
//! | `LedgerHistoricMerkleTree<D, _>` | the same plus `{blank root → null}` | `historic_merkle_tree_reset_value` |
//! | `LedgerField` | Null — untyped, so no default; [`StateBuilder::set`] it | — |
//! | a group slot (`Signet`, `Pending`, `Fired`, `Outbox`, `Stream`) | its members' | — |
//! | a standard (`#[derive(LedgerHeader)]`) | its magic, sealed, and its fields' defaults | [`stored_cell`] |
//!
//! — the constants the circuits' own `resetToDefault` ops push, not a second
//! table. The magic is the standard's `LedgerHeader::MAGIC`, stored the way
//! compactc's constructor writes a `Bytes<32>` (trailing zero bytes dropped),
//! so NO circuit ever writes it.
//!
//! What compactc's constructor would write besides — a sealed signer
//! address, an owner — is the deployer's: [`StateBuilder::set`] replaces a
//! declared slot's value, and refuses anything else (a path the block does
//! not declare, a different shape, the magic). A blind accumulator starts at
//! its cell's default, which is the identity of `Add`, `Max` and `Or` and
//! not of `Min` or `And`: a stream that must start at the identity is `set`.
//!
//! OFF-CHAIN ONLY: nothing here emits a circuit instruction, and the derive's
//! `initial_state()` is calls and paths (THINNESS RULE). The state is a
//! claim the deployer makes; the ledger does not check its shape
//! (notes/ledger-header.org "claim, not proof").

use std::collections::BTreeMap;

use midnight_onchain_state::state::StateValue;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::Array;
use minocrab::AlignmentAtom;
use minocrab_ledger::stored_cell;

use super::header::Magic;
use super::ledger::FieldPath;

/// The ledger's Array bound (onchain-state `state.rs`: `len() > 16` is an
/// invalid `StateValue`).
const MAX_ARRAY: usize = 16;

/// A slot type's share of its block's DEPLOY-TIME state: its initial value
/// at the path it was laid out at (see the module docs for each type's).
///
/// Every slot of a `#[derive(Ledger)]` block implements it, because the
/// derive's `initial_state()` calls it on every field. A group slot
/// delegates to its members; a slot that only REFERS to another slot's
/// fields (a `Pending`'s copy of the block's `Signet`) contributes nothing
/// for them — the owner does.
#[diagnostic::on_unimplemented(
    message = "`{Self}` has no deploy-time state",
    label = "every slot of a `#[derive(Ledger)]` block contributes its initial value to `initial_state()`",
    note = "implement `InitialState` for a custom slot type: write each field it occupies at its \
            path (a group slot calls its members' `contribute`)"
)]
pub trait InitialState {
    /// Write this slot's initial value(s) into `state`, each at its path.
    fn contribute(&self, state: &mut StateBuilder);
}

/// Tuples of slots — a tuple step's accumulator and snapshot maps
/// (`blind::Primitive::Acc`) — contribute componentwise.
macro_rules! tuple_states {
    ($( ($($t:ident $i:tt),+) ),* $(,)?) => {$(
        impl<$($t: InitialState),+> InitialState for ($($t,)+) {
            fn contribute(&self, state: &mut StateBuilder) {
                $( self.$i.contribute(state); )+
            }
        }
    )*};
}

tuple_states! {
    (A 0, B 1),
    (A 0, B 1, C 2),
    (A 0, B 1, C 2, D 3),
}

/// One declared slot of the tree under construction.
struct Slot {
    value: StateValue<InMemoryDB>,
    /// A standard's magic: [`StateBuilder::set`] refuses it.
    sealed: bool,
}

/// A block's deploy-time state, slot by slot, and the tree it assembles.
///
/// Returned by the `initial_state()` that `#[derive(Ledger)]` gives every
/// block, with each slot's initial value already in:
///
/// ```
/// use minocrab::Public;
/// use minocrab_std::v3::{Ledger, LedgerCell, LedgerCounter, LedgerField, Uint};
///
/// #[derive(Ledger)]
/// struct Block {
///     value: LedgerCell<Uint<64, Public>>,
///     count: LedgerCounter,
///     signer: LedgerField, // sealed, written by the deployer
/// }
/// const BLOCK: Block = Block::new();
///
/// let mut state = Block::initial_state();
/// // What a Compact constructor would have written: the builder leaves an
/// // untyped `LedgerField` Null, since it cannot know its type.
/// state.set(
///     BLOCK.signer.field_path(),
///     minocrab_ledger::stored_cell(
///         vec![minocrab::AlignmentAtom::Bytes { length: 32 }],
///         vec![vec![0x5a; 32]],
///     ),
/// );
/// let _data = state.build(); // Array(3): the cell, the counter, the address
/// ```
///
/// Paths are kept in a sorted map, so the tree is the same whatever order
/// the slots arrive in.
#[derive(Default)]
pub struct StateBuilder {
    slots: BTreeMap<Vec<u8>, Slot>,
}

impl StateBuilder {
    /// An empty tree: a block with no fields builds the empty root Array
    /// (compactc's `StateValue.newArray()` with nothing pushed).
    pub fn new() -> Self {
        StateBuilder::default()
    }

    /// DECLARE a slot: `value` is its initial value at `path`. What every
    /// [`InitialState`] impl calls, once per field it occupies.
    ///
    /// Panics when `path` is already declared, or is a prefix of a declared
    /// path (or the reverse): two slots of one layout cannot overlap, so
    /// either is a bug in a slot type's `contribute`, not a state.
    pub fn slot(&mut self, path: FieldPath, value: StateValue<InMemoryDB>) {
        self.declare(path, value, false);
    }

    /// A standard's MAGIC at its path — a `Bytes<32>` Cell, stored in FAB
    /// normal form, as compactc's constructor writes `pad(32, "…")` — and
    /// SEALED: [`Self::set`] refuses it. For `#[derive(LedgerHeader)]`'s
    /// expansion.
    #[doc(hidden)]
    pub fn magic(&mut self, magic: Magic, value: &[u8; 32]) {
        let cell = stored_cell(
            vec![AlignmentAtom::Bytes { length: 32 }],
            vec![value.to_vec()],
        );
        self.declare(magic.field_path(), cell, true);
    }

    fn declare(&mut self, path: FieldPath, value: StateValue<InMemoryDB>, sealed: bool) {
        let path = path.as_slice().to_vec();
        for declared in self.slots.keys() {
            let shorter = declared.len().min(path.len());
            assert!(
                declared[..shorter] != path[..shorter],
                "two slots of one ledger block contributed overlapping paths {declared:?} and \
                 {path:?}: a layout gives every field its own path, so a slot type's \
                 `InitialState::contribute` wrote outside its fields"
            );
        }
        self.slots.insert(path, Slot { value, sealed });
    }

    /// REPLACE a declared slot's initial value — what a Compact constructor
    /// would write at deploy (a sealed signer address, an owner), or a
    /// stream accumulator that starts at its step's identity.
    ///
    /// Only a slot the block declares, and only with a value of the same
    /// SHAPE: a Cell for a Cell (and at the same alignment, so the
    /// circuits' reads still match), a Map for a Map, an Array for an
    /// Array. A `LedgerField` is untyped (Null), so any value may replace
    /// it. A standard's magic cannot be replaced: it is the standard's
    /// constant. Each refusal panics, naming the rule — the path and the
    /// value are the deployer's, known only at run time.
    pub fn set(&mut self, path: FieldPath, value: StateValue<InMemoryDB>) -> &mut Self {
        let key = path.as_slice();
        let Some(slot) = self.slots.get_mut(key) else {
            panic!(
                "StateBuilder::set: {key:?} is not a slot of this block — `set` replaces a \
                 declared slot's initial value (take the path from the block's own handle, \
                 e.g. `BLOCK.owner.field_path()`); it cannot add a ledger field"
            );
        };
        assert!(
            !slot.sealed,
            "StateBuilder::set: {key:?} is a standard's magic — the standard's own constant \
             (`LedgerHeader::MAGIC`), sealed by the builder; a deploy state cannot carry another"
        );
        assert!(
            same_shape(&slot.value, &value),
            "StateBuilder::set: the value for {key:?} is not the slot's shape — a Cell replaces \
             a Cell of the same alignment, a Map a Map, an Array an Array (a `LedgerField` is \
             the only slot that takes any value)"
        );
        slot.value = value;
        self
    }

    /// A declared slot's current initial value.
    pub fn get(&self, path: FieldPath) -> Option<&StateValue<InMemoryDB>> {
        self.slots.get(path.as_slice()).map(|slot| &slot.value)
    }

    /// The state tree: every declared slot at its path, each Array as long
    /// as its highest index plus one, every other entry Null. A block with
    /// no fields is the empty Array.
    pub fn build(&self) -> StateValue<InMemoryDB> {
        let entries: Vec<(&[u8], &StateValue<InMemoryDB>)> = self
            .slots
            .iter()
            .map(|(path, slot)| (path.as_slice(), &slot.value))
            .collect();
        assemble(&entries)
    }
}

/// One Array node from the slots under it, paths relative to it (sorted,
/// non-empty, prefix-free — [`StateBuilder::declare`] saw to that).
fn assemble(entries: &[(&[u8], &StateValue<InMemoryDB>)]) -> StateValue<InMemoryDB> {
    let len = entries
        .iter()
        .map(|(path, _)| usize::from(path[0]) + 1)
        .max()
        .unwrap_or(0);
    assert!(
        len <= MAX_ARRAY,
        "a ledger Array holds at most sixteen entries, and this node would hold {len}"
    );
    let mut items = vec![StateValue::Null; len];
    let mut at = 0;
    while at < entries.len() {
        let head = entries[at].0[0];
        let end = at
            + entries[at..]
                .iter()
                .take_while(|(path, _)| path[0] == head)
                .count();
        let group = &entries[at..end];
        items[usize::from(head)] = match group {
            [(path, value)] if path.len() == 1 => (*value).clone(),
            _ => {
                let deeper: Vec<(&[u8], &StateValue<InMemoryDB>)> = group
                    .iter()
                    .map(|(path, value)| (&path[1..], *value))
                    .collect();
                assemble(&deeper)
            }
        };
        at = end;
    }
    StateValue::Array(Array::from(items))
}

/// Whether `new` may replace `old` in [`StateBuilder::set`].
fn same_shape(old: &StateValue<InMemoryDB>, new: &StateValue<InMemoryDB>) -> bool {
    match (old, new) {
        (StateValue::Null, _) => true,
        (StateValue::Cell(a), StateValue::Cell(b)) => a.alignment == b.alignment,
        (StateValue::Map(_), StateValue::Map(_)) => true,
        (StateValue::Array(_), StateValue::Array(_)) => true,
        (StateValue::BoundedMerkleTree(_), StateValue::BoundedMerkleTree(_)) => true,
        _ => false,
    }
}
