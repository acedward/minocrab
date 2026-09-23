//! THE DISCRIMINATOR'S RULE (notes/ledger-header.org; spec 00002 FR-008,
//! SC-004): `v3::discriminator` on state trees built here — every shape the
//! rule reads, every shape it refuses, and the trailing zeros of the
//! placeholder magic, stored trimmed and read back padded.
//!
//! - READ: a standard's magic at `[0]` (magic-only) and `[0, 0]` (with
//!   fields), wherever the block declares it; a plain `Bytes<32>` cell
//!   written first, compactc-style, at `[0]`, `[0, 0]` and `[0, 0, 0]`.
//! - REFUSED (`None`): a first leaf that is a Counter, a Map, Null, a
//!   `Bytes<16>` Cell, a Cell of several atoms or of a field atom, an EMPTY
//!   List or a Merkle tree; an empty root; a root that is not an Array; a
//!   nest deeper than three; a Cell that does not fit its own alignment.
//! - `implements::<S>`: the discriminator compared with one standard's
//!   magic, true and false.
//! - WHAT THE RULE CANNOT TELL (a claim, not proof), pinned through the VM:
//!   a pushed `List<Bytes<32>>` first field reads its current head (the
//!   list node `[head, tail, length]` is shaped like a three-field block),
//!   and a contract's own circuit can rewrite a standard's magic through a
//!   hand-written path.
//!
//! The same reader on SERIALIZED, tagged `ContractState`s — every deployed
//! block of the deploy gate, compactc's own initial states, and bytes that
//! are not a `ContractState` — is minocrab-contracts'
//! `tests/ledger_deploy.rs` (T5).

use midnight_base_crypto::fab::{AlignedValue, Value, ValueAtom};
use midnight_onchain_state::state::StateValue;
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::Array;
use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{Alignment, AlignmentAtom, AlignmentSegment, Public};
use minocrab_ledger::{empty_counter, empty_map, stored_cell};
use minocrab_sim::v3::exec::{self, Call};
use minocrab_std::v3::{
    discriminator, implements, pad32, Bytes, FieldPath, Ledger, LedgerCell, LedgerCounter,
    LedgerField, LedgerHeader, LedgerList, LedgerMap, LedgerMerkleTree, LedgerRepr, Maybe,
    MerkleTreeDigest, StateBuilder, Uint, B32,
};

type State = StateValue<InMemoryDB>;
type U64 = Uint<64, Public>;
type U8 = Uint<8, Public>;
type B32P = B32<Public>;

/// The placeholder magic: 26 bytes, then six zero bytes the ledger trims.
const PLACEHOLDER: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");

// ---- the standards --------------------------------------------------------------------

/// Magic-only, with the placeholder.
#[derive(LedgerHeader)]
struct Mip0099;

impl LedgerHeader for Mip0099 {
    const MAGIC: [u8; 32] = PLACEHOLDER;
}

/// Magic plus fields: the magic at `[0, 0]`.
#[derive(LedgerHeader)]
struct Versioned {
    version: LedgerCell<U8>,
    admin: LedgerCell<B32P>,
}

impl LedgerHeader for Versioned {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:versioned[v1]");
}

/// A magic that fills all 32 bytes: nothing to trim.
#[derive(LedgerHeader)]
struct Full;

impl LedgerHeader for Full {
    const MAGIC: [u8; 32] = *b"mip-0099:the-full-width-magic[1]";
}

/// A magic with zero bytes INSIDE it: only the trailing ones are trimmed.
#[derive(LedgerHeader)]
struct Gappy;

impl LedgerHeader for Gappy {
    const MAGIC: [u8; 32] = pad32(b"mip\0-0099\0\0:gap");
}

/// A magic the placeholder is a prefix of: a prefix is not a match.
#[derive(LedgerHeader)]
struct Longer;

impl LedgerHeader for Longer {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]x");
}

// ---- the blocks -------------------------------------------------------------------------

/// The standard declared between two fields: `[0]`.
#[derive(Ledger)]
struct HeadedFlat {
    a: LedgerCell<U64>,
    std: Mip0099,
    b: LedgerCounter,
}

#[derive(Ledger)]
struct OnlyStandard {
    std: Mip0099,
}

/// A multi-field standard declared last: `[0]` is `Array(3)`, the magic at
/// `[0, 0]`.
#[derive(Ledger)]
struct HeadedFields {
    a: LedgerCell<U64>,
    b: LedgerMap<U64, U64>,
    std: Versioned,
}

/// Declared first.
#[derive(Ledger)]
struct FullBlock {
    std: Full,
    a: LedgerCounter,
}

#[derive(Ledger)]
struct GappyBlock {
    a: LedgerCounter,
    std: Gappy,
}

#[derive(Ledger)]
struct LongerBlock {
    std: Longer,
}

/// No standard: a `Bytes<32>` cell first, which the deployer writes the way
/// a Compact constructor writes `magic = pad(32, "…")` — compactc's
/// magic-first contract of three fields.
#[derive(Ledger)]
struct MagicFirst {
    magic: LedgerCell<B32P>,
    a: LedgerCell<U64>,
    b: LedgerCounter,
}

/// The same at sixteen fields: compactc segments it, the magic at `[0, 0]`.
#[derive(Ledger)]
struct MagicFirst16 {
    magic: LedgerCell<B32P>,
    f1: LedgerCell<U64>,
    f2: LedgerCell<U64>,
    f3: LedgerCell<U64>,
    f4: LedgerCell<U64>,
    f5: LedgerCell<U64>,
    f6: LedgerCell<U64>,
    f7: LedgerCell<U64>,
    f8: LedgerCell<U64>,
    f9: LedgerCell<U64>,
    f10: LedgerCell<U64>,
    f11: LedgerCell<U64>,
    f12: LedgerCell<U64>,
    f13: LedgerCell<U64>,
    f14: LedgerCell<U64>,
    f15: LedgerCell<U64>,
}

// The refused first leaves. Each block's SECOND field is a `Bytes<32>` cell
// the tests write the placeholder into: a magic anywhere but the first leaf
// is not read.

#[derive(Ledger)]
struct CounterFirst {
    count: LedgerCounter,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct MapFirst {
    map: LedgerMap<B32P, U64>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct NullFirst {
    raw: LedgerField,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct Bytes16First {
    tag: LedgerCell<Bytes<16, Public>>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct MaybeFirst {
    maybe: LedgerCell<Maybe<B32P, Public>>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct DigestFirst {
    digest: LedgerCell<MerkleTreeDigest<Public>>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct ListFirst {
    list: LedgerList<B32P>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct TreeFirst {
    tree: LedgerMerkleTree<10, B32P>,
    magic: LedgerCell<B32P>,
}

#[derive(Ledger)]
struct Empty {}

// ---- helpers ------------------------------------------------------------------------------

fn b32_cell(bytes: &[u8]) -> State {
    stored_cell(
        vec![AlignmentAtom::Bytes { length: 32 }],
        vec![bytes.to_vec()],
    )
}

/// A Cell built field by field, skipping `AlignedValue::new`'s fit check and
/// FAB normalization — what a hand-written state could carry.
fn raw_cell(atoms: Vec<Vec<u8>>, alignment: Vec<AlignmentAtom>) -> State {
    StateValue::Cell(Sp::new(AlignedValue {
        value: Value(atoms.into_iter().map(ValueAtom).collect()),
        alignment: Alignment(alignment.into_iter().map(AlignmentSegment::Atom).collect()),
    }))
}

fn array(items: Vec<State>) -> State {
    StateValue::Array(Array::from(items))
}

/// `leaf` under `depth` one-entry Arrays: its path is `depth` zeros.
fn nest(depth: usize, leaf: State) -> State {
    (0..depth).fold(leaf, |node, _| array(vec![node]))
}

fn at<'a>(state: &'a State, path: &[u8]) -> &'a State {
    let mut node = state;
    for i in path {
        let StateValue::Array(items) = node else {
            panic!("{path:?} walks through a non-Array");
        };
        node = items.get(usize::from(*i)).expect("in range");
    }
    node
}

/// The one atom a Cell stores.
fn stored_atom(state: &State) -> Vec<u8> {
    let StateValue::Cell(cell) = state else {
        panic!("not a Cell: {state:?}");
    };
    assert_eq!(cell.value.0.len(), 1, "one atom");
    cell.value.0[0].0.clone()
}

/// A block's state with the placeholder written into the `Bytes<32>` cell
/// at `magic`, as a Compact constructor would.
fn with_magic(mut state: StateBuilder, magic: FieldPath) -> State {
    state.set(magic, b32_cell(&PLACEHOLDER));
    state.build()
}

// ---- read ---------------------------------------------------------------------------------

/// A standard's magic at `[0]` or `[0, 0]`, wherever the block declares it.
#[test]
fn a_standards_magic_is_read_at_either_header_shape() {
    let flat = HeadedFlat::initial_state().build();
    assert_eq!(
        discriminator(&flat),
        Some(PLACEHOLDER),
        "[0], declared second"
    );
    let alone = OnlyStandard::initial_state().build();
    assert_eq!(
        discriminator(&alone),
        Some(PLACEHOLDER),
        "a block of the standard alone"
    );
    let full = FullBlock::initial_state().build();
    assert_eq!(
        discriminator(&full),
        Some(Full::MAGIC),
        "[0], declared first"
    );
    let gappy = GappyBlock::initial_state().build();
    assert_eq!(
        discriminator(&gappy),
        Some(Gappy::MAGIC),
        "[0], declared last"
    );

    let fields = HeadedFields::initial_state().build();
    assert_eq!(
        HeadedFields::new().std.magic().field_path().as_slice(),
        &[0, 0]
    );
    assert_eq!(discriminator(&fields), Some(Versioned::MAGIC), "[0, 0]");
}

/// compactc's magic-first contract: no standard, a `Bytes<32>` first field
/// holding the magic, at every depth compactc nests it — `[0]` (up to
/// fifteen fields), `[0, 0]` (16 to 225), `[0, 0, 0]` (226 and up).
#[test]
fn a_bytes32_cell_written_first_is_read_at_every_depth() {
    let magic = MagicFirst::new().magic.field_path();
    assert_eq!(magic.as_slice(), &[0]);
    let state = with_magic(MagicFirst::initial_state(), magic);
    assert_eq!(discriminator(&state), Some(PLACEHOLDER), "[0]");

    let magic = MagicFirst16::new().magic.field_path();
    assert_eq!(magic.as_slice(), &[0, 0]);
    let state = with_magic(MagicFirst16::initial_state(), magic);
    assert_eq!(discriminator(&state), Some(PLACEHOLDER), "[0, 0]");

    // [0, 0, 0] — compactc's 226-field shape: the magic and the last field
    // at [1, 14, 14]. (Real 226-field blocks, deployed and serialized, are
    // ledger_deploy's.)
    let mut state = StateBuilder::new();
    state.slot(FieldPath::of(&[0, 0, 0]), b32_cell(&PLACEHOLDER));
    state.slot(FieldPath::of(&[1, 14, 14]), empty_counter());
    let state = state.build();
    assert_eq!(discriminator(&state), Some(PLACEHOLDER), "[0, 0, 0]");

    // The same three depths as bare nests.
    for depth in 1..=3 {
        let state = nest(depth, b32_cell(&PLACEHOLDER));
        assert_eq!(discriminator(&state), Some(PLACEHOLDER), "depth {depth}");
    }
}

/// The ledger stores a `Bytes<32>` without its trailing zeros (FAB normal
/// form); the reader pads it back. Zeros inside the magic are kept.
#[test]
fn the_placeholder_is_stored_trimmed_and_read_back_padded() {
    assert_eq!(PLACEHOLDER[26..], [0u8; 6], "six trailing zeros");

    let flat = HeadedFlat::initial_state().build();
    assert_eq!(
        stored_atom(at(&flat, &[0])),
        b"mip-0099:ledger-header[v1]".to_vec(),
        "stored trimmed: 26 bytes"
    );
    assert_eq!(discriminator(&flat), Some(PLACEHOLDER), "read back padded");

    // Nothing to trim.
    let full = FullBlock::initial_state().build();
    assert_eq!(stored_atom(at(&full, &[0])), Full::MAGIC.to_vec());
    assert_eq!(discriminator(&full), Some(Full::MAGIC));

    // Inner zeros kept, trailing ones trimmed.
    let gappy = GappyBlock::initial_state().build();
    assert_eq!(
        stored_atom(at(&gappy, &[0])),
        b"mip\0-0099\0\0:gap".to_vec()
    );
    assert_eq!(discriminator(&gappy), Some(Gappy::MAGIC));

    // A hand-written atom that keeps its trailing zeros (not normal form)
    // reads the same.
    let untrimmed = array(vec![raw_cell(
        vec![PLACEHOLDER.to_vec()],
        vec![AlignmentAtom::Bytes { length: 32 }],
    )]);
    assert_eq!(stored_atom(at(&untrimmed, &[0])).len(), 32);
    assert_eq!(discriminator(&untrimmed), Some(PLACEHOLDER));

    // Never written: the empty atom reads as 32 zero bytes — a value the
    // reader returns (it keeps no registry), and no standard's magic (a
    // zero magic does not compile).
    let unset = MagicFirst::initial_state().build();
    assert!(stored_atom(at(&unset, &[0])).is_empty());
    assert_eq!(discriminator(&unset), Some([0u8; 32]));
}

// ---- refused --------------------------------------------------------------------------

/// A first leaf that is not one `bytes<32>` Cell, with the placeholder
/// written into the block's second field: `None` every time.
#[test]
fn a_first_leaf_of_any_other_shape_is_none() {
    // A Counter: a Cell of one `bytes<8>` atom.
    let state = with_magic(
        CounterFirst::initial_state(),
        CounterFirst::new().magic.field_path(),
    );
    assert_eq!(discriminator(&state), None, "a Counter");

    // A Map.
    let state = with_magic(
        MapFirst::initial_state(),
        MapFirst::new().magic.field_path(),
    );
    assert!(matches!(at(&state, &[0]), StateValue::Map(_)));
    assert_eq!(discriminator(&state), None, "a Map");

    // Null: an untyped field nobody set.
    let state = with_magic(
        NullFirst::initial_state(),
        NullFirst::new().magic.field_path(),
    );
    assert!(matches!(at(&state, &[0]), StateValue::Null));
    assert_eq!(discriminator(&state), None, "Null");

    // A Bytes<16> Cell, even holding the placeholder's first 16 bytes.
    let block = Bytes16First::new();
    let mut state = Bytes16First::initial_state();
    state.set(
        block.tag.field_path(),
        stored_cell(
            vec![AlignmentAtom::Bytes { length: 16 }],
            vec![PLACEHOLDER[..16].to_vec()],
        ),
    );
    let state = with_magic(state, block.magic.field_path());
    assert_eq!(discriminator(&state), None, "a Bytes<16> Cell");

    // A Cell of several atoms, one of them the placeholder: a `Maybe`.
    let block = MaybeFirst::new();
    let atoms = Maybe::<B32P, Public>::atoms();
    assert!(atoms.len() > 1);
    assert!(atoms.contains(&AlignmentAtom::Bytes { length: 32 }));
    let mut state = MaybeFirst::initial_state();
    state.set(
        block.maybe.field_path(),
        stored_cell(atoms, vec![vec![1], PLACEHOLDER.to_vec()]),
    );
    let state = with_magic(state, block.magic.field_path());
    assert_eq!(discriminator(&state), None, "a Maybe<Bytes<32>> Cell");

    // …and two `bytes<32>` atoms side by side.
    let two = array(vec![stored_cell(
        vec![
            AlignmentAtom::Bytes { length: 32 },
            AlignmentAtom::Bytes { length: 32 },
        ],
        vec![PLACEHOLDER.to_vec(), PLACEHOLDER.to_vec()],
    )]);
    assert_eq!(discriminator(&two), None, "two bytes<32> atoms");

    // A field atom (a Merkle tree digest).
    let state = with_magic(
        DigestFirst::initial_state(),
        DigestFirst::new().magic.field_path(),
    );
    assert_eq!(discriminator(&state), None, "a field-atom Cell");

    // An EMPTY List ([0] an Array whose first entry is Null) and a Merkle
    // tree ([0] an Array whose first entry is the tree). A PUSHED List is
    // another matter: see `a_pushed_list_first_field_reads_its_head`.
    let state = with_magic(
        ListFirst::initial_state(),
        ListFirst::new().magic.field_path(),
    );
    assert!(matches!(at(&state, &[0, 0]), StateValue::Null));
    assert_eq!(discriminator(&state), None, "an empty List");
    let state = with_magic(
        TreeFirst::initial_state(),
        TreeFirst::new().magic.field_path(),
    );
    assert!(matches!(
        at(&state, &[0, 0]),
        StateValue::BoundedMerkleTree(_)
    ));
    assert_eq!(discriminator(&state), None, "a Merkle tree");
}

/// A root with no first entry, or that is not an Array: no first field,
/// so no discriminator — even when the root itself is a `bytes<32>` Cell.
#[test]
fn an_empty_or_non_array_root_is_none() {
    assert_eq!(
        discriminator(&Empty::initial_state().build()),
        None,
        "no fields"
    );
    assert_eq!(discriminator(&array(vec![])), None, "the empty Array");
    assert_eq!(discriminator(&b32_cell(&PLACEHOLDER)), None, "a bare Cell");
    assert_eq!(discriminator(&State::Null), None, "Null");
    assert_eq!(discriminator(&empty_map()), None, "a Map");
}

/// At most three steps: the magic under a fourth Array is not read.
#[test]
fn a_nest_deeper_than_three_is_none() {
    assert_eq!(
        discriminator(&nest(3, b32_cell(&PLACEHOLDER))),
        Some(PLACEHOLDER),
        "three: read"
    );
    assert_eq!(
        discriminator(&nest(4, b32_cell(&PLACEHOLDER))),
        None,
        "four: refused"
    );
    assert_eq!(
        discriminator(&nest(5, b32_cell(&PLACEHOLDER))),
        None,
        "five: refused"
    );
    // A fourth Array beside real entries, as a malformed segmented root.
    let deep = array(vec![
        array(vec![array(vec![array(vec![b32_cell(&PLACEHOLDER)])])]),
        empty_counter(),
    ]);
    assert_eq!(discriminator(&deep), None);
}

/// A Cell whose value does not fit its own `bytes<32>` alignment — which
/// `AlignedValue::new` would refuse, built here field by field: `None`, never
/// a truncated or partial read.
#[test]
fn a_cell_that_does_not_fit_its_alignment_is_none() {
    let b32 = || vec![AlignmentAtom::Bytes { length: 32 }];
    let too_long = array(vec![raw_cell(vec![vec![0x6d; 33]], b32())]);
    assert_eq!(discriminator(&too_long), None, "a 33-byte atom");
    let none = array(vec![raw_cell(vec![], b32())]);
    assert_eq!(discriminator(&none), None, "no atom");
    let two = array(vec![raw_cell(
        vec![PLACEHOLDER.to_vec(), PLACEHOLDER.to_vec()],
        b32(),
    )]);
    assert_eq!(discriminator(&two), None, "two atoms under one bytes<32>");
}

// ---- implements -------------------------------------------------------------------------

#[test]
fn implements_compares_the_discriminator_with_one_standards_magic() {
    let flat = HeadedFlat::initial_state().build();
    assert!(implements::<Mip0099>(&flat));
    assert!(!implements::<Versioned>(&flat));
    assert!(!implements::<Full>(&flat));
    assert!(
        !implements::<Longer>(&flat),
        "a magic the stored bytes are a prefix of"
    );

    let fields = HeadedFields::initial_state().build();
    assert!(implements::<Versioned>(&fields));
    assert!(!implements::<Mip0099>(&fields));

    let longer = LongerBlock::initial_state().build();
    assert!(implements::<Longer>(&longer));
    assert!(
        !implements::<Mip0099>(&longer),
        "a prefix of the stored bytes"
    );

    let gappy = GappyBlock::initial_state().build();
    assert!(implements::<Gappy>(&gappy));

    // A contract without a minocrab standard that writes the magic first
    // CLAIMS the standard all the same: the reader sees state, not source.
    let state = with_magic(
        MagicFirst::initial_state(),
        MagicFirst::new().magic.field_path(),
    );
    assert!(implements::<Mip0099>(&state));

    // Never written: a discriminator of zeros, no standard's.
    let unset = MagicFirst::initial_state().build();
    for claims in [
        implements::<Mip0099>(&unset),
        implements::<Versioned>(&unset),
        implements::<Full>(&unset),
    ] {
        assert!(!claims);
    }

    // No discriminator: false.
    let counter = with_magic(
        CounterFirst::initial_state(),
        CounterFirst::new().magic.field_path(),
    );
    assert!(!implements::<Mip0099>(&counter));
    assert!(!implements::<Mip0099>(&Empty::initial_state().build()));
}

// ---- what the rule cannot tell: a claim, not proof ----------------------------------------

/// `state` after `circuit` runs on it through Midnight's VM (the executor).
fn run(circuit: &Compiled3, state: &State) -> State {
    let context = exec::context(state.clone(), [7; 32]);
    exec::execute(&circuit.ir, &Call::new(&[], &[]), &context)
        .expect("the circuit runs through QueryContext::query")
        .post
}

/// A NON-headed contract whose first field is a `List<Bytes<32>>`: empty,
/// it has no discriminator; once a circuit pushes onto it, the list node
/// `[head, tail, length]` has exactly the shape of a three-field block
/// `{Bytes<32>, List, Counter}`, so the walk reads the head — and whoever
/// may call the push "claims" any standard, until the next push or pop.
/// Inherent to the rule (spec FR-008); pinned so the docs cannot drift.
#[test]
fn a_pushed_list_first_field_reads_its_head() {
    const LIST: ListFirst = ListFirst::new();
    let empty = ListFirst::initial_state().build();
    assert_eq!(discriminator(&empty), None, "the empty List: None");
    let mut c = Circuit3::new();
    let head = B32::pad(&mut c, "mip-0099:ledger-header[v1]");
    LIST.list.push_front(&mut c, &head);
    let pushed = run(&c.finish(false), &empty);
    assert!(matches!(at(&pushed, &[0, 0]), StateValue::Cell(_)));
    assert!(matches!(at(&pushed, &[0, 1]), StateValue::Array(_)));
    assert_eq!(discriminator(&pushed), Some(Mip0099::MAGIC));
    assert!(implements::<Mip0099>(&pushed));
}

/// No typed handle writes a standard's magic (`Magic` has no write or
/// reset), but `LedgerCell::at_path` on the magic's own path is an ordinary
/// typed write: a contract's OWN circuit can drop or change its claim, no
/// maintenance update needed. The verifier-key caveat covers it.
#[test]
fn a_circuit_that_names_the_magics_path_by_hand_can_rewrite_it() {
    const BLOCK: HeadedFlat = HeadedFlat::new();
    let deployed = HeadedFlat::initial_state().build();
    assert!(implements::<Mip0099>(&deployed));
    let by_hand: LedgerCell<B32P> = LedgerCell::at_path(BLOCK.std.magic().field_path().as_slice());
    let mut c = Circuit3::new();
    let other = B32::pad(&mut c, "another claim");
    by_hand.write(&mut c, &other);
    let rewritten = run(&c.finish(false), &deployed);
    assert_eq!(discriminator(&rewritten), Some(pad32(b"another claim")));
    assert!(!implements::<Mip0099>(&rewritten));
}
