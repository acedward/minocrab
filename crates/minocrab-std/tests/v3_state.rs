//! THE DEPLOY STATE'S GATE (notes/ledger-header.org): `#[derive(Ledger)]`'s
//! `initial_state()` is the state compactc's generated `initialState`
//! builds, checked here against compactc's own PROCEDURE — the skeleton of
//! Nulls, then every field's `resetToDefault` run through Midnight's on-chain
//! VM (the executor, `minocrab_sim::v3::exec`). The resets are minocrab's
//! op builders, each differential-tested against compactc's vm-code; a Cell's
//! is compactc's `push key; pushs default; ins 1` with `default_value`'s
//! zeros. So the builder's values are pinned to what the ledger itself
//! computes, flat and segmented, and nothing here re-derives them.
//!
//! Also here: the builder's own rules (the skeleton's lengths, Null for an
//! untyped field, the header's two shapes, the empty block), every refusal
//! of `StateBuilder::set` (the Array slots' shapes included), and the
//! magic's own rules for slot types written BY HAND: a magic only at `[0]`
//! or `[0, 0]`, one per state, present exactly when the block embeds a
//! standard — so a standard hidden in a group slot is refused by name.
//!
//! What this file cannot see is compactc's JAVASCRIPT: a curve point's Compact
//! default is its identity, not the zero limbs a circuit default pushes, and
//! a `compress` atom has no limb decoding. Those two are pinned against
//! compactc's generated `initialState` byte for byte by minocrab-contracts'
//! `tests/ledger_deploy.rs` (the T4b oracle fixtures).

use midnight_onchain_state::state::StateValue;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::Array;
use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{AlignmentAtom, Public};
use minocrab_ledger::{
    cell_write_at, default_value, emit, empty_list, empty_merkle_tree_value,
    historic_merkle_tree_reset_value, stored_cell, LedgerKey,
};
use minocrab_sim::v3::exec::{self, Call};
use minocrab_std::v3::{
    pad32, BlockLayout, Bool, FieldPath, InitialState, Ledger, LedgerCell, LedgerCounter,
    LedgerField, LedgerHeader, LedgerHistoricMerkleTree, LedgerList, LedgerMap, LedgerMerkleTree,
    LedgerRepr, LedgerSet, LedgerWidth, Magic, Placement, StateBuilder, Uint, B32,
};

type U64 = Uint<64, Public>;
type U8 = Uint<8, Public>;

// ---- the blocks ----------------------------------------------------------------------

/// One of every std slot type, flat: ten fields.
#[derive(Ledger)]
struct Every {
    num: LedgerCell<U64>,
    hash: LedgerCell<B32<Public>>,
    flag: LedgerCell<Bool<Public>>,
    count: LedgerCounter,
    map: LedgerMap<B32<Public>, U64>,
    set: LedgerSet<B32<Public>>,
    list: LedgerList<U64>,
    tree: LedgerMerkleTree<10, B32<Public>>,
    history: LedgerHistoricMerkleTree<10, B32<Public>>,
    untyped: LedgerField,
}

const EVERY: Every = Every::new();

/// The same ten behind ten more cells: twenty fields, so compactc segments
/// it (`[[5 fields], [15 fields]]`) and every path has two elements.
#[derive(Ledger)]
struct Segmented {
    p0: LedgerCell<U64>,
    p1: LedgerCell<U64>,
    p2: LedgerCell<U8>,
    p3: LedgerCell<U64>,
    p4: LedgerCell<B32<Public>>,
    p5: LedgerCell<U64>,
    p6: LedgerCell<U64>,
    p7: LedgerCell<U64>,
    p8: LedgerCell<U64>,
    p9: LedgerCell<U64>,
    num: LedgerCell<U64>,
    hash: LedgerCell<B32<Public>>,
    flag: LedgerCell<Bool<Public>>,
    count: LedgerCounter,
    map: LedgerMap<B32<Public>, U64>,
    set: LedgerSet<B32<Public>>,
    list: LedgerList<U64>,
    tree: LedgerMerkleTree<10, B32<Public>>,
    history: LedgerHistoricMerkleTree<10, B32<Public>>,
    untyped: LedgerField,
}

const SEGMENTED: Segmented = Segmented::new();

/// The tests' placeholder standard, magic-only.
#[derive(LedgerHeader)]
struct Mip0099;

impl LedgerHeader for Mip0099 {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
}

/// A standard that owns a version and an admin key besides its magic.
#[derive(LedgerHeader)]
struct Versioned {
    version: LedgerCell<U8>,
    admin: LedgerCell<B32<Public>>,
    uses: LedgerCounter,
}

impl LedgerHeader for Versioned {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:versioned[v1]");
}

#[derive(Ledger)]
struct HeadedFlat {
    a: LedgerCell<U64>,
    std: Mip0099,
    b: LedgerCounter,
}

#[derive(Ledger)]
struct HeadedFields {
    a: LedgerCell<U64>,
    b: LedgerMap<U64, U64>,
    std: Versioned,
}

const HEADED_FIELDS: HeadedFields = HeadedFields::new();

#[derive(Ledger)]
struct OnlyStandard {
    std: Mip0099,
}

#[derive(Ledger)]
struct Empty {}

// ---- helpers --------------------------------------------------------------------------

fn keys(path: FieldPath) -> Vec<LedgerKey> {
    path.as_slice()
        .iter()
        .map(|i| LedgerKey::Field(*i))
        .collect()
}

/// compactc's Cell `resetToDefault`: `cell_write_at` of `default_value`'s
/// zeros (midnight-ledger.ss:560-566).
fn reset_cell<T: LedgerRepr>(c: &mut Circuit3, cell: &LedgerCell<T>) {
    emit(
        c,
        &cell_write_at(&keys(cell.field_path()), &default_value(T::atoms())),
    );
}

fn compile(body: impl FnOnce(&mut Circuit3)) -> Compiled3 {
    let mut c = Circuit3::new();
    body(&mut c);
    c.finish(false)
}

/// The same tree with every leaf Null — compactc's skeleton, phase 1 of
/// `initialState`.
fn skeleton(state: &StateValue<InMemoryDB>) -> StateValue<InMemoryDB> {
    match state {
        StateValue::Array(items) => StateValue::Array(Array::from(
            items.iter_deref().map(skeleton).collect::<Vec<_>>(),
        )),
        _ => StateValue::Null,
    }
}

/// Phase 2: `resets` run through the VM against the skeleton.
fn run_resets(
    shape: &StateValue<InMemoryDB>,
    resets: impl FnOnce(&mut Circuit3),
) -> StateValue<InMemoryDB> {
    let circuit = compile(resets);
    let ctx = exec::context(skeleton(shape), [7u8; 32]);
    exec::execute(&circuit.ir, &Call::new(&[], &[]), &ctx)
        .expect("every reset applies to the skeleton")
        .post
}

fn at<'a>(state: &'a StateValue<InMemoryDB>, path: &[u8]) -> &'a StateValue<InMemoryDB> {
    let mut node = state;
    for i in path {
        let StateValue::Array(items) = node else {
            panic!("{path:?} walks through a non-Array");
        };
        node = items.get(usize::from(*i)).expect("in range");
    }
    node
}

fn array_len(state: &StateValue<InMemoryDB>) -> usize {
    match state {
        StateValue::Array(items) => items.len(),
        other => panic!("not an Array: {other:?}"),
    }
}

fn b32_cell(bytes: [u8; 32]) -> StateValue<InMemoryDB> {
    stored_cell(
        vec![AlignmentAtom::Bytes { length: 32 }],
        vec![bytes.to_vec()],
    )
}

// ---- compactc's procedure, through the VM ---------------------------------------------

/// Every slot type, flat: the builder's tree IS the skeleton with every
/// field's reset run on it through the VM. The one field the VM run leaves
/// Null is the untyped `LedgerField`, and the builder leaves it Null too.
#[test]
fn a_flat_block_is_its_skeleton_with_every_reset_run_on_it() {
    let built = Every::initial_state().build();
    assert_eq!(array_len(&built), 10);
    let vm = run_resets(&built, |c| {
        reset_cell(c, &EVERY.num);
        reset_cell(c, &EVERY.hash);
        reset_cell(c, &EVERY.flag);
        EVERY.count.reset_to_default(c);
        EVERY.map.reset_to_default(c);
        EVERY.set.reset_to_default(c);
        EVERY.list.reset_to_default(c);
        EVERY.tree.reset_to_default(c);
        EVERY.history.reset_to_default(c);
    });
    assert!(vm == built, "builder:\n{built:?}\nVM:\n{vm:?}");
    assert!(*at(&built, &[9]) == StateValue::Null, "the untyped field");
}

/// The same across segments: twenty fields, every path two deep.
#[test]
fn a_segmented_block_is_its_skeleton_with_every_reset_run_on_it() {
    let built = Segmented::initial_state().build();
    assert_eq!(
        array_len(&built),
        2,
        "the remainder segment and one full one"
    );
    assert_eq!(array_len(at(&built, &[0])), 5);
    assert_eq!(array_len(at(&built, &[1])), 15);
    let s = &SEGMENTED;
    let vm = run_resets(&built, |c| {
        reset_cell(c, &s.p0);
        reset_cell(c, &s.p1);
        reset_cell(c, &s.p2);
        reset_cell(c, &s.p3);
        reset_cell(c, &s.p4);
        reset_cell(c, &s.p5);
        reset_cell(c, &s.p6);
        reset_cell(c, &s.p7);
        reset_cell(c, &s.p8);
        reset_cell(c, &s.p9);
        reset_cell(c, &s.num);
        reset_cell(c, &s.hash);
        reset_cell(c, &s.flag);
        s.count.reset_to_default(c);
        s.map.reset_to_default(c);
        s.set.reset_to_default(c);
        s.list.reset_to_default(c);
        s.tree.reset_to_default(c);
        s.history.reset_to_default(c);
    });
    assert!(vm == built, "builder:\n{built:?}\nVM:\n{vm:?}");
    assert!(
        *at(&built, &[1, 14]) == StateValue::Null,
        "the untyped field"
    );
}

/// A headed block's body is laid out one root slot along, and its standard's
/// fields reset through the VM the same as the body's; the magic is the
/// deploy state's alone, so the VM run starts from the builder's magic.
#[test]
fn a_headed_block_is_its_skeleton_with_every_reset_run_on_it() {
    let built = HeadedFields::initial_state().build();
    assert_eq!(
        array_len(&built),
        3,
        "the standard at [0], a and b at [1], [2]"
    );
    assert_eq!(
        array_len(at(&built, &[0])),
        4,
        "magic, version, admin, uses"
    );
    let h = &HEADED_FIELDS;
    let circuit = compile(|c| {
        reset_cell(c, &h.a);
        h.b.reset_to_default(c);
        reset_cell(c, &h.std.version);
        reset_cell(c, &h.std.admin);
        h.std.uses.reset_to_default(c);
    });
    // The skeleton, and the magic as the deploy state carries it.
    let skeleton = skeleton(&built);
    let StateValue::Array(ref root) = skeleton else {
        unreachable!()
    };
    let StateValue::Array(ref header) = *root.get(0).expect("[0]") else {
        unreachable!()
    };
    let header = header
        .insert(0, at(&built, &[0, 0]).clone())
        .expect("[0, 0]");
    let start = root.insert(0, StateValue::Array(header)).expect("[0]");
    let ctx = exec::context(StateValue::Array(start), [7u8; 32]);
    let vm = exec::execute(&circuit.ir, &Call::new(&[], &[]), &ctx)
        .expect("the resets apply")
        .post;
    assert!(vm == built, "builder:\n{built:?}\nVM:\n{vm:?}");
}

// ---- the builder's rules --------------------------------------------------------------

/// The two header shapes: a magic-only standard is ONE Cell at `[0]`, a
/// standard with fields an Array at `[0]` with the magic at `[0, 0]`. Both
/// magics are stored trimmed, under one `bytes<32>` atom.
#[test]
fn a_standard_contributes_its_magic_in_either_shape() {
    let flat = HeadedFlat::initial_state().build();
    assert_eq!(array_len(&flat), 3);
    assert!(*at(&flat, &[0]) == b32_cell(Mip0099::MAGIC));
    let StateValue::Cell(ref magic) = *at(&flat, &[0]) else {
        panic!("a Cell at [0]");
    };
    assert_eq!(
        magic.value.0[0].0,
        b"mip-0099:ledger-header[v1]".to_vec(),
        "stored trimmed"
    );
    assert!(*at(&flat, &[1]) == stored_cell(U64::atoms(), U64::default_stored()));
    let fields = HeadedFields::initial_state().build();
    assert!(*at(&fields, &[0, 0]) == b32_cell(Versioned::MAGIC));
    assert!(*at(&fields, &[0, 1]) == stored_cell(U8::atoms(), U8::default_stored()));
}

/// No fields at all is the empty root; the standard alone is a root of one.
#[test]
fn the_smallest_blocks() {
    assert_eq!(array_len(&Empty::initial_state().build()), 0);
    let only = OnlyStandard::initial_state().build();
    assert_eq!(array_len(&only), 1);
    assert!(*at(&only, &[0]) == b32_cell(Mip0099::MAGIC));
}

/// `set` replaces a declared slot's value: any value for the untyped field,
/// a Cell of the same alignment for a Cell.
#[test]
fn set_replaces_a_declared_slot() {
    let signer = b32_cell([0x5a; 32]);
    let seven = stored_cell(U64::atoms(), vec![7u64.to_le_bytes().to_vec()]);
    let mut state = Every::initial_state();
    state
        .set(EVERY.untyped.field_path(), signer.clone())
        .set(EVERY.num.field_path(), seven.clone());
    assert!(*state.get(EVERY.untyped.field_path()).expect("declared") == signer);
    let built = state.build();
    assert!(*at(&built, &[9]) == signer);
    assert!(*at(&built, &[0]) == seven);
}

#[test]
#[should_panic(expected = "is not a slot of this block")]
fn set_refuses_a_path_the_block_does_not_declare() {
    Every::initial_state().set(FieldPath::of(&[10]), StateValue::Null);
}

#[test]
#[should_panic(expected = "is not a slot of this block")]
fn set_refuses_a_path_inside_a_slot() {
    Every::initial_state().set(FieldPath::of(&[8, 2]), StateValue::Null);
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_cell_of_another_alignment() {
    Every::initial_state().set(EVERY.num.field_path(), b32_cell([1; 32]));
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_cell_for_a_map() {
    Every::initial_state().set(EVERY.map.field_path(), b32_cell([1; 32]));
}

#[test]
#[should_panic(expected = "is a standard's magic")]
fn set_refuses_the_magic() {
    let block = HeadedFlat::new();
    HeadedFlat::initial_state().set(block.std.magic().field_path(), b32_cell([1; 32]));
}

/// Two contributions at one path, or one under another, are a slot type's
/// bug: the builder refuses them rather than building one of the two.
#[test]
#[should_panic(expected = "overlapping paths")]
fn the_builder_refuses_overlapping_slots() {
    let mut state = StateBuilder::new();
    state.slot(FieldPath::of(&[1]), StateValue::Null);
    state.slot(FieldPath::of(&[1, 0]), StateValue::Null);
}

#[test]
#[should_panic(expected = "overlapping paths")]
fn the_builder_refuses_a_second_value_at_one_path() {
    let mut state = StateBuilder::new();
    state.slot(FieldPath::of(&[0]), StateValue::Null);
    state.slot(FieldPath::of(&[0]), StateValue::Null);
}

/// The tree does not depend on the order slots arrive in.
#[test]
fn the_order_of_contributions_does_not_matter() {
    let one = b32_cell([1; 32]);
    let two = b32_cell([2; 32]);
    let mut forward = StateBuilder::new();
    forward.slot(FieldPath::of(&[0, 0]), one.clone());
    forward.slot(FieldPath::of(&[1, 3]), two.clone());
    let mut backward = StateBuilder::new();
    backward.slot(FieldPath::of(&[1, 3]), two);
    backward.slot(FieldPath::of(&[0, 0]), one);
    assert!(forward.build() == backward.build());
    // Unset entries are Null, and each Array is as long as its highest
    // index plus one.
    let built = forward.build();
    assert_eq!(array_len(&built), 2);
    assert_eq!(array_len(at(&built, &[0])), 1);
    assert_eq!(array_len(at(&built, &[1])), 4);
    assert!(*at(&built, &[1, 0]) == StateValue::Null);
}

// ---- the Array slots' shapes (`set`) ------------------------------------------------

/// A List slot takes a PUSHED list — `[head, the rest, length]` — as well
/// as an empty one, and keeps taking one after it was replaced.
#[test]
fn set_takes_a_pushed_list_for_a_list() {
    let u64_cell = |v: u64| stored_cell(U64::atoms(), vec![v.to_le_bytes().to_vec()]);
    let pushed = StateValue::Array(Array::from(vec![u64_cell(9), empty_list(), u64_cell(1)]));
    let mut state = Every::initial_state();
    state
        .set(EVERY.list.field_path(), pushed.clone())
        .set(EVERY.list.field_path(), empty_list())
        .set(EVERY.list.field_path(), pushed.clone());
    assert!(*state.get(EVERY.list.field_path()).expect("declared") == pushed);
    // The trees take their own shape back.
    state
        .set(EVERY.tree.field_path(), empty_merkle_tree_value(10))
        .set(
            EVERY.history.field_path(),
            historic_merkle_tree_reset_value(10),
        );
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_an_empty_array_for_a_list() {
    Every::initial_state().set(
        EVERY.list.field_path(),
        StateValue::Array(Array::from(Vec::<StateValue<InMemoryDB>>::new())),
    );
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_list_for_a_merkle_tree() {
    Every::initial_state().set(EVERY.tree.field_path(), empty_list());
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_tree_of_another_height() {
    Every::initial_state().set(EVERY.tree.field_path(), empty_merkle_tree_value(11));
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_merkle_tree_for_a_historic_one() {
    Every::initial_state().set(EVERY.history.field_path(), empty_merkle_tree_value(10));
}

#[test]
#[should_panic(expected = "is not the slot's shape")]
fn set_refuses_a_historic_tree_for_a_list() {
    Every::initial_state().set(
        EVERY.list.field_path(),
        historic_merkle_tree_reset_value(10),
    );
}

// ---- the magic's rules, for slot types written by hand --------------------------------

/// A magic is at `[0]` or `[0, 0]`: no `Magic` handle names another path.
#[test]
#[should_panic(expected = "a standard's magic is at [0] (a magic-only standard) or [0, 0]")]
fn a_magic_elsewhere_is_refused() {
    let _ = Magic::at_path(std::hint::black_box(&[5]));
}

#[test]
#[should_panic(expected = "a standard's magic is at [0] (a magic-only standard) or [0, 0]")]
fn a_magic_deeper_is_refused() {
    let _ = Magic::at_path(std::hint::black_box(&[0, 0, 0]));
}

/// One magic per state: the second is the one-standard rule, named.
#[test]
#[should_panic(expected = "one standard per ledger block")]
fn a_second_magic_is_refused() {
    let mut state = StateBuilder::new();
    state.magic::<Mip0099>(Magic::at_path(&[0]));
    state.magic::<Mip0099>(Magic::at_path(&[0, 0]));
}

/// A derived standard built inside a hand-written group slot: the derive
/// sees the block's own fields only, so it is not counted — and in a block
/// with a standard of its own it would be a second owner of `root[0]`.
#[derive(LedgerHeader)]
struct Inner;

impl LedgerHeader for Inner {
    const MAGIC: [u8; 32] = pad32(b"inner");
}

struct Smuggler {
    inner: Inner,
    x: LedgerCell<U64>,
}

impl LedgerWidth for Smuggler {}

impl Smuggler {
    const fn at_layout(layout: BlockLayout, start: usize) -> Self {
        Smuggler {
            inner: Inner::at_layout(layout, start),
            x: LedgerCell::at_layout(layout, start),
        }
    }
}

impl InitialState for Smuggler {
    fn contribute(&self, state: &mut StateBuilder) {
        self.inner.contribute(state);
        self.x.contribute(state);
    }
}

#[derive(Ledger)]
struct TwoStandards {
    std: Mip0099,
    group: Smuggler,
}

#[test]
#[should_panic(expected = "one standard per ledger block")]
fn a_standard_hidden_in_a_group_slot_is_refused_by_name() {
    // Both handles are root[0]: the layout cannot tell them apart…
    let block = TwoStandards::new();
    assert_eq!(block.std.magic().field_path().as_slice(), &[0]);
    assert_eq!(block.group.inner.magic().field_path().as_slice(), &[0]);
    assert_eq!(block.group.x.field_path().as_slice(), &[1]);
    // …and the deploy state refuses the second, naming the rule.
    TwoStandards::initial_state();
}

/// A hand-written standard whose deploy state forgets its magic.
struct Silent;

impl LedgerWidth for Silent {
    const WIDTH: usize = 0;
    const PLACEMENT: Placement = Placement::root_header::<Silent>();
}

impl LedgerHeader for Silent {
    const MAGIC: [u8; 32] = pad32(b"silent");
}

impl Silent {
    const fn at_layout(_layout: BlockLayout, _start: usize) -> Self {
        Silent
    }
}

impl InitialState for Silent {
    fn contribute(&self, _state: &mut StateBuilder) {}
}

#[derive(Ledger)]
struct SilentHeaded {
    a: LedgerCell<U64>,
    std: Silent,
}

#[test]
#[should_panic(expected = "this block embeds 1 and its slots wrote 0")]
fn a_headed_block_without_its_magic_is_refused() {
    // Headed all the same: the placement says so.
    assert_eq!(SilentHeaded::new().a.field_path().as_slice(), &[1]);
    SilentHeaded::initial_state();
}

/// A BODY slot that writes a magic: a claim without a standard.
struct Claimer;

impl LedgerWidth for Claimer {}

impl Claimer {
    const fn at_layout(_layout: BlockLayout, _start: usize) -> Self {
        Claimer
    }
}

impl InitialState for Claimer {
    fn contribute(&self, state: &mut StateBuilder) {
        state.magic::<Mip0099>(Magic::at_path(&[0]));
    }
}

#[derive(Ledger)]
struct Claims {
    claimer: Claimer,
}

#[test]
#[should_panic(expected = "this block embeds 0 and its slots wrote 1")]
fn a_body_slot_that_writes_a_magic_is_refused() {
    Claims::initial_state();
}
