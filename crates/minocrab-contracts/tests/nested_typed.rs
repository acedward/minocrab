//! THE TYPED SURFACE, against the raw one it was built over (M22 stage B2,
//! notes/coin-arms-nested-adts.org "Design of record").
//!
//! Stage B1 proved the nested LOWERING by hand-building `&[LedgerKey]` paths
//! and comparing all twenty-eight circuits to compactc, instruction for
//! instruction (`nested_differential.rs`). This file is the other half: the
//! same twenty-eight circuits SPELLED THROUGH THE TYPED API —
//!
//! ```ignore
//! NESTED.mm.at_key(c, &k).insert(c, &k2, &v)
//! ```
//!
//! — asserted BYTE-IDENTICAL to `nested::Nested`'s raw spelling. Chaining
//! `at_key` twice covers depth three. Transitively, then, the typed surface
//! is compactc's, because the raw side already is.
//!
//! WHY A TEST AND NOT A SECOND CONTRACT IN `src/`. These circuits are a
//! DUPLICATE of `nested::Nested`'s by construction — that is the whole
//! claim — and listing them in `support::circuits()` would double
//! twenty-eight rows in both frozen snapshots to say a thing this file says
//! exactly. The contract block lives here so the snapshots stay a statement
//! about distinct circuits.
//!
//! WHAT THE TYPED SPELLING ADDS over the raw one, and it is the whole of
//! stage B2:
//!
//! - `at_key` builds the path and emits NOTHING — the `.field()` convention,
//!   and compactc's own shape (`propagate-ledger-paths.ss` folds an
//!   intermediate `lookup` into `f` at compile time);
//! - the leaf method emits the ONE Impact operation Compact names, with the
//!   path re-encoded into it;
//! - `Map` is the only nestable ADT, and that is a TYPE ERROR here rather
//!   than a comment: `LedgerSet<LedgerList<..>>` has no method that would
//!   accept it, exactly as compactc's kind-checker rejects `Set<List<T>>`;
//! - `insertDefault` on an ADT-valued map pushes the ADT's INITIAL VALUE,
//!   chosen by the value type's `LedgerSlot` family rather than by the call
//!   site (`outer_insert_default` below is the differential for it).

use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{Private, Public};
use minocrab_contracts::nested::Nested;
use minocrab_std::v3::{
    contract, label, Bool, Disclose, Discloses, Ledger, LedgerCounter,
    LedgerHistoricMerkleTree, LedgerList, LedgerMap, LedgerMerkleTree, LedgerSet, Maybe,
    MerkleTreeDigest, Uint, B32,
};
use minocrab_zkir::v3::to_zkir_string;

label! {
    Key = "key";
    Key2 = "inner key";
    Key3 = "innermost key";
    Elem = "element";
    Val = "value";
    Root = "root";
}

/// The fixture's `export ledger` block, TYPED — one Rust field per Compact
/// declaration, in declaration order, with the nesting in the type.
///
/// `nested.rs` could not write this: at stage B1 the handle types could not
/// name a nested field, so it declared seven `const … : u8` field indices
/// instead. This is what those became.
#[derive(Ledger)]
struct NestedLedger {
    /// `Map<Bytes<32>, Map<Bytes<32>, Uint<64>>>`
    mm: LedgerMap<B32<Public>, LedgerMap<B32<Public>, Uint<64, Public>>>,
    /// `Map<Bytes<32>, List<Bytes<32>>>`
    ml: LedgerMap<B32<Public>, LedgerList<B32<Public>>>,
    /// `Map<Bytes<32>, Set<Bytes<32>>>`
    ms: LedgerMap<B32<Public>, LedgerSet<B32<Public>>>,
    /// `Map<Bytes<32>, Counter>`
    mc: LedgerMap<B32<Public>, LedgerCounter>,
    /// `Map<Bytes<32>, MerkleTree<8, Bytes<32>>>`
    mt: LedgerMap<B32<Public>, LedgerMerkleTree<8, B32<Public>>>,
    /// `Map<Bytes<32>, HistoricMerkleTree<8, Bytes<32>>>`
    mh: LedgerMap<B32<Public>, LedgerHistoricMerkleTree<8, B32<Public>>>,
    /// `Map<Bytes<32>, Map<Bytes<32>, Map<Bytes<32>, Uint<64>>>>`
    mmm: LedgerMap<B32<Public>, LedgerMap<B32<Public>, LedgerMap<B32<Public>, Uint<64, Public>>>>,
}

/// The ledger block as a `const` item — the nesting costs nothing at run
/// time, because a declared handle is still just its field path.
const NESTED: NestedLedger = NestedLedger::new();

/// The typed twin of `nested::Nested`, circuit for circuit.
struct NestedTyped;

#[contract]
impl NestedTyped {
    // ---- Map<K, Map<K2, V>> -------------------------------------------------

    #[circuit]
    pub fn map_insert(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
        v: Uint<64, Private>,
    ) -> Discloses<(Key, Key2, Val)> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        let v = v.disclose_as::<Val>(c);
        NESTED.mm.at_key(c, &k).insert(c, &k2, &v);
        Discloses::of(())
    }

    #[circuit]
    pub fn map_insert_default(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
    ) -> Discloses<(Key, Key2)> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        NESTED.mm.at_key(c, &k).insert_default(c, &k2);
        Discloses::of(())
    }

    #[circuit(output = "value")]
    pub fn map_lookup(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
    ) -> Discloses<(Key, Key2), Uint<64, Public>> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        Discloses::of(*NESTED.mm.at_key(c, &k).lookup(c, &k2))
    }

    #[circuit(output = "member")]
    pub fn map_member(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
    ) -> Discloses<(Key, Key2), Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        Discloses::of(*NESTED.mm.at_key(c, &k).member(c, &k2))
    }

    #[circuit]
    pub fn map_remove(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
    ) -> Discloses<(Key, Key2)> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        NESTED.mm.at_key(c, &k).remove(c, &k2);
        Discloses::of(())
    }

    #[circuit(output = "size")]
    pub fn map_size(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,), Uint<64, Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.mm.at_key(c, &k).size(c))
    }

    #[circuit(output = "empty")]
    pub fn map_is_empty(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,), Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.mm.at_key(c, &k).is_empty(c))
    }

    #[circuit]
    pub fn map_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mm.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    /// The OUTER map's `insertDefault`, whose value type is an ADT — so the
    /// pushed constant is the empty map and not a cell of zeros, and NOTHING
    /// at this call site says so. The `LedgerSlot` impl for `LedgerMap` does.
    #[circuit]
    pub fn outer_insert_default(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mm.insert_default(c, &k);
        Discloses::of(())
    }

    // ---- Map<K, List<V>> ----------------------------------------------------

    #[circuit]
    pub fn list_push_front(
        c: &mut Circuit3,
        k: B32<Private>,
        v: B32<Private>,
    ) -> Discloses<(Key, Val)> {
        let k = k.disclose_as::<Key>(c);
        let v = v.disclose_as::<Val>(c);
        NESTED.ml.at_key(c, &k).push_front(c, &v);
        Discloses::of(())
    }

    #[circuit]
    pub fn list_pop_front(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.ml.at_key(c, &k).pop_front(c);
        Discloses::of(())
    }

    #[circuit(output = "length")]
    pub fn list_length(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,), Uint<64, Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.ml.at_key(c, &k).length(c))
    }

    #[circuit(output = "head")]
    pub fn list_head(
        c: &mut Circuit3,
        k: B32<Private>,
    ) -> Discloses<(Key,), Maybe<B32<Public>, Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.ml.at_key(c, &k).head(c))
    }

    #[circuit(output = "empty")]
    pub fn list_is_empty(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,), Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.ml.at_key(c, &k).is_empty(c))
    }

    #[circuit]
    pub fn list_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.ml.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    // ---- Map<K, Set<T>> -----------------------------------------------------

    #[circuit]
    pub fn set_insert(
        c: &mut Circuit3,
        k: B32<Private>,
        e: B32<Private>,
    ) -> Discloses<(Key, Elem)> {
        let k = k.disclose_as::<Key>(c);
        let e = e.disclose_as::<Elem>(c);
        NESTED.ms.at_key(c, &k).insert(c, &e);
        Discloses::of(())
    }

    #[circuit]
    pub fn set_remove(
        c: &mut Circuit3,
        k: B32<Private>,
        e: B32<Private>,
    ) -> Discloses<(Key, Elem)> {
        let k = k.disclose_as::<Key>(c);
        let e = e.disclose_as::<Elem>(c);
        NESTED.ms.at_key(c, &k).remove(c, &e);
        Discloses::of(())
    }

    #[circuit(output = "member")]
    pub fn set_member(
        c: &mut Circuit3,
        k: B32<Private>,
        e: B32<Private>,
    ) -> Discloses<(Key, Elem), Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        let e = e.disclose_as::<Elem>(c);
        Discloses::of(*NESTED.ms.at_key(c, &k).member(c, &e))
    }

    #[circuit]
    pub fn set_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.ms.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    // ---- Map<K, Counter> ----------------------------------------------------

    #[circuit]
    pub fn counter_increment(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mc.at_key(c, &k).increment(c, 1);
        Discloses::of(())
    }

    #[circuit(output = "count")]
    pub fn counter_read(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,), Uint<64, Public>> {
        let k = k.disclose_as::<Key>(c);
        Discloses::of(*NESTED.mc.at_key(c, &k).read(c))
    }

    #[circuit]
    pub fn counter_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mc.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    // ---- Map<K, MerkleTree> / Map<K, HistoricMerkleTree> --------------------

    #[circuit]
    pub fn mt_insert(
        c: &mut Circuit3,
        k: B32<Private>,
        item: B32<Private>,
    ) -> Discloses<(Key, Elem)> {
        let k = k.disclose_as::<Key>(c);
        let item = item.disclose_as::<Elem>(c);
        NESTED.mt.at_key(c, &k).insert(c, &item);
        Discloses::of(())
    }

    #[circuit(output = "ok")]
    pub fn mt_check_root(
        c: &mut Circuit3,
        k: B32<Private>,
        rt: MerkleTreeDigest<Private>,
    ) -> Discloses<(Key, Root), Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        let rt = rt.disclose_as::<Root>(c);
        Discloses::of(*NESTED.mt.at_key(c, &k).check_root(c, rt))
    }

    #[circuit]
    pub fn mt_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mt.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    #[circuit]
    pub fn hmt_insert(
        c: &mut Circuit3,
        k: B32<Private>,
        item: B32<Private>,
    ) -> Discloses<(Key, Elem)> {
        let k = k.disclose_as::<Key>(c);
        let item = item.disclose_as::<Elem>(c);
        NESTED.mh.at_key(c, &k).insert(c, &item);
        Discloses::of(())
    }

    #[circuit]
    pub fn hmt_reset_history(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mh.at_key(c, &k).reset_history(c);
        Discloses::of(())
    }

    #[circuit]
    pub fn hmt_reset(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        NESTED.mh.at_key(c, &k).reset_to_default(c);
        Discloses::of(())
    }

    // ---- three levels: at_key CHAINED ---------------------------------------

    #[circuit]
    pub fn deep_insert(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
        k3: B32<Private>,
        v: Uint<64, Private>,
    ) -> Discloses<(Key, Key2, Key3, Val)> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        let k3 = k3.disclose_as::<Key3>(c);
        let v = v.disclose_as::<Val>(c);
        NESTED.mmm.at_key(c, &k).at_key(c, &k2).insert(c, &k3, &v);
        Discloses::of(())
    }

    #[circuit(output = "value")]
    pub fn deep_lookup(
        c: &mut Circuit3,
        k: B32<Private>,
        k2: B32<Private>,
        k3: B32<Private>,
    ) -> Discloses<(Key, Key2, Key3), Uint<64, Public>> {
        let k = k.disclose_as::<Key>(c);
        let k2 = k2.disclose_as::<Key2>(c);
        let k3 = k3.disclose_as::<Key3>(c);
        Discloses::of(*NESTED.mmm.at_key(c, &k).at_key(c, &k2).lookup(c, &k3))
    }
}

/// Every circuit, typed spelling against raw spelling.
fn pairs() -> Vec<(&'static str, fn() -> Compiled3, fn() -> Compiled3)> {
    vec![
        ("map_insert", NestedTyped::map_insert as fn() -> Compiled3, Nested::map_insert as fn() -> Compiled3),
        ("map_insert_default", NestedTyped::map_insert_default, Nested::map_insert_default),
        ("map_lookup", NestedTyped::map_lookup, Nested::map_lookup),
        ("map_member", NestedTyped::map_member, Nested::map_member),
        ("map_remove", NestedTyped::map_remove, Nested::map_remove),
        ("map_size", NestedTyped::map_size, Nested::map_size),
        ("map_is_empty", NestedTyped::map_is_empty, Nested::map_is_empty),
        ("map_reset", NestedTyped::map_reset, Nested::map_reset),
        ("outer_insert_default", NestedTyped::outer_insert_default, Nested::outer_insert_default),
        ("list_push_front", NestedTyped::list_push_front, Nested::list_push_front),
        ("list_pop_front", NestedTyped::list_pop_front, Nested::list_pop_front),
        ("list_length", NestedTyped::list_length, Nested::list_length),
        ("list_head", NestedTyped::list_head, Nested::list_head),
        ("list_is_empty", NestedTyped::list_is_empty, Nested::list_is_empty),
        ("list_reset", NestedTyped::list_reset, Nested::list_reset),
        ("set_insert", NestedTyped::set_insert, Nested::set_insert),
        ("set_remove", NestedTyped::set_remove, Nested::set_remove),
        ("set_member", NestedTyped::set_member, Nested::set_member),
        ("set_reset", NestedTyped::set_reset, Nested::set_reset),
        ("counter_increment", NestedTyped::counter_increment, Nested::counter_increment),
        ("counter_read", NestedTyped::counter_read, Nested::counter_read),
        ("counter_reset", NestedTyped::counter_reset, Nested::counter_reset),
        ("mt_insert", NestedTyped::mt_insert, Nested::mt_insert),
        ("mt_check_root", NestedTyped::mt_check_root, Nested::mt_check_root),
        ("mt_reset", NestedTyped::mt_reset, Nested::mt_reset),
        ("hmt_insert", NestedTyped::hmt_insert, Nested::hmt_insert),
        ("hmt_reset_history", NestedTyped::hmt_reset_history, Nested::hmt_reset_history),
        ("hmt_reset", NestedTyped::hmt_reset, Nested::hmt_reset),
        ("deep_insert", NestedTyped::deep_insert, Nested::deep_insert),
        ("deep_lookup", NestedTyped::deep_lookup, Nested::deep_lookup),
    ]
}

/// THE HEADLINE: the typed spelling's ZKIR IS the raw spelling's, byte for
/// byte — not modulo renaming, not modulo folding. Both sides are ours, so
/// there is nothing to canonicalize away.
#[test]
fn the_typed_spelling_is_the_raw_one() {
    for (name, typed, raw) in pairs() {
        let (typed, raw) = (
            to_zkir_string(&typed().ir).expect("serializes"),
            to_zkir_string(&raw().ir).expect("serializes"),
        );
        assert_eq!(typed, raw, "{name}: the typed spelling lowers differently");
    }
}

/// EVERY circuit of the raw contract has a typed twin, compared by FUNCTION
/// POINTER — `nested_differential` makes the same check against compactc's
/// artifacts, and this one keeps the two sides in step as the fixture grows.
#[test]
fn every_raw_circuit_has_a_typed_twin() {
    let paired: std::collections::HashSet<usize> =
        pairs().iter().map(|(_, _, raw)| *raw as usize).collect();
    let missing: Vec<&str> = Nested::CIRCUITS
        .iter()
        .filter(|(_, build)| !paired.contains(&(*build as usize)))
        .map(|(name, _)| *name)
        .collect();
    assert!(
        missing.is_empty(),
        "these raw circuits have no typed re-expression: {missing:?}"
    );
}

/// …and no typed circuit is left out of the comparison either.
#[test]
fn every_typed_circuit_is_compared() {
    let paired: std::collections::HashSet<usize> =
        pairs().iter().map(|(_, typed, _)| *typed as usize).collect();
    let missing: Vec<&str> = NestedTyped::CIRCUITS
        .iter()
        .filter(|(_, build)| !paired.contains(&(*build as usize)))
        .map(|(name, _)| *name)
        .collect();
    assert!(missing.is_empty(), "not compared: {missing:?}");
}

/// The ledger block's FIELD PATHS are the declaration order, because seven
/// fields fit one segment — the same statement `nested.rs`'s `const MM: u8 =
/// 0;` made, now made by the derive.
#[test]
fn the_derive_gives_the_seven_fields_their_declaration_order() {
    assert_eq!(NESTED.mm.index(), 0);
    assert_eq!(NESTED.ml.index(), 1);
    assert_eq!(NESTED.ms.index(), 2);
    assert_eq!(NESTED.mc.index(), 3);
    assert_eq!(NESTED.mt.index(), 4);
    assert_eq!(NESTED.mh.index(), 5);
    assert_eq!(NESTED.mmm.index(), 6);
}
