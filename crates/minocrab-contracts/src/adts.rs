//! `adts.compact` — every ledger-ADT operation Compact exposes, one circuit
//! each (M16, notes/ledger-adts.org).
//!
//! Not a corpus contract, and the reason is the M14/M15 one measured again:
//! our IR is v3, only the three sig-net sources carry `--feature-zkir-v3`, and
//! between them their v3 artifacts exercise `Set.insert`, `Set.member` and
//! `List.pushFront` — three of the thirty-one operations here. So the source
//! is ours, lives beside its differential at `tests/fixtures/adts/`, and is
//! compiled with the PINNED compactc (the invocation is in the fixture's
//! header). `pushFront`'s corpus provenance is recovered separately, in
//! `tests/adts_differential.rs`.
//!
//! What each ADT is, at the ledger level — all four are `Array`s or `Map`s
//! and none is a primitive:
//!
//! | Compact | stored as | this module |
//! |---|---|---|
//! | `Set<T>` | a `Map` with `Null` values | [`LedgerSet`] |
//! | `List<T>` | `Array[3]` = `{head, tail, length}` | [`LedgerList`] |
//! | `MerkleTree<n, T>` | `Array[2]` = `{tree, next index}` | [`LedgerMerkleTree`] |
//! | `HistoricMerkleTree<n, T>` | `Array[3]` = `{tree, next index, past roots}` | [`LedgerHistoricMerkleTree`] |
//!
//! TWO THINGS WORTH READING TWICE. `List.head` returns a `Maybe<T>` and
//! contains Impact-level `branch`/`jmp` — transcript control flow, not circuit
//! control flow, so its cost is fixed whether the list is empty or not. And
//! the five `insert*` methods on each tree are only TWO instruction streams:
//! what differs inside a pair is where the 32-byte leaf came from (hashed from
//! the item, handed over, or hashed from the type's default).

use minocrab::v3::Circuit3;
use minocrab::{Private, Public};
use minocrab_std::v3::{
    contract, label, Bool, Disclose, Discloses, Ledger, LedgerCounter, LedgerHistoricMerkleTree,
    LedgerList, LedgerMap, LedgerMerkleTree, LedgerSet, Maybe, MerkleTreeDigest, Uint, B32,
};

label! {
    Element = "element";
    Key = "key";
    Index = "index";
    Hash = "hash";
    Root = "root";
}

/// The tree depth both fixture trees are declared at (`MerkleTree<10, …>`).
pub const DEPTH: u8 = 10;

/// THE LEDGER BLOCK — declaration order is the field index, matching the
/// fixture's `export ledger` block one for one.
#[derive(Ledger)]
pub struct Adts {
    pub dummy: LedgerCounter,
    pub s: LedgerSet<B32<Public>>,
    pub l: LedgerList<B32<Public>>,
    pub m: LedgerMap<B32<Public>, Uint<64, Public>>,
    pub mt: LedgerMerkleTree<DEPTH, B32<Public>>,
    pub hmt: LedgerHistoricMerkleTree<DEPTH, B32<Public>>,
}

/// The contract's ledger block.
pub const ADTS: Adts = Adts::new();

// ---- Set --------------------------------------------------------------------

#[contract]
impl Adts {
    /// `export circuit setInsert(x: Bytes<32>): [] { s.insert(disclose(x)); }`
    #[circuit]
    pub fn set_insert(c: &mut Circuit3, x: B32<Private>) -> Discloses<(Element,)> {
        let x = x.disclose_as::<Element>(c);
        ADTS.s.insert(c, &x);
        Discloses::of(())
    }

    /// `export circuit setMember(x: Bytes<32>): Boolean { return s.member(disclose(x)); }`
    #[circuit(output = "member")]
    pub fn set_member(
        c: &mut Circuit3,
        x: B32<Private>,
    ) -> Discloses<(Element,), Bool<Public>> {
        let x = x.disclose_as::<Element>(c);
        Discloses::of(*ADTS.s.member(c, &x))
    }

    /// `export circuit setRemove(x: Bytes<32>): [] { s.remove(disclose(x)); }`
    #[circuit]
    pub fn set_remove(c: &mut Circuit3, x: B32<Private>) -> Discloses<(Element,)> {
        let x = x.disclose_as::<Element>(c);
        ADTS.s.remove(c, &x);
        Discloses::of(())
    }

    /// `export circuit setSize(): Uint<64> { return s.size(); }`
    #[circuit(output = "size")]
    pub fn set_size(c: &mut Circuit3) -> Discloses<(), Uint<64, Public>> {
        Discloses::of(*ADTS.s.size(c))
    }

    /// `export circuit setIsEmpty(): Boolean { return s.isEmpty(); }`
    #[circuit(output = "empty")]
    pub fn set_is_empty(c: &mut Circuit3) -> Discloses<(), Bool<Public>> {
        Discloses::of(*ADTS.s.is_empty(c))
    }

    /// `export circuit setReset(): [] { s.resetToDefault(); }`
    #[circuit]
    pub fn set_reset(c: &mut Circuit3) -> Discloses<()> {
        ADTS.s.reset_to_default(c);
        Discloses::of(())
    }

    // ---- List -------------------------------------------------------------------

    /// `export circuit listPushFront(x: Bytes<32>): [] { l.pushFront(disclose(x)); }`
    ///
    /// The one M16 operation with corpus provenance: `test-caller-contract`'s
    /// `requestLog.pushFront(requestId)` is this instruction stream with a
    /// different field index.
    #[circuit]
    pub fn list_push_front(c: &mut Circuit3, x: B32<Private>) -> Discloses<(Element,)> {
        let x = x.disclose_as::<Element>(c);
        ADTS.l.push_front(c, &x);
        Discloses::of(())
    }

    /// `export circuit listPopFront(): [] { l.popFront(); }`
    #[circuit]
    pub fn list_pop_front(c: &mut Circuit3) -> Discloses<()> {
        ADTS.l.pop_front(c);
        Discloses::of(())
    }

    /// `export circuit listHead(): Maybe<Bytes<32>> { return l.head(); }`
    #[circuit(output = "head")]
    pub fn list_head(c: &mut Circuit3) -> Discloses<(), Maybe<B32<Public>, Public>> {
        Discloses::of(*ADTS.l.head(c))
    }

    /// `export circuit listLength(): Uint<64> { return l.length(); }`
    #[circuit(output = "length")]
    pub fn list_length(c: &mut Circuit3) -> Discloses<(), Uint<64, Public>> {
        Discloses::of(*ADTS.l.length(c))
    }

    /// `export circuit listIsEmpty(): Boolean { return l.isEmpty(); }`
    #[circuit(output = "empty")]
    pub fn list_is_empty(c: &mut Circuit3) -> Discloses<(), Bool<Public>> {
        Discloses::of(*ADTS.l.is_empty(c))
    }

    /// `export circuit listReset(): [] { l.resetToDefault(); }`
    #[circuit]
    pub fn list_reset(c: &mut Circuit3) -> Discloses<()> {
        ADTS.l.reset_to_default(c);
        Discloses::of(())
    }

    // ---- Map: the two operations LedgerMap was missing --------------------------

    /// `export circuit mapInsertDefault(k: Bytes<32>): [] { m.insertDefault(disclose(k)); }`
    #[circuit]
    pub fn map_insert_default(c: &mut Circuit3, k: B32<Private>) -> Discloses<(Key,)> {
        let k = k.disclose_as::<Key>(c);
        ADTS.m.insert_default(c, &k);
        Discloses::of(())
    }

    /// `export circuit mapReset(): [] { m.resetToDefault(); }`
    #[circuit]
    pub fn map_reset(c: &mut Circuit3) -> Discloses<()> {
        ADTS.m.reset_to_default(c);
        Discloses::of(())
    }

    // ---- MerkleTree -------------------------------------------------------------

    /// `export circuit mtInsert(x: Bytes<32>): [] { mt.insert(disclose(x)); }`
    #[circuit]
    pub fn mt_insert(c: &mut Circuit3, x: B32<Private>) -> Discloses<(Element,)> {
        let x = x.disclose_as::<Element>(c);
        ADTS.mt.insert(c, &x);
        Discloses::of(())
    }

    /// `export circuit mtInsertIndex(x: Bytes<32>, i: Uint<64>): [] { … }`
    #[circuit]
    pub fn mt_insert_index(
        c: &mut Circuit3,
        x: B32<Private>,
        i: Uint<64>,
    ) -> Discloses<(Element, Index)> {
        let x = x.disclose_as::<Element>(c);
        let i = i.disclose_as::<Index>(c);
        ADTS.mt.insert_index(c, &x, i);
        Discloses::of(())
    }

    /// `export circuit mtInsertHash(h: Bytes<32>): [] { mt.insertHash(disclose(h)); }`
    #[circuit]
    pub fn mt_insert_hash(c: &mut Circuit3, h: B32<Private>) -> Discloses<(Hash,)> {
        let h = h.disclose_as::<Hash>(c);
        ADTS.mt.insert_hash(c, &h);
        Discloses::of(())
    }

    /// `export circuit mtInsertHashIndex(h: Bytes<32>, i: Uint<64>): [] { … }`
    #[circuit]
    pub fn mt_insert_hash_index(
        c: &mut Circuit3,
        h: B32<Private>,
        i: Uint<64>,
    ) -> Discloses<(Hash, Index)> {
        let h = h.disclose_as::<Hash>(c);
        let i = i.disclose_as::<Index>(c);
        ADTS.mt.insert_hash_index(c, &h, i);
        Discloses::of(())
    }

    /// `export circuit mtInsertIndexDefault(i: Uint<64>): [] { … }`
    #[circuit]
    pub fn mt_insert_index_default(c: &mut Circuit3, i: Uint<64>) -> Discloses<(Index,)> {
        let i = i.disclose_as::<Index>(c);
        ADTS.mt.insert_index_default(c, i);
        Discloses::of(())
    }

    /// `export circuit mtCheckRoot(r: MerkleTreeDigest): Boolean { … }`
    #[circuit(output = "ok")]
    pub fn mt_check_root(
        c: &mut Circuit3,
        r: MerkleTreeDigest,
    ) -> Discloses<(Root,), Bool<Public>> {
        let r = r.disclose_as::<Root>(c);
        Discloses::of(*ADTS.mt.check_root(c, r))
    }

    /// `export circuit mtIsFull(): Boolean { return mt.isFull(); }`
    #[circuit(output = "full")]
    pub fn mt_is_full(c: &mut Circuit3) -> Discloses<(), Bool<Public>> {
        Discloses::of(*ADTS.mt.is_full(c))
    }

    /// `export circuit mtReset(): [] { mt.resetToDefault(); }`
    #[circuit]
    pub fn mt_reset(c: &mut Circuit3) -> Discloses<()> {
        ADTS.mt.reset_to_default(c);
        Discloses::of(())
    }

    // ---- HistoricMerkleTree -----------------------------------------------------

    /// `export circuit hmtInsert(x: Bytes<32>): [] { hmt.insert(disclose(x)); }`
    #[circuit]
    pub fn hmt_insert(c: &mut Circuit3, x: B32<Private>) -> Discloses<(Element,)> {
        let x = x.disclose_as::<Element>(c);
        ADTS.hmt.insert(c, &x);
        Discloses::of(())
    }

    /// `export circuit hmtInsertIndex(x: Bytes<32>, i: Uint<64>): [] { … }`
    #[circuit]
    pub fn hmt_insert_index(
        c: &mut Circuit3,
        x: B32<Private>,
        i: Uint<64>,
    ) -> Discloses<(Element, Index)> {
        let x = x.disclose_as::<Element>(c);
        let i = i.disclose_as::<Index>(c);
        ADTS.hmt.insert_index(c, &x, i);
        Discloses::of(())
    }

    /// `export circuit hmtInsertHash(h: Bytes<32>): [] { … }`
    #[circuit]
    pub fn hmt_insert_hash(c: &mut Circuit3, h: B32<Private>) -> Discloses<(Hash,)> {
        let h = h.disclose_as::<Hash>(c);
        ADTS.hmt.insert_hash(c, &h);
        Discloses::of(())
    }

    /// `export circuit hmtInsertHashIndex(h: Bytes<32>, i: Uint<64>): [] { … }`
    #[circuit]
    pub fn hmt_insert_hash_index(
        c: &mut Circuit3,
        h: B32<Private>,
        i: Uint<64>,
    ) -> Discloses<(Hash, Index)> {
        let h = h.disclose_as::<Hash>(c);
        let i = i.disclose_as::<Index>(c);
        ADTS.hmt.insert_hash_index(c, &h, i);
        Discloses::of(())
    }

    /// `export circuit hmtInsertIndexDefault(i: Uint<64>): [] { … }`
    #[circuit]
    pub fn hmt_insert_index_default(c: &mut Circuit3, i: Uint<64>) -> Discloses<(Index,)> {
        let i = i.disclose_as::<Index>(c);
        ADTS.hmt.insert_index_default(c, i);
        Discloses::of(())
    }

    /// `export circuit hmtCheckRoot(r: MerkleTreeDigest): Boolean { … }`
    ///
    /// A `member` on the history map, not an equality against the current root —
    /// the whole difference between the two tree ADTs at read time.
    #[circuit(output = "ok")]
    pub fn hmt_check_root(
        c: &mut Circuit3,
        r: MerkleTreeDigest,
    ) -> Discloses<(Root,), Bool<Public>> {
        let r = r.disclose_as::<Root>(c);
        Discloses::of(*ADTS.hmt.check_root(c, r))
    }

    /// `export circuit hmtIsFull(): Boolean { return hmt.isFull(); }`
    #[circuit(output = "full")]
    pub fn hmt_is_full(c: &mut Circuit3) -> Discloses<(), Bool<Public>> {
        Discloses::of(*ADTS.hmt.is_full(c))
    }

    /// `export circuit hmtResetHistory(): [] { hmt.resetHistory(); }`
    #[circuit]
    pub fn hmt_reset_history(c: &mut Circuit3) -> Discloses<()> {
        ADTS.hmt.reset_history(c);
        Discloses::of(())
    }

    /// `export circuit hmtReset(): [] { hmt.resetToDefault(); }`
    #[circuit]
    pub fn hmt_reset(c: &mut Circuit3) -> Discloses<()> {
        ADTS.hmt.reset_to_default(c);
        Discloses::of(())
    }
}
