//! The reads: `cell_read*`, `counter_read*`, `mint_read`, `popeq`, `emit`.

use midnight_base_crypto::fab::AlignmentAtom;
use midnight_onchain_vm::ops::Op;
use minocrab::v3::{Circuit3, FieldT, Wire3};
use minocrab::v3::ImpactElem;
use minocrab::{Fr, Public};

use crate::impact::*;
use crate::ops::*;

/// `popeq` / `popeqc` expecting `result`:
/// `[0x0c + cached, alignment header…, limbs…]` (ops.rs:477-480). The limb
/// wires must be the same `public_input` outputs that witnessed the read.
pub fn popeq(cached: bool, result: &LedgerValue) -> ImpactOp {
    let mut elems = vec![ImpactElem::Imm(Fr::from(0x0cu64 + u64::from(cached)))];
    elems.extend(alignment_header(&result.atoms));
    elems.extend(result.elems.iter().copied());
    ImpactOp(elems)
}

/// Emit `ops` as Impact instructions (one per op).
///
/// The guard is AMBIENT (notes/edsl-trim.org §B): [`Circuit3::impact_mixed`]
/// resolves whatever scope the call sits in — the native `1u64` for
/// straight-line code, which inlines as an immediate rather than naming a
/// `Copy`, or a branch condition's wire inside [`Circuit3::when`]. There is
/// no explicit guard parameter here to thread.
pub fn emit(c: &mut Circuit3, ops: &[ImpactOp]) {
    for op in ops {
        c.impact_mixed(1u64, &op.0);
    }
}

// --- reads ------------------------------------------------------------------
//
// A ledger read = `public_input` gates witnessing the read value from
// `public_transcript_outputs` (one per FAB limb, minted BEFORE the op's
// impact instructions — reduce-to-zkir.ss:620-633), then the op's impact
// stream whose trailing `popeq[c]` embeds those same wires as the expected
// result. Reads therefore emit directly into the circuit and return the
// witnessed wires. All shapes are compactc's vm-code (midnight-ledger.ss;
// line refs per function).

/// Mint one `public_input` gate per FAB limb of `atoms`; returns the wires
/// plus the same wires packaged for a `popeq[c]` embed.
///
/// [`Circuit3::public_transcript_input`] resolves the AMBIENT scope
/// (notes/edsl-trim.org §B): unguarded in straight-line code, or under
/// whatever [`Circuit3::when`] the call sits inside — compactc puts the SAME
/// guard on the gates and the op's impact instructions
/// (completeWithdraw.zkir:292-297).
pub fn mint_read(c: &mut Circuit3, atoms: Vec<AlignmentAtom>) -> (Vec<Wire3<FieldT, Public>>, LedgerValue) {
    let limbs: usize = atoms.iter().map(atom_limbs).sum();
    let wires: Vec<Wire3<FieldT, Public>> = (0..limbs)
        .map(|_| c.public_transcript_input::<FieldT>())
        .collect();
    let value = LedgerValue::new(atoms, wires.iter().map(|&w| ImpactElem::Wire(w)).collect());
    (wires, value)
}

/// Name the wires of a minted read for the stale-read backstop
/// (`Circuit3::refuse_stale`, notes/hooks-design.org): `what` is the
/// operation, `path` the slot.
pub fn label_read(c: &mut Circuit3, value: &LedgerValue, what: &str, path: &[LedgerKey]) {
    let wires: Vec<Wire3<FieldT, Public>> = value
        .elems
        .iter()
        .filter_map(|e| match e {
            ImpactElem::Wire(w) => Some(*w),
            ImpactElem::Imm(_) => None,
        })
        .collect();
    let label = if path.is_empty() {
        what.to_string()
    } else {
        format!("{what} at {}", render_path(path))
    };
    c.label_reads(&wires, &label);
}

pub(crate) const U64_ATOM: AlignmentAtom = AlignmentAtom::Bytes { length: 8 };
pub(crate) const BOOL_ATOM: AlignmentAtom = AlignmentAtom::Bytes { length: 1 };

/// `Cell.read()` of the top-level field `index`
/// (midnight-ledger.ss:547-551): `dup 0; idx [field]; popeq` — both the idx
/// and the popeq uncached (`f-cached` = #f). `atoms` is the cell type's FAB
/// alignment; returns one wire per limb, in slot order.
pub fn cell_read(
    c: &mut Circuit3,
    index: u8,
    atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    cell_read_at(c, &field_path(index), atoms)
}

/// [`cell_read`] on a general path.
pub fn cell_read_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    let (wires, value) = mint_read(c, atoms);
    cell_read_embedded_at(c, path, &value);
    wires
}

/// [`cell_read`] against gates the caller has already minted.
///
/// The read shape — `dup 0; idx [field]; popeq` with the witnessed value
/// embedded in the `popeq` — is the same whatever minted the value; what
/// differs is HOW the value was witnessed. A `Bytes<32>` cell mints one
/// native gate per limb ([`mint_read`], which is what [`cell_read`]
/// does). A `Secp256k1Point` cell mints ONE TYPED gate and derives its five
/// limbs with an `encode` instruction (claim.zkir:29-33), so the limbs are
/// computed rather than read and the caller has to build the value itself.
/// Both end here.
pub fn cell_read_embedded(c: &mut Circuit3, index: u8, value: &LedgerValue) {
    cell_read_embedded_at(c, &field_path(index), value)
}

/// [`cell_read_embedded`] on a general path.
pub fn cell_read_embedded_at(c: &mut Circuit3, path: &[LedgerKey], value: &LedgerValue) {
    label_read(c, value, "a cell read", path);
    emit(
        c,
        &[dup(0), idx_path(false, false, path), popeq(false, value)],
    );
}

/// `Counter.read()` on field `index` (midnight-ledger.ss:590-594):
/// `dup 0; idx [field]; popeqc` — the popeq is cached even on the first
/// access (unlike Cell.read). Returns the u64 counter value.
pub fn counter_read(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    counter_read_at(c, &field_path(index))
}

/// [`counter_read`] on a general path.
pub fn counter_read_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![U64_ATOM]);
    label_read(c, &value, "a counter read", path);
    emit(
        c,
        &[dup(0), idx_path(false, false, path), popeq(true, &value)],
    );
    wires[0]
}

/// `Counter.lessThan(threshold)` (midnight-ledger.ss:595-600):
/// `dup 0; idx [field]; push threshold (u64 cell); lt; popeqc` → Boolean.
pub fn counter_less_than(
    c: &mut Circuit3,
    index: u8,
    threshold: &LedgerValue,
) -> Wire3<FieldT, Public> {
    counter_less_than_at(c, &field_path(index), threshold)
}

/// [`counter_less_than`] on a general path.
pub fn counter_less_than_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    threshold: &LedgerValue,
) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a counter comparison", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            push_cell(false, threshold),
            ImpactOp::constant(&Op::Lt),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `Map.member(key)` on field `index` (midnight-ledger.ss:649-655):
/// `dup 0; idx [field]; push key; member; popeqc` → Boolean.
pub fn map_member(c: &mut Circuit3, index: u8, key: &LedgerValue) -> Wire3<FieldT, Public> {
    map_member_at(c, &field_path(index), key)
}

/// [`map_member`] on a general path.
pub fn map_member_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    key: &LedgerValue,
) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a map membership read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            push_cell(false, key),
            ImpactOp::constant(&Op::Member),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `Map.lookup(key)` on field `index`, for flat (Cell) value types
/// (midnight-ledger.ss:741-747): `dup 0; idx [field]; idx {key}; popeq` —
/// the key descent and the popeq both uncached. `value_atoms` is the value
/// type's FAB alignment.
pub fn map_lookup(
    c: &mut Circuit3,
    index: u8,
    key: &LedgerValue,
    value_atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    map_lookup_at(c, &field_path(index), key, value_atoms)
}

/// [`map_lookup`] on a general path.
///
/// NOTE THE TWO `idx`: the path reaches the MAP, and the key descent is a
/// SECOND one-element `idx` (`(idx … [path (list key)])`,
/// midnight-ledger.ss:745-746). A leaf lookup does not append its key to
/// `f`; only an INTERMEDIATE `lookup` — the one whose result is another ADT —
/// does, and that one emits nothing at all.
pub fn map_lookup_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    key: &LedgerValue,
    value_atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    let (wires, value) = mint_read(c, value_atoms);
    label_read(c, &value, "a map lookup", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_key(key),
            popeq(false, &value),
        ],
    );
    wires
}

/// `Map.size()` on field `index` (midnight-ledger.ss:728-733):
/// `dup 0; idx [field]; size; popeqc` → Uint64.
pub fn map_size(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    map_size_at(c, &field_path(index))
}

/// [`map_size`] on a general path.
pub fn map_size_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![U64_ATOM]);
    label_read(c, &value, "a map size read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            ImpactOp::constant(&Op::Size),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `Map.isEmpty()` on field `index` (midnight-ledger.ss:720-727):
/// `dup 0; idx [field]; size; push 0 (u64 cell); eq; popeqc` → Boolean.
pub fn map_is_empty(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    map_is_empty_at(c, &field_path(index))
}

/// [`map_is_empty`] on a general path.
pub fn map_is_empty_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    let zero = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(0u64))]);
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a map is-empty read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            ImpactOp::constant(&Op::Size),
            push_cell(false, &zero),
            ImpactOp::constant(&Op::Eq),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `set.size()` / `set.isEmpty()` — the `Map` streams, exactly
/// ([`set_remove`] carries the argument).
pub fn set_size(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    map_size(c, index)
}

/// [`set_size`] on a general path.
pub fn set_size_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    map_size_at(c, path)
}

/// See [`set_size`].
pub fn set_is_empty(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    map_is_empty(c, index)
}

/// [`set_is_empty`] on a general path.
pub fn set_is_empty_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    map_is_empty_at(c, path)
}

// --- List reads --------------------------------------------------------------

/// `list.length()` on field `index`: `dup 0; idx [field]; idx [2]; popeqc`
/// → Uint64. The length is a stored cell, not a computed `size`.
pub fn list_length(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    list_length_at(c, &field_path(index))
}

/// [`list_length`] on a general path.
pub fn list_length_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![U64_ATOM]);
    label_read(c, &value, "a list length read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, LIST_LENGTH),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `list.isEmpty()` on field `index`: `dup 0; idx [field]; idx [1]; type;
/// push 1u8; eq; popeqc` → Boolean.
///
/// The `1` is `Op::Type`'s code for `Null` (vm.rs:414-425 — a DIFFERENT
/// numbering from `StateValue::field_repr`'s, where `Null` is `0`), so this
/// reads as "the tail is null", which is what an empty list's tail is. See
/// notes/ledger-adts.org §1, which also disposes of the upstream comment
/// claiming `1` encodes a cell.
pub fn list_is_empty(c: &mut Circuit3, index: u8) -> Wire3<FieldT, Public> {
    list_is_empty_at(c, &field_path(index))
}

/// [`list_is_empty`] on a general path.
pub fn list_is_empty_at(c: &mut Circuit3, path: &[LedgerKey]) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a list is-empty read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, LIST_TAIL),
            ImpactOp::constant(&Op::Type),
            push_cell(false, &field_index_value(TYPE_NULL)),
            ImpactOp::constant(&Op::Eq),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `Op::Type`'s result for `StateValue::Null` (vm.rs:414-425).
const TYPE_NULL: u8 = 1;

/// `list.head()` on field `index` → `Maybe<T>`, whose limbs are the returned
/// wires: the tag's, then `elem_atoms`'.
///
/// The one ledger operation with Impact-level control flow in its middle. The
/// `branch` is taken when the head IS null (`Op::Branch` jumps on a truthy
/// cell, vm.rs:1015-1021), landing on the `None` path; the fall-through
/// builds `(1, head)` with a `concat`. Both are constant instructions under
/// the same guard, so the CIRCUIT does not branch — see
/// notes/ledger-adts.org finding (b).
///
/// ```text
/// dup 0; idx [field]; idx [0]; dup 0; type; push 1u8; eq
/// branch 4;  push 1u8; swap 0; concat (2 + max_sizeof(T));  jmp 2
///            pop; push (cell [0u8, default T])
/// popeqc <Maybe<T>>
/// ```
pub fn list_head(
    c: &mut Circuit3,
    index: u8,
    elem_atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    list_head_at(c, &field_path(index), elem_atoms)
}

/// [`list_head`] on a general path.
pub fn list_head_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    elem_atoms: Vec<AlignmentAtom>,
) -> Vec<Wire3<FieldT, Public>> {
    let mut maybe_atoms = vec![BOOL_ATOM];
    maybe_atoms.extend(elem_atoms.iter().copied());
    let none = default_value(maybe_atoms.clone());
    let (wires, value) = mint_read(c, maybe_atoms);
    label_read(c, &value, "a list head read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, LIST_HEAD),
            dup(0),
            ImpactOp::constant(&Op::Type),
            push_cell(false, &field_index_value(TYPE_NULL)),
            ImpactOp::constant(&Op::Eq),
            ImpactOp::constant(&Op::Branch { skip: 4 }),
            push_cell(false, &field_index_value(1)),
            swap(0),
            ImpactOp::constant(&Op::Concat {
                cached: false,
                n: 2 + max_sizeof(&elem_atoms),
            }),
            ImpactOp::constant(&Op::Jmp { skip: 2 }),
            ImpactOp::constant(&Op::Pop),
            push_cell(false, &none),
            popeq(true, &value),
        ],
    );
    wires
}

/// compactc's `rt-max-sizeof` — an upper bound on a type's serialized size,
/// and the operand of `List.head`'s `concat`
/// (reduce-to-zkir.ss:356-375, transcribed).
pub(crate) fn max_sizeof(atoms: &[AlignmentAtom]) -> u32 {
    /// `(ceiling (/ (integer-length n) 8))`.
    fn sep(n: u32) -> u32 {
        (32 - n.leading_zeros()).div_ceil(8)
    }
    if atoms.is_empty() {
        return 2;
    }
    atoms.iter().fold(1 + sep(atoms.len() as u32), |sum, atom| {
        sum + match atom {
            AlignmentAtom::Bytes { length: 0 } => 3,
            AlignmentAtom::Bytes { length: n } => 2 + n + sep(*n),
            AlignmentAtom::Field | AlignmentAtom::Compress => 34,
        }
    })
}

// --- MerkleTree reads --------------------------------------------------------

/// `mt.isFull()` / `hmt.isFull()` on field `index`: `dup 0; idx [field];
/// idx [1]; push 2^depth (u64 cell); lt; neg; popeqc` → Boolean, i.e.
/// `!(next < 2^depth)`.
pub fn merkle_tree_is_full(c: &mut Circuit3, index: u8, depth: u8) -> Wire3<FieldT, Public> {
    merkle_tree_is_full_at(c, &field_path(index), depth)
}

/// [`merkle_tree_is_full`] on a general path.
pub fn merkle_tree_is_full_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    depth: u8,
) -> Wire3<FieldT, Public> {
    let capacity = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(1u64 << depth))]);
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a merkle-tree is-full read", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, TREE_NEXT),
            push_cell(false, &capacity),
            ImpactOp::constant(&Op::Lt),
            ImpactOp::constant(&Op::Neg),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `mt.checkRoot(rt)` on field `index`: `dup 0; idx [field]; idx [0]; root;
/// push rt (field cell); eq; popeqc` → Boolean. `root` is the CURRENT root,
/// so this is an equality — the historic twin is [`historic_merkle_tree_check_root`].
pub fn merkle_tree_check_root(
    c: &mut Circuit3,
    index: u8,
    root: &LedgerValue,
) -> Wire3<FieldT, Public> {
    merkle_tree_check_root_at(c, &field_path(index), root)
}

/// [`merkle_tree_check_root`] on a general path.
pub fn merkle_tree_check_root_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    root: &LedgerValue,
) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a merkle-tree root check", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, TREE),
            ImpactOp::constant(&Op::Root),
            push_cell(false, root),
            ImpactOp::constant(&Op::Eq),
            popeq(true, &value),
        ],
    );
    wires[0]
}

/// `hmt.checkRoot(rt)` on field `index`: `dup 0; idx [field]; idx [2];
/// push rt; member; popeqc` → Boolean. A `member` on the HISTORY map, not an
/// `eq` on the current root — which is the whole difference between the two
/// tree ADTs at read time.
pub fn historic_merkle_tree_check_root(
    c: &mut Circuit3,
    index: u8,
    root: &LedgerValue,
) -> Wire3<FieldT, Public> {
    historic_merkle_tree_check_root_at(c, &field_path(index), root)
}

/// [`historic_merkle_tree_check_root`] on a general path.
pub fn historic_merkle_tree_check_root_at(
    c: &mut Circuit3,
    path: &[LedgerKey],
    root: &LedgerValue,
) -> Wire3<FieldT, Public> {
    let (wires, value) = mint_read(c, vec![BOOL_ATOM]);
    label_read(c, &value, "a historic-merkle-tree root check", path);
    emit(
        c,
        &[
            dup(0),
            idx_path(false, false, path),
            idx_one(false, false, TREE_HISTORY),
            push_cell(false, root),
            ImpactOp::constant(&Op::Member),
            popeq(true, &value),
        ],
    );
    wires[0]
}
