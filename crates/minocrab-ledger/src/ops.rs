//! The ledger operations: cell/counter/map/set/list/merkle-tree writes and
//! resets, the `_at` path variants, and the coin arms.

use midnight_base_crypto::fab::{
    Alignment, AlignmentAtom, AlignmentSegment, AlignedValue, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_onchain_vm::ops::{Key, Op};
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::HashMap as StorageHashMap;
use midnight_transient_crypto::merkle_tree::MerkleTree as VmMerkleTree;
use minocrab::v3::ImpactElem;
use minocrab::Fr;

use crate::impact::*;

/// A `Uint<64>` as an `AlignedValue`: one `bytes<8>` atom. The initial-value
/// constants of `List` (its length) and both trees (their next index) are
/// this, and nothing else in the crate needs it.
pub(crate) fn u64_aligned(value: u64) -> AlignedValue {
    AlignedValue::new(
        Value(vec![ValueAtom(value.to_le_bytes().to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 8,
        })]),
    )
    .expect("a u64 fits a bytes<8> atom")
}

/// `insc n`, with compactc's own nibble bound stated.
fn insc(n: usize) -> ImpactOp {
    assert!(
        n <= 15,
        "insc {n}: the depth does not fit the opcode's low nibble"
    );
    ImpactOp::constant(&Op::Ins {
        cached: true,
        n: n as u8,
    })
}

/// `ins 1` — the uncached insert every write closes its inner slot with.
fn ins1() -> ImpactOp {
    ImpactOp::constant(&Op::Ins {
        cached: false,
        n: 1,
    })
}

// --- PATH SUPPRESSION -------------------------------------------------------
//
// Nine operations REPLACE a whole field rather than reach inside it —
// `Cell.write`, `Cell.writeCoin`, `Cell.resetToDefault`,
// `Counter.resetToDefault`, and the five collections' `resetToDefault`
// (midnight-ledger.ss:554, 561, 573, 616, 627, 715, 821, 1015, 1178). They
// alone split `f` into "the path to the container" and "the key to write":
//
//   (idx [pushPath #t] [path (suppress-null (reverse (cdr (reverse f))))])
//   (push [storage #f] [value (state-value 'cell (car (reverse f)))])
//   …
//   (ins [cached #t] [n (suppress-zero (sub1 (length f)))])
//
// `suppress-null` / `suppress-zero` (vm.ss:192-194) turn the degenerate
// operand into `VMsuppress`, which `assemble1` maps to the EMPTY operand list
// and `assemble` then drops — the instruction disappears. At depth 1 both
// vanish, which is why a top-level `Cell` write is three instructions. At
// depth 2 BOTH become live: `idxp [field]` and `insc 1` reappear, exactly as
// the probe of `a.lookup(k).resetToDefault()` shows.
//
// This is the one place our encoding must diverge from `Op::field_repr`:
// upstream's `Op::Ins { n: 0 }` writes `0xa0` rather than nothing, so the
// suppressed `insc` has to be OMITTED here and not encoded as zero.
// (`Op::Idx` with an empty path already writes nothing, so that half agrees.)

/// The leading `idxp` of a whole-field-replace op: the path MINUS its last
/// element, suppressed away entirely when that leaves nothing.
fn idxp_container(path: &[LedgerKey]) -> Vec<ImpactOp> {
    let head = &path[..path.len() - 1];
    if head.is_empty() {
        Vec::new()
    } else {
        vec![idx_path(false, true, head)]
    }
}

/// The closing `insc` of a whole-field-replace op: `len(f) − 1`, suppressed
/// away entirely at zero.
fn insc_container(path: &[LedgerKey]) -> Vec<ImpactOp> {
    if path.len() == 1 {
        Vec::new()
    } else {
        vec![insc(path.len() - 1)]
    }
}

// --- compactc's vm-code per ledger operation (midnight-ledger.ss) -----------
//
// Every builder comes in two forms: `foo(index: u8, ..)` for a top-level
// field and `foo_at(path: &[LedgerKey], ..)` for the general case. The `u8`
// form is a one-line wrapper over the one-element path, so the widening adds
// a capability without moving a single byte of what the crate already emits
// (M22 stage B1's zero-movement gate).

/// `Counter.increment(amount)` on ledger field `index`
/// (midnight-ledger.ss:605-609): `idxp [field]; addi amount; insc 1`.
pub fn counter_increment(index: u8, amount: u32) -> Vec<ImpactOp> {
    counter_increment_at(&field_path(index), amount)
}

/// [`counter_increment`] on a general path: `idxp f; addi amount; insc len(f)`.
pub fn counter_increment_at(path: &[LedgerKey], amount: u32) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        ImpactOp::constant(&Op::Addi { immediate: amount }),
        insc(path.len()),
    ]
}

/// `field = value` — Cell write to a top-level field
/// (midnight-ledger.ss:552-558 with the idxp/insc pair suppressed for
/// top-level fields, reduce-to-zkir.ss:595-608): `push key; pushs value;
/// ins 1`.
pub fn cell_write(index: u8, value: &LedgerValue) -> Vec<ImpactOp> {
    cell_write_at(&field_path(index), value)
}

/// [`cell_write`] on a general path — one of the NINE whole-field-replace ops
/// (see "PATH SUPPRESSION" above), so the leading `idxp` and closing `insc`
/// are live at depth 2 and suppressed at depth 1:
///
/// ```text
/// idxp f[..len-1];  push f[len-1];  pushs value;  ins 1;  insc len(f)-1
/// ```
pub fn cell_write_at(path: &[LedgerKey], value: &LedgerValue) -> Vec<ImpactOp> {
    let mut ops = idxp_container(path);
    ops.push(path[path.len() - 1].push_as_cell());
    ops.push(push_cell(true, value));
    ops.push(ins1());
    ops.extend(insc_container(path));
    ops
}

/// `Cell<QualifiedShieldedCoinInfo>.writeCoin(coin, recipient)` on the
/// top-level field `index` (midnight-ledger.ss:567-583): the coin's
/// Merkle-tree index is resolved by indexing the context's
/// commitment-index map (context\[1\]) with the coin's commitment (from the
/// stack) and concatenated onto the coin, writing the resulting
/// QualifiedShieldedCoinInfo. `push key; dup 3; push cm; idxc [1, stack];
/// push coin; swap 0; concatc 91; ins 1` — the leading idx (empty path)
/// and trailing insc 0 are compactc's depth-1 suppressions; the `dup 3`
/// reaches the context past the key push, the result slot, and effects.
/// `cm` is the runtime coin commitment (`rt-coin-commit`, a `bytes<32>`);
/// `coin` the 3-atom `[bytes<32>, bytes<32>, bytes<16>]` ShieldedCoinInfo.
///
/// The middle six are `qualify_coin`, shared with the three collection
/// arms; this is `cell_write` with its value push replaced by them.
pub fn cell_write_coin(index: u8, cm: &LedgerValue, coin: &LedgerValue) -> Vec<ImpactOp> {
    cell_write_coin_at(&field_path(index), cm, coin)
}

/// [`cell_write_coin`] on a general path — [`cell_write_at`] with its value
/// push replaced by `qualify_coin`, and the `dup` reach growing with the
/// path (`cell_coin_dup`).
pub fn cell_write_coin_at(path: &[LedgerKey], cm: &LedgerValue, coin: &LedgerValue) -> Vec<ImpactOp> {
    let mut ops = idxp_container(path);
    ops.push(path[path.len() - 1].push_as_cell());
    ops.extend(qualify_coin(cell_coin_dup(path.len()), cm, coin));
    ops.push(ins1());
    ops.extend(insc_container(path));
    ops
}

/// THE QUALIFY DANCE — the six instructions all four coin arms share
/// (`Cell.writeCoin`, `Set.insertCoin`, `Map.insertCoin`,
/// `List.pushFrontCoin`; midnight-ledger.ss:567-583, :670-696, :769-795,
/// :918-968).
///
/// It turns a `ShieldedCoinInfo` into the `QualifiedShieldedCoinInfo` the
/// four store, by resolving the coin's Merkle-tree index on chain and
/// concatenating it on:
///
/// ```text
/// dup dup_n                   // reach the CONTEXT down the stack
/// push (cell cm)              // the runtime coin commitment
/// idxc [(1), stack]           // context[1][cm] → the coin's mt_index
/// push (cell coin)            // the 3-atom ShieldedCoinInfo
/// swap 0
/// concatc 91                  // [nonce, color, value] ++ [mt_index]
/// ```
///
/// `91` is `2 + rt-max-sizeof(QualifiedShieldedCoinInfo)` and is a literal in
/// compactc's source. `cm` is the runtime coin commitment (`rt-coin-commit`,
/// a `bytes<32>`); `coin` the 3-atom `[bytes<32>, bytes<32>, bytes<16>]`
/// `ShieldedCoinInfo`.
///
/// THE ONLY THING THAT DIFFERS between the four arms is `dup_n` and what
/// surrounds the six — each arm is its plain twin with one push replaced by
/// this. The reach is past the pushes the arm has already made, the result
/// slot, the `2n` path items the leading `idx` left, and the effects, so it
/// is a per-arm constant at depth 1 (the four `*_COIN_DUP` below).
fn qualify_coin(dup_n: u8, cm: &LedgerValue, coin: &LedgerValue) -> [ImpactOp; 6] {
    [
        dup(dup_n),
        push_cell(false, cm),
        ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Value(field_key(1)), Key::Stack].into(),
        }),
        push_cell(false, coin),
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Concat { cached: true, n: 91 }),
    ]
}

/// The four coin arms' `qualify_coin` reaches, as compactc writes them —
/// each counting the arm's own pushes, the result slot, the `2·len(f)` path
/// items the leading `idx` left, and the effects. At `len(f) = 1` they are
/// 3, 4, 5 and 7 (pinned by the tests below).
///
/// compactc notes at midnight-ledger.ss:576-577 that a long `f` overflows the
/// `dup` nibble; [`dup`] asserts what compactc only comments.
pub(crate) fn cell_coin_dup(len: usize) -> u8 {
    (3 + 2 * (len - 1)) as u8
}

/// See `cell_coin_dup`.
pub(crate) fn set_coin_dup(len: usize) -> u8 {
    (2 + 2 * len) as u8
}

/// See `cell_coin_dup`.
pub(crate) fn map_coin_dup(len: usize) -> u8 {
    (3 + 2 * len) as u8
}

/// See `cell_coin_dup`.
pub(crate) fn list_coin_dup(len: usize) -> u8 {
    (5 + 2 * len) as u8
}

/// `map.insert(key, value)` on ledger field `index`:
/// `idxp [field]; push key; pushs value; ins 1; insc 1`.
pub fn map_insert(index: u8, key: &LedgerValue, value: &LedgerValue) -> Vec<ImpactOp> {
    map_insert_at(&field_path(index), key, value)
}

/// [`map_insert`] on a general path: `idxp f; push key; pushs value; ins 1;
/// insc len(f)`. The nested form of `m.lookup(k).insert(k2, v)`, and the
/// stream OpenZeppelin's `ShieldedMultiSig.approveProposal` compiles to
/// (`0x71 … 0x91 0xa2`).
pub fn map_insert_at(path: &[LedgerKey], key: &LedgerValue, value: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, key),
        push_cell(true, value),
        ins1(),
        insc(path.len()),
    ]
}

/// `Map<K, QualifiedShieldedCoinInfo>.insertCoin(key, coin, recipient)` on
/// ledger field `index` (midnight-ledger.ss:769-795) — [`map_insert`] with
/// its `pushs value` replaced by `qualify_coin`:
///
/// ```text
/// idxp [field]; push key
/// dup 5; push cm; idxc [(1), stack]; push coin; swap 0; concatc 91
/// ins 1; insc 1
/// ```
///
/// The `dup 5` reaches the context past the key push, the map, the two path
/// items the `idxp` left, and the effects.
pub fn map_insert_coin(
    index: u8,
    key: &LedgerValue,
    cm: &LedgerValue,
    coin: &LedgerValue,
) -> Vec<ImpactOp> {
    map_insert_coin_at(&field_path(index), key, cm, coin)
}

/// [`map_insert_coin`] on a general path.
pub fn map_insert_coin_at(
    path: &[LedgerKey],
    key: &LedgerValue,
    cm: &LedgerValue,
    coin: &LedgerValue,
) -> Vec<ImpactOp> {
    let mut ops = vec![idx_path(false, true, path), push_cell(false, key)];
    ops.extend(qualify_coin(map_coin_dup(path.len()), cm, coin));
    ops.push(ins1());
    ops.push(insc(path.len()));
    ops
}

/// `map.remove(key)` on ledger field `index` (midnight-ledger.ss Map
/// `remove`; claim.zkir:287-291): `idxp [field]; push key; rem; insc 1`.
pub fn map_remove(index: u8, key: &LedgerValue) -> Vec<ImpactOp> {
    map_remove_at(&field_path(index), key)
}

/// [`map_remove`] on a general path.
pub fn map_remove_at(path: &[LedgerKey], key: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, key),
        ImpactOp::constant(&Op::Rem { cached: false }),
        insc(path.len()),
    ]
}

/// `set.insert(elem)` on ledger field `index` — `map_insert` with a `Null`
/// value (midnight-ledger.ss's Set vm-code; xcontract-events
/// depositViaVault): `idxp [field]; push elem; pushs null; ins 1; insc 1`.
pub fn set_insert(index: u8, elem: &LedgerValue) -> Vec<ImpactOp> {
    set_insert_at(&field_path(index), elem)
}

/// [`set_insert`] on a general path.
pub fn set_insert_at(path: &[LedgerKey], elem: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, elem),
        ImpactOp::constant(&Op::Push {
            storage: true,
            value: midnight_onchain_state::state::StateValue::Null,
        }),
        ins1(),
        insc(path.len()),
    ]
}

/// `Set<QualifiedShieldedCoinInfo>.insertCoin(coin, recipient)` on ledger
/// field `index` (midnight-ledger.ss:670-696) — [`set_insert`] with its
/// `push elem` replaced by `qualify_coin`:
///
/// ```text
/// idxp [field]
/// dup 4; push cm; idxc [(1), stack]; push coin; swap 0; concatc 91
/// pushs null; ins 1; insc 1
/// ```
///
/// The qualified coin is the KEY the `Null` is stored under, so the dance
/// runs BEFORE the `pushs null` — the `dup 4` reaches the context past the
/// set, the two path items the `idxp` left, and the effects.
pub fn set_insert_coin(index: u8, cm: &LedgerValue, coin: &LedgerValue) -> Vec<ImpactOp> {
    set_insert_coin_at(&field_path(index), cm, coin)
}

/// [`set_insert_coin`] on a general path.
pub fn set_insert_coin_at(path: &[LedgerKey], cm: &LedgerValue, coin: &LedgerValue) -> Vec<ImpactOp> {
    let mut ops = vec![idx_path(false, true, path)];
    ops.extend(qualify_coin(set_coin_dup(path.len()), cm, coin));
    ops.push(ImpactOp::constant(&Op::Push {
        storage: true,
        value: midnight_onchain_state::state::StateValue::Null,
    }));
    ops.push(ins1());
    ops.push(insc(path.len()));
    ops
}

/// `set.remove(elem)` on ledger field `index` — the SAME instruction stream
/// `map.remove(key)` is, because a Compact `Set` is a `Map` with `Null`
/// values and `remove` does not touch the value (fixture `setRemove` is
/// `map_remove`'s stream, notes/ledger-adts.org §1). Named for the caller's
/// sake; it emits nothing of its own.
pub fn set_remove(index: u8, elem: &LedgerValue) -> Vec<ImpactOp> {
    map_remove(index, elem)
}

/// [`set_remove`] on a general path — see [`map_remove_at`].
pub fn set_remove_at(path: &[LedgerKey], elem: &LedgerValue) -> Vec<ImpactOp> {
    map_remove_at(path, elem)
}

/// `map.insertDefault(key)` / a `Map` whose value type's default is written
/// (midnight-ledger.ss Map `insertDefault`): `idxp [field]; push key;
/// pushs default; ins 1; insc 1`. `value_atoms` is the VALUE type's
/// alignment; the limbs are zeros ([`default_value`]).
pub fn map_insert_default(index: u8, key: &LedgerValue, value_atoms: Vec<AlignmentAtom>) -> Vec<ImpactOp> {
    map_insert(index, key, &default_value(value_atoms))
}

/// [`map_insert_default`] on a general path.
pub fn map_insert_default_at(
    path: &[LedgerKey],
    key: &LedgerValue,
    value_atoms: Vec<AlignmentAtom>,
) -> Vec<ImpactOp> {
    map_insert_at(path, key, &default_value(value_atoms))
}

/// `map.insertDefault(key)` where the VALUE TYPE IS AN ADT — a different
/// instruction from [`map_insert_default`] (notes/coin-arms-nested-adts.org
/// records how this one was found).
///
/// compactc's `insert`/`insertDefault` push `(state-value 'ADT value
/// value_type)`, and `assemble-operand-acc`'s `VMstate-value-ADT` case
/// (reduce-to-zkir.ss:424-433) DISCARDS the value and emits the ADT's own
/// `(initial-value …)` whenever the type is an ADT — the empty map for
/// `Map`/`Set`, `[null, null, cell 0u64]` for `List`, `cell 0u64` for
/// `Counter`, the blank tree pair for the two trees. Only when the type is
/// NOT an ADT does it fall through to `(cons 1 val)`, the plain cell
/// [`map_insert_default`] pushes.
///
/// So an ADT-valued `insertDefault` is `idxp f; push key; pushs <the ADT's
/// initial value>; ins 1; insc len(f)` — verified against compactc for
/// `Map<K, Map<..>>`, `Map<K, List<..>>` and `Map<K, Counter>`. The initial
/// values are the same constants `resetToDefault` writes, so they come from
/// [`empty_map`], [`empty_list`], [`empty_counter`] and `empty_merkle_tree`
/// rather than a second table.
pub fn map_insert_adt_default_at(
    path: &[LedgerKey],
    key: &LedgerValue,
    initial: StateValue<InMemoryDB>,
) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, key),
        ImpactOp::constant(&Op::Push {
            storage: true,
            value: initial,
        }),
        ins1(),
        insc(path.len()),
    ]
}

/// The shared shape of every `resetToDefault`: `idxp f[..len-1];
/// push f[len-1]; pushs initial; ins 1; insc len(f)-1`, the first and last
/// suppressed at depth 1.
///
/// One of the NINE whole-field-replace ops — see "PATH SUPPRESSION" above and
/// notes/ledger-adts.org finding (d). Five of the six `resetToDefault`s go
/// through here; `HistoricMerkleTree`'s open-codes its own because its
/// closing pair is asymmetric.
fn reset_to_at(path: &[LedgerKey], initial: StateValue<InMemoryDB>) -> Vec<ImpactOp> {
    let mut ops = idxp_container(path);
    ops.push(path[path.len() - 1].push_as_cell());
    ops.push(ImpactOp::constant(&Op::Push {
        storage: true,
        value: initial,
    }));
    ops.push(ins1());
    ops.extend(insc_container(path));
    ops
}

/// `map.resetToDefault()` on field `index`: `push key; pushs (empty map);
/// ins 1`.
pub fn map_reset(index: u8) -> Vec<ImpactOp> {
    map_reset_at(&field_path(index))
}

/// [`map_reset`] on a general path.
pub fn map_reset_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    reset_to_at(path, empty_map())
}

/// `set.resetToDefault()` — [`map_reset`], since a `Set`'s initial value is
/// the empty map a `Map`'s is.
pub fn set_reset(index: u8) -> Vec<ImpactOp> {
    map_reset(index)
}

/// [`set_reset`] on a general path.
pub fn set_reset_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    map_reset_at(path)
}

/// A `Map`'s (and a `Set`'s) initial value: the empty map.
pub fn empty_map() -> StateValue<InMemoryDB> {
    StateValue::Map(StorageHashMap::new())
}

/// A `Counter`'s initial value: `cell 0u64`.
pub fn empty_counter() -> StateValue<InMemoryDB> {
    StateValue::Cell(Sp::new(u64_aligned(0)))
}

/// `counter.resetToDefault()` on field `index` (midnight-ledger.ss:614-620) —
/// the fourth of the nine whole-field-replace ops, and the one the crate had
/// no builder for until a NESTED `Map<K, Counter>` needed it.
pub fn counter_reset(index: u8) -> Vec<ImpactOp> {
    counter_reset_at(&field_path(index))
}

/// [`counter_reset`] on a general path.
pub fn counter_reset_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    reset_to_at(path, empty_counter())
}

// --- List: an `Array[3]` of `{head cell, tail list, length}` ----------------

/// A `List`'s initial value: `[null, null, cell 0u64]`.
pub fn empty_list() -> StateValue<InMemoryDB> {
    StateValue::Array(
        [
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(u64_aligned(0))),
        ]
        .into(),
    )
}

/// `list.resetToDefault()` on field `index`.
pub fn list_reset(index: u8) -> Vec<ImpactOp> {
    list_reset_at(&field_path(index))
}

/// [`list_reset`] on a general path.
pub fn list_reset_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    reset_to_at(path, empty_list())
}

/// `list.pushFront(value)` on field `index` (midnight-ledger.ss List
/// `pushFront`; the corpus's own shape is test-caller-contract
/// submitSignatureRequest.zkir:43-55):
///
/// ```text
/// idxp [field]; dup 0; idx [2]; addi 1        // len + 1
/// pushs [cell value, null, null]              // the new node
/// swap 0; push 2u8; swap 0; insc 1            // node[2] = len + 1
/// swap 0; push 1u8; swap 0; insc 2            // node[1] = the old list
/// ```
pub fn list_push_front(index: u8, value: &LedgerValue) -> Vec<ImpactOp> {
    list_push_front_at(&field_path(index), value)
}

/// [`list_push_front`] on a general path. The closing `insc` is
/// `len(f) + 1` — the only op family whose depth arithmetic is not
/// `len(f)` — and the `insc 1` in the middle is a literal 1 at every depth.
pub fn list_push_front_at(path: &[LedgerKey], value: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        dup(0),
        idx_one(false, false, LIST_LENGTH),
        ImpactOp::constant(&Op::Addi { immediate: 1 }),
        push_array(
            true,
            &[
                LedgerElem::Cell(value.clone()),
                LedgerElem::Null,
                LedgerElem::Null,
            ],
        ),
        swap(0),
        push_cell(false, &field_index_value(LIST_LENGTH)),
        swap(0),
        ImpactOp::constant(&Op::Ins { cached: true, n: 1 }),
        swap(0),
        push_cell(false, &field_index_value(LIST_TAIL)),
        swap(0),
        insc(path.len() + 1),
    ]
}

/// `List<QualifiedShieldedCoinInfo>.pushFrontCoin(coin, recipient)` on field
/// `index` (midnight-ledger.ss:918-968) — the one arm that is NOT a
/// one-for-one swap, because [`list_push_front`] builds its new node with the
/// value already in it and this cannot: the qualified coin does not exist
/// until the dance has run against a node that is already on the stack.
///
/// So the node is pushed BLANK, the position key `0u8` goes on, the dance
/// runs, and an `insc 1` puts the coin at `node[0]`. Eight instructions
/// longer than `pushFront`'s thirteen; the tail is identical.
///
/// ```text
/// idxp [field]; dup 0; idx [2]; addi 1        // len + 1
/// pushs [null, null, null]                    // the BLANK new node
/// push 0u8                                    // node[0], the head slot
/// dup 7; push cm; idxc [(1), stack]; push coin; swap 0; concatc 91
/// insc 1                                      // node[0] = the qualified coin
/// swap 0; push 2u8; swap 0; insc 1            // node[2] = len + 1
/// swap 0; push 1u8; swap 0; insc 2            // node[1] = the old list
/// ```
pub fn list_push_front_coin(index: u8, cm: &LedgerValue, coin: &LedgerValue) -> Vec<ImpactOp> {
    list_push_front_coin_at(&field_path(index), cm, coin)
}

/// [`list_push_front_coin`] on a general path.
pub fn list_push_front_coin_at(
    path: &[LedgerKey],
    cm: &LedgerValue,
    coin: &LedgerValue,
) -> Vec<ImpactOp> {
    let mut ops = vec![
        idx_path(false, true, path),
        dup(0),
        idx_one(false, false, LIST_LENGTH),
        ImpactOp::constant(&Op::Addi { immediate: 1 }),
        push_array(true, &[LedgerElem::Null, LedgerElem::Null, LedgerElem::Null]),
        push_cell(false, &field_index_value(LIST_HEAD)),
    ];
    ops.extend(qualify_coin(list_coin_dup(path.len()), cm, coin));
    ops.extend([
        ImpactOp::constant(&Op::Ins { cached: true, n: 1 }),
        swap(0),
        push_cell(false, &field_index_value(LIST_LENGTH)),
        swap(0),
        ImpactOp::constant(&Op::Ins { cached: true, n: 1 }),
        swap(0),
        push_cell(false, &field_index_value(LIST_TAIL)),
        swap(0),
        insc(path.len() + 1),
    ]);
    ops
}

/// `list.popFront()` on field `index`: `idxp [field]; idx [1]; insc 1` — the
/// list becomes its own tail.
pub fn list_pop_front(index: u8) -> Vec<ImpactOp> {
    list_pop_front_at(&field_path(index))
}

/// [`list_pop_front`] on a general path.
pub fn list_pop_front_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        idx_one(false, false, LIST_TAIL),
        insc(path.len()),
    ]
}

/// Array positions inside a `List` node.
pub(crate) const LIST_HEAD: u8 = 0;
pub(crate) const LIST_TAIL: u8 = 1;
pub(crate) const LIST_LENGTH: u8 = 2;

/// Array positions inside a `MerkleTree` / `HistoricMerkleTree` node.
pub(crate) const TREE: u8 = 0;
pub(crate) const TREE_NEXT: u8 = 1;
pub(crate) const TREE_HISTORY: u8 = 2;

// --- MerkleTree: an `Array[2]` of `{tree, next index}` ----------------------

/// A `MerkleTree`'s initial value: `[blank tree of height DEPTH, cell 0u64]`.
fn empty_merkle_tree(depth: u8) -> [StateValue<InMemoryDB>; 2] {
    [
        StateValue::BoundedMerkleTree(VmMerkleTree::blank(depth)),
        StateValue::Cell(Sp::new(u64_aligned(0))),
    ]
}

/// A `MerkleTree`'s initial value as one `StateValue`
/// (midnight-ledger.ss:973): `[merkle-tree nat (), cell 0u64]`.
///
/// The constant `resetToDefault` writes AND the one an ADT-valued
/// `insertDefault` pushes — `VMstate-value-ADT` expands the declared
/// `(initial-value …)` in both cases, which is why there is one function
/// rather than two tables (see [`map_insert_adt_default_at`]).
pub fn empty_merkle_tree_value(depth: u8) -> StateValue<InMemoryDB> {
    StateValue::Array(empty_merkle_tree(depth).into_iter().collect())
}

/// A `HistoricMerkleTree`'s initial value (midnight-ledger.ss:1129):
/// [`empty_merkle_tree_value`] plus an empty history map.
///
/// NOTE the asymmetry with [`historic_merkle_tree_reset_at`], which pushes
/// this and then APPENDS the blank tree's root to the history; the declared
/// initial value itself has the history empty.
pub fn empty_historic_merkle_tree_value(depth: u8) -> StateValue<InMemoryDB> {
    let [tree, next] = empty_merkle_tree(depth);
    StateValue::Array([tree, next, empty_map()].into_iter().collect())
}

/// What [`historic_merkle_tree_reset_at`] LEAVES at its path: the declared
/// initial value ([`empty_historic_merkle_tree_value`]) with the blank
/// tree's root recorded in the history — the reset's `history_append`
/// (`idxp [2]; dup 2; idx [0]; root; pushs null; insc 2`), evaluated. The
/// root is the VM's own: `root` reads `MerkleTree::root` of the tree it
/// finds, and a blank tree has one.
///
/// compactc's generated `initialState` runs EVERY field's `resetToDefault`
/// (notes/ledger-abi.org "Initial state"), so this, and not the declared
/// value, is what a fresh HistoricMerkleTree field holds at deploy — the
/// deploy builder's contribution (minocrab-std `v3::state`), pinned against
/// compactc's JS in project 00002's T4b: `[tree, cell 0u64, {root → null}]`.
pub fn historic_merkle_tree_reset_value(depth: u8) -> StateValue<InMemoryDB> {
    let [tree, next] = empty_merkle_tree(depth);
    let StateValue::BoundedMerkleTree(ref blank) = tree else {
        unreachable!("empty_merkle_tree's first entry is the blank tree")
    };
    let root = blank
        .root()
        .expect("a blank tree has a root: the VM's `root` op reads it the same way");
    let history = StorageHashMap::new().insert(AlignedValue::from(root), StateValue::Null);
    StateValue::Array([tree, next, StateValue::Map(history)].into_iter().collect())
}

/// A `Cell` holding `stored` — one byte string per atom of `atoms`, in slot
/// order — AS THE LEDGER STORES IT: each atom in FAB normal form, its
/// trailing zero bytes dropped (`ValueAtom::normalize`), so a `Bytes<32>`
/// ending in NULs is kept shorter than 32 bytes and a reader pads it back.
///
/// The one Cell constructor of a DEPLOY state (minocrab-std `v3::state`):
/// a slot type's default (what compactc's generated `initialState` writes
/// with the field's `resetToDefault`) and a value a Compact constructor
/// would have written (a standard's magic, a sealed address) both come
/// through here, which is the same `newCell({ value: toValue(v),
/// alignment })` compactc's JS builds.
///
/// Panics when the two lists differ in length or a value does not fit its
/// atom: that is the caller's bug, not a state.
pub fn stored_cell(atoms: Vec<AlignmentAtom>, stored: Vec<Vec<u8>>) -> StateValue<InMemoryDB> {
    assert_eq!(
        atoms.len(),
        stored.len(),
        "stored_cell: {} stored atoms for alignment {atoms:?}",
        stored.len()
    );
    let value = Value(
        stored
            .into_iter()
            .map(|b| ValueAtom(b).normalize())
            .collect(),
    );
    let alignment = Alignment(atoms.iter().cloned().map(AlignmentSegment::Atom).collect());
    let aligned = AlignedValue::new(value, alignment)
        .unwrap_or_else(|| panic!("stored_cell: the value does not fit alignment {atoms:?}"));
    StateValue::Cell(Sp::new(aligned))
}

/// `mt.resetToDefault()` on field `index`.
pub fn merkle_tree_reset(index: u8, depth: u8) -> Vec<ImpactOp> {
    merkle_tree_reset_at(&field_path(index), depth)
}

/// [`merkle_tree_reset`] on a general path.
pub fn merkle_tree_reset_at(path: &[LedgerKey], depth: u8) -> Vec<ImpactOp> {
    reset_to_at(path, empty_merkle_tree_value(depth))
}

/// `mt.insert(item)` / `mt.insertHash(hash)` on field `index`
/// (midnight-ledger.ss MerkleTree `insert`): ONE stream for both, because the
/// two differ only in where the 32-byte leaf came from — `insert` hashes the
/// item (`rt-leaf-hash`, computed above this layer) and `insertHash` is
/// handed it. The fixture's `mtInsert` and `mtInsertHash` are identical
/// instruction for instruction.
///
/// ```text
/// idxp [field]; idxp [0]; dup 2; idx [1]      // the tree, then the next index
/// pushs (cell leaf); ins 1; insc 1            // tree[next] = leaf
/// idxp [1]; addi 1; insc 2                    // next += 1
/// ```
pub fn merkle_tree_insert(index: u8, leaf: &LedgerValue) -> Vec<ImpactOp> {
    merkle_tree_insert_at(&field_path(index), leaf)
}

/// [`merkle_tree_insert`] on a general path — the closing `insc` is
/// `len(f) + 1`; the two in the middle are literal 1s at every depth.
pub fn merkle_tree_insert_at(path: &[LedgerKey], leaf: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        idx_one(false, true, TREE),
        dup(2),
        idx_one(false, false, TREE_NEXT),
        push_cell(true, leaf),
        ins1(),
        ImpactOp::constant(&Op::Ins { cached: true, n: 1 }),
        idx_one(false, true, TREE_NEXT),
        ImpactOp::constant(&Op::Addi { immediate: 1 }),
        insc(path.len() + 1),
    ]
}

/// `mt.insertIndex(item, i)` / `insertHashIndex(hash, i)` /
/// `insertIndexDefault(i)` on field `index` — again ONE stream for all three,
/// which differ only in the leaf (the item's hash, the given hash, or the
/// DEFAULT value's hash).
///
/// The tail is `next = max(next, i + 1)`, and it is where the Impact-level
/// `branch`/`jmp` lives — transcript control flow, not circuit control flow
/// (notes/ledger-adts.org finding (b)):
///
/// ```text
/// idxp [field]; idxp [0]; push i; pushs (cell leaf); ins 2
/// idxp [1]; push i; addi 1; dup 1; dup 1; lt
/// branch 2; pop; jmp 2; swap 0; pop           // max(next, i + 1)
/// ins 1; insc 1
/// ```
pub fn merkle_tree_insert_index(
    index: u8,
    leaf: &LedgerValue,
    at: &LedgerValue,
) -> Vec<ImpactOp> {
    merkle_tree_insert_index_at(&field_path(index), leaf, at)
}

/// [`merkle_tree_insert_index`] on a general path.
pub fn merkle_tree_insert_index_at(
    path: &[LedgerKey],
    leaf: &LedgerValue,
    at: &LedgerValue,
) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        idx_one(false, true, TREE),
        push_cell(false, at),
        push_cell(true, leaf),
        ImpactOp::constant(&Op::Ins {
            cached: false,
            n: 2,
        }),
        idx_one(false, true, TREE_NEXT),
        push_cell(false, at),
        ImpactOp::constant(&Op::Addi { immediate: 1 }),
        dup(1),
        dup(1),
        ImpactOp::constant(&Op::Lt),
        ImpactOp::constant(&Op::Branch { skip: 2 }),
        ImpactOp::constant(&Op::Pop),
        ImpactOp::constant(&Op::Jmp { skip: 2 }),
        swap(0),
        ImpactOp::constant(&Op::Pop),
        ins1(),
        insc(path.len()),
    ]
}

// --- HistoricMerkleTree: the same, plus an `Array[2]` history map -----------

/// The history append every `HistoricMerkleTree` mutation ends with: descend
/// to position 2 and insert the tree's NEW root as a key with a `Null` value.
///
/// The two closing `ins` are the caller's, because the mutations and
/// `resetToDefault` close in OPPOSITE ORDERS: an insert ends `ins 1; insc 2`,
/// a reset `insc 2; ins 1` (midnight-ledger.ss:1183-1190 against :1211-1228).
/// A shared "closing" argument would have hidden that.
fn history_append() -> Vec<ImpactOp> {
    vec![
        idx_one(false, true, TREE_HISTORY),
        dup(2),
        idx_one(false, false, TREE),
        ImpactOp::constant(&Op::Root),
        ImpactOp::constant(&Op::Push {
            storage: true,
            value: StateValue::Null,
        }),
    ]
}

/// `hmt.insert(item)` / `hmt.insertHash(hash)` — [`merkle_tree_insert`] with
/// the history append spliced in, and the `insc 2` that closed it demoted to
/// `insc 1` because the append now closes the operation.
pub fn historic_merkle_tree_insert(index: u8, leaf: &LedgerValue) -> Vec<ImpactOp> {
    historic_merkle_tree_insert_at(&field_path(index), leaf)
}

/// [`historic_merkle_tree_insert`] on a general path. The `insc` the plain
/// tree closed with is demoted to a LITERAL 1 (midnight-ledger.ss:1222) at
/// every depth; only the new closing `insc` tracks `len(f) + 1`.
pub fn historic_merkle_tree_insert_at(path: &[LedgerKey], leaf: &LedgerValue) -> Vec<ImpactOp> {
    let mut ops = merkle_tree_insert_at(path, leaf);
    let last = ops.len() - 1;
    ops[last] = ImpactOp::constant(&Op::Ins { cached: true, n: 1 });
    ops.extend(history_append());
    ops.push(ins1());
    ops.push(insc(path.len() + 1));
    ops
}

/// `hmt.insertIndex(..)` / `insertHashIndex(..)` / `insertIndexDefault(i)` —
/// [`merkle_tree_insert_index`] with the history append replacing its closing
/// `insc 1`.
pub fn historic_merkle_tree_insert_index(
    index: u8,
    leaf: &LedgerValue,
    at: &LedgerValue,
) -> Vec<ImpactOp> {
    historic_merkle_tree_insert_index_at(&field_path(index), leaf, at)
}

/// [`historic_merkle_tree_insert_index`] on a general path.
pub fn historic_merkle_tree_insert_index_at(
    path: &[LedgerKey],
    leaf: &LedgerValue,
    at: &LedgerValue,
) -> Vec<ImpactOp> {
    let mut ops = merkle_tree_insert_index_at(path, leaf, at);
    ops.pop();
    ops.extend(history_append());
    ops.push(ins1());
    ops.push(insc(path.len() + 1));
    ops
}

/// `hmt.resetHistory()` on field `index` (midnight-ledger.ss
/// HistoricMerkleTree `resetHistory`): replace the history with a one-entry
/// map holding the CURRENT root.
pub fn historic_merkle_tree_reset_history(index: u8) -> Vec<ImpactOp> {
    historic_merkle_tree_reset_history_at(&field_path(index))
}

/// [`historic_merkle_tree_reset_history`] on a general path — the ONE
/// operation whose closing depth is `len(f) + 2` (midnight-ledger.ss:1338).
pub fn historic_merkle_tree_reset_history_at(path: &[LedgerKey]) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, &field_index_value(TREE_HISTORY)),
        ImpactOp::constant(&Op::Push {
            storage: true,
            value: empty_map(),
        }),
        dup(2),
        idx_one(false, false, TREE),
        ImpactOp::constant(&Op::Root),
        ImpactOp::constant(&Op::Push {
            storage: true,
            value: StateValue::Null,
        }),
        insc(path.len() + 2),
    ]
}

/// `hmt.resetToDefault()` on field `index` — the ONE `resetToDefault` that is
/// not three instructions, because the fresh history has to be seeded with
/// the blank tree's root.
pub fn historic_merkle_tree_reset(index: u8, depth: u8) -> Vec<ImpactOp> {
    historic_merkle_tree_reset_at(&field_path(index), depth)
}

/// [`historic_merkle_tree_reset`] on a general path — the ninth and last of
/// the whole-field-replace ops, and the one that open-codes the suppression
/// rather than going through `reset_to_at` because its closing pair is
/// `insc 2; ins 1` where every other reset's is `ins 1; insc len(f)-1`.
pub fn historic_merkle_tree_reset_at(path: &[LedgerKey], depth: u8) -> Vec<ImpactOp> {
    let initial = empty_historic_merkle_tree_value(depth);
    let mut ops = idxp_container(path);
    ops.push(path[path.len() - 1].push_as_cell());
    ops.push(ImpactOp::constant(&Op::Push {
        storage: true,
        value: initial,
    }));
    ops.extend(history_append());
    ops.push(ImpactOp::constant(&Op::Ins { cached: true, n: 2 }));
    ops.push(ins1());
    ops.extend(insc_container(path));
    ops
}

// --- events -----------------------------------------------------------------

/// `emit <event>` (compiler/analysis-passes/lower-emit.ss:20-27): push the
/// MIP-0002 wrapper `Array[Cell(version: u32 as bytes<4>), Cell(tag:
/// bytes<1>), Cell(payload)]`, then the VM `log` op. `payload` is the
/// serialized event value (a single `bytes<n>` atom for the declared
/// event size).
pub fn emit_event(version: u32, tag: u8, payload: &LedgerValue) -> Vec<ImpactOp> {
    let mut elems = vec![
        ImpactElem::Imm(Fr::from(0x10u64)), // push, storage = false
        ImpactElem::Imm(Fr::from(3u64 | (3 << 4))), // StateValue::Array(3) tag
        // Cell(version as bytes<4>)
        ImpactElem::Imm(Fr::from(1u64)),
        ImpactElem::Imm(Fr::from(1u64)),
        ImpactElem::Imm(Fr::from(4u64)),
        ImpactElem::Imm(Fr::from(u64::from(version))),
        // Cell(tag as bytes<1>)
        ImpactElem::Imm(Fr::from(1u64)),
        ImpactElem::Imm(Fr::from(1u64)),
        ImpactElem::Imm(Fr::from(1u64)),
        ImpactElem::Imm(Fr::from(u64::from(tag))),
        // Cell(payload)
        ImpactElem::Imm(Fr::from(1u64)),
    ];
    elems.extend(alignment_header(&payload.atoms));
    elems.extend(payload.elems.iter().copied());
    vec![ImpactOp(elems), ImpactOp::constant(&Op::Log)]
}

// --- BLIND OPS (M40, notes/stream-design.org) --------------------------------
//
// A ledger op that fetches a cell and stores or combines it WITHOUT a
// `popeq` never goes stale: the chain executes it at inclusion against
// whatever the cell holds then, and the circuit embeds no public input for
// it. `Counter.increment` (`idxp; addi; insc`) is the one such op Compact
// has. These are the rest of the family the on-chain VM can express with
// its real op set (Lt Neg And Or Add Branch Jmp Dup Swap Pop Idx Ins): a
// blind SNAPSHOT of a cell into a map entry, and a blind COMBINE of a cell
// with a public constant under add, max, min, and, or, and first-write.
//
// None of these is expressible in Compact, so there is no compactc
// differential; the gate is the on-chain VM itself
// (minocrab-std/tests/v3_blind.rs runs every transcript through
// `midnight_onchain_vm::vm::run_program` on a seeded state).
//
// Stack discipline, from onchain-vm `vm.rs`: `idxp f` leaves the `(container,
// key)` pairs of the walk and then the value, so after `idxp f` the state
// sits `2·len(f) − 1` below the top; `ins n` pops the value then `n` pairs;
// `lt` pops `b` then `a` and pushes `a < b`; `branch k` pops a Boolean cell
// and skips `k` ops when it is TRUE; `dup n` copies the element `n` below the
// top; `swap n` exchanges the top with the element `n + 1` below it. A value
// pushed with `push` (storage = false) is WEAK and the runtime refuses to
// persist it, so a constant that may be WRITTEN goes in with `pushs`.

/// The blind SNAPSHOT: `map[key] = cell`, the circuit never learning the
/// value. `idxp m; push key; dup 2·len(m)+1; idx c; ins 1; insc len(m)`.
///
/// The `dup` is `Map.insertCoin`'s reach-back (midnight-ledger.ss:769-795):
/// after `idxp m; push key` the state is `2·len(m) + 1` below the top, so a
/// copy of it, indexed by the cell's path, is the value the insert takes.
/// The value an `idx` fetches is as strong as the state it came from, so it
/// persists (the compactc `StampedCounter.stamp` port learned this the hard
/// way — notes/stream-design.org, "as built").
pub fn cell_snapshot_into_map_at(
    cell: &[LedgerKey],
    map: &[LedgerKey],
    key: &LedgerValue,
) -> Vec<ImpactOp> {
    let reach = 2 * map.len() + 1;
    assert!(
        reach <= 15,
        "cell_snapshot_into_map_at: a map path of {} elements puts the state \
         {reach} deep, past the `dup` nibble",
        map.len()
    );
    vec![
        idx_path(false, true, map),
        push_cell(false, key),
        dup(reach as u8),
        idx_path(false, false, cell),
        ins1(),
        insc(map.len()),
    ]
}

/// The blind CELL-TO-CELL COPY: `dst = src`, the circuit never learning the
/// value: `idxp dst[..len-1]; push dst[len-1]; dup 2·len(dst)−1; idx src;
/// ins 1; insc len(dst)−1` — [`cell_write_at`] with its `pushs value`
/// replaced by the reach-back of [`cell_snapshot_into_map_at`]. After the
/// container walk and the key push the state sits `2·len(dst) − 1` below
/// the top (one pair per walked element, then the key), so a copy of it
/// indexed by `src` is the value the insert takes.
pub fn cell_copy_at(src: &[LedgerKey], dst: &[LedgerKey]) -> Vec<ImpactOp> {
    let reach = 2 * dst.len() - 1;
    assert!(
        reach <= 15,
        "cell_copy_at: a destination path of {} elements puts the state {reach} deep, \
         past the `dup` nibble",
        dst.len()
    );
    let mut ops = idxp_container(dst);
    ops.push(dst[dst.len() - 1].push_as_cell());
    ops.push(dup(reach as u8));
    ops.push(idx_path(false, false, src));
    ops.push(ins1());
    ops.extend(insc_container(dst));
    ops
}

/// The blind MOVE of a map entry: `map[to] = map[from]; map.remove(from)`,
/// the circuit never learning the value, and an ABSENT `from` failing the
/// transaction:
///
/// ```text
/// idxp m; push to; dup 2·len(m)+1; idx m ++ [from];
/// dup 0; type; push 0; swap 0; sub; pop;
/// ins 1; insc len(m); <map_remove_at m from>
/// ```
///
/// `idx` of a missing map key yields `Null` rather than failing (`vm.rs`
/// `idx`: `unwrap_or(StateValue::Null)`), and `ins` would store that
/// `Null` under `to`. The six middle ops are the presence check: `type`
/// pushes `0` for a cell and `1` for `Null`, and `0 − type` is a checked
/// subtraction that underflows — fails the transaction — exactly when the
/// entry was absent. Six ops rather than a second `member` walk, and total
/// over every entry type (a `lt`/`eq` probe would decode the value).
pub fn map_move_entry_at(map: &[LedgerKey], from: &LedgerValue, to: &LedgerValue) -> Vec<ImpactOp> {
    let reach = 2 * map.len() + 1;
    assert!(
        reach <= 15,
        "map_move_entry_at: a map path of {} elements puts the state {reach} deep, past \
         the `dup` nibble",
        map.len()
    );
    let zero = LedgerValue::bytes(1, vec![ImpactElem::Imm(Fr::from(0u64))]);
    let mut entry: Vec<LedgerKey> = map.to_vec();
    entry.push(LedgerKey::Value(from.clone()));
    let mut ops = vec![
        idx_path(false, true, map),
        push_cell(false, to),
        dup(reach as u8),
        idx_path(false, false, &entry),
        dup(0),
        type_of(),
        push_cell(false, &zero),
        swap(0),
        ImpactOp::constant(&Op::Sub),
        pop(),
        ins1(),
        insc(map.len()),
    ];
    ops.extend(map_remove_at(map, from));
    ops
}

/// The blind ADD: `cell = cell + delta` on a `Uint<64>` cell, `delta` a
/// public circuit value: `idxp f; push delta; add; insc len(f)`.
///
/// `Counter.increment`'s `addi` takes a LITERAL (an op immediate); a delta
/// the circuit computes goes through `push` + `add`, one op more. Both
/// overflow-check on chain (`vm.rs` `add`: `checked_add`, the transaction
/// fails), and neither embeds a public input.
pub fn cell_add_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, delta),
        ImpactOp::constant(&Op::Add),
        insc(path.len()),
    ]
}

/// The blind SUB: `cell = cell − delta` on a `Uint<64>` cell:
/// `idxp f; push delta; sub; insc len(f)`. `sub` pops Δ then the cell and
/// leaves `cell − Δ` (`vm.rs`: `sub(&b, a)` with `a` the top), and it is
/// `checked_sub`, so an underflow fails the transaction.
pub fn cell_sub_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, delta),
        ImpactOp::constant(&Op::Sub),
        insc(path.len()),
    ]
}

/// The blind MAX: `cell = max(cell, delta)` on a `Uint<64>` cell, the
/// kernel-mint / compactc `Counter.raiseTo` pattern:
///
/// ```text
/// idxp f; pushs Δ; dup 1; dup 1; lt; neg; branch 3; swap 0; pop; jmp 1; pop; insc len(f)
/// ```
///
/// With `[cur, Δ]` on the stack, `lt` leaves `cur < Δ`, `neg` inverts it,
/// and `branch 3` skips the Δ-wins arm (`swap 0; pop; jmp 1`, leaving `Δ`)
/// when the current value is at least Δ, landing on the cur-wins arm
/// (`pop`, leaving `cur`). The `jmp 1` is what makes the two arms exclusive;
/// a `branch 2` without it would write Δ on both paths. Δ is `pushs` because
/// on its winning path it is what gets persisted.
pub fn cell_max_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    cell_extremum_at(path, delta, true)
}

/// The blind MIN: [`cell_max_at`] without the `neg`, so the Δ-wins arm runs
/// when `cur < Δ` is FALSE, i.e. when Δ is the smaller.
pub fn cell_min_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    cell_extremum_at(path, delta, false)
}

fn cell_extremum_at(path: &[LedgerKey], delta: &LedgerValue, max: bool) -> Vec<ImpactOp> {
    let mut ops = vec![
        idx_path(false, true, path),
        push_cell(true, delta),
        dup(1),
        dup(1),
        ImpactOp::constant(&Op::Lt),
    ];
    if max {
        ops.push(ImpactOp::constant(&Op::Neg));
    }
    ops.extend([
        ImpactOp::constant(&Op::Branch { skip: 3 }),
        ImpactOp::constant(&Op::Swap { n: 0 }),
        ImpactOp::constant(&Op::Pop),
        ImpactOp::constant(&Op::Jmp { skip: 1 }),
        ImpactOp::constant(&Op::Pop),
        insc(path.len()),
    ]);
    ops
}

/// The blind AND: `cell = cell && delta` on a `Boolean` cell:
/// `idxp f; push delta; and; insc len(f)`.
pub fn cell_and_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    cell_boolean_at(path, delta, Op::And)
}

/// The blind OR: `cell = cell || delta` on a `Boolean` cell:
/// `idxp f; push delta; or; insc len(f)`.
pub fn cell_or_at(path: &[LedgerKey], delta: &LedgerValue) -> Vec<ImpactOp> {
    cell_boolean_at(path, delta, Op::Or)
}

fn cell_boolean_at(path: &[LedgerKey], delta: &LedgerValue, op: VmOp) -> Vec<ImpactOp> {
    vec![
        idx_path(false, true, path),
        push_cell(false, delta),
        ImpactOp::constant(&op),
        insc(path.len()),
    ]
}

/// The blind FIRST-WRITE: `if !flag { value_cell = value; flag = true }`,
/// the two-cell layout of a `First` accumulator:
///
/// ```text
/// dup 0; idx flag; branch k; <cell_write_at value>; <cell_write_at flag = true>
/// ```
///
/// `branch k` pops the flag and skips both writes (`k` ops) when it is
/// already set. Either write is [`cell_write_at`]'s three or five
/// instructions, so `k` is their sum and is computed, not assumed.
pub fn cell_write_first_at(
    value_path: &[LedgerKey],
    flag_path: &[LedgerKey],
    value: &LedgerValue,
) -> Vec<ImpactOp> {
    let set = LedgerValue::bytes(1, vec![ImpactElem::Imm(Fr::from(1u64))]);
    let write_value = cell_write_at(value_path, value);
    let write_flag = cell_write_at(flag_path, &set);
    let skip = write_value.len() + write_flag.len();
    assert!(skip <= u32::MAX as usize, "branch skip fits a u32");
    let mut ops = vec![
        dup(0),
        idx_path(false, false, flag_path),
        ImpactOp::constant(&Op::Branch { skip: skip as u32 }),
    ];
    ops.extend(write_value);
    ops.extend(write_flag);
    ops
}

// --- the branch-and-compare ops the hooks compose ---------------------------
//
// `minocrab_std::v3::hook` builds `if_absent` / `if_below` / `if_unset` out
// of these and the writes above; they are named here so the stdlib never
// spells an opcode itself and the encoding stays `Op::field_repr`'s.

/// `branch k`: pop a Boolean cell, skip the next `k` instructions when it
/// is TRUE.
pub fn branch(skip: u32) -> ImpactOp {
    ImpactOp::constant(&Op::Branch { skip })
}

/// `jmp k`: skip the next `k` instructions.
pub fn jmp(skip: u32) -> ImpactOp {
    ImpactOp::constant(&Op::Jmp { skip })
}

/// `member`: pop a key then a map, push whether the map holds the key.
pub fn member() -> ImpactOp {
    ImpactOp::constant(&Op::Member)
}

/// `lt`: pop `b` then `a` (both `Uint<64>` cells), push `a < b`.
pub fn lt() -> ImpactOp {
    ImpactOp::constant(&Op::Lt)
}

/// `neg`: pop a Boolean cell, push its negation.
pub fn neg() -> ImpactOp {
    ImpactOp::constant(&Op::Neg)
}

/// `pop`: discard the top of the stack.
pub fn pop() -> ImpactOp {
    ImpactOp::constant(&Op::Pop)
}

/// `type`: pop a value, push its kind as a `bytes<1>` cell — `0` for a
/// cell, `1` for `Null`, `2` for a map (`vm.rs`).
pub fn type_of() -> ImpactOp {
    ImpactOp::constant(&Op::Type)
}
