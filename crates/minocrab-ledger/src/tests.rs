//! Tests for the ledger op layer, covering the encodings in `impact`, `ops`,
//! `reads` and `kernel` against the real `Op::field_repr`.

use midnight_base_crypto::fab::{
    Alignment, AlignmentAtom, AlignmentSegment, AlignedValue, Value, ValueAtom,
};
use midnight_onchain_state::state::StateValue;
use midnight_onchain_vm::ops::{Key, Op};
use midnight_storage::arena::Sp;
use midnight_transient_crypto::repr::FieldRepr;
use minocrab::v3::ImpactElem;
use minocrab::Fr;

use crate::impact::*;
use crate::kernel::*;
use crate::ops::*;
use crate::reads::*;

fn imms(op: &ImpactOp) -> Vec<Fr> {
    op.0.iter()
        .map(|e| match e {
            ImpactElem::Imm(f) => *f,
            ImpactElem::Wire(_) => panic!("expected constant"),
        })
        .collect()
}

fn repr(op: &VmOp) -> Vec<Fr> {
    let mut out = Vec::new();
    op.field_repr(&mut out);
    out
}

/// Our hand-laid push/popeq headers must match the real Op encodings.
#[test]
fn mixed_op_layout_matches_field_repr() {
    // push Cell{bytes<16>, 5}:
    let av = AlignedValue::new(
        Value(vec![ValueAtom(5u128.to_le_bytes().to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 16,
        })]),
    )
    .unwrap();
    let real = repr(&Op::Push {
        storage: true,
        value: midnight_onchain_state::state::StateValue::Cell(Sp::new(av.clone())),
    });
    let ours = imms(&push_cell(
        true,
        &LedgerValue::bytes(16, vec![ImpactElem::Imm(Fr::from(5u64))]),
    ));
    assert_eq!(ours, real);

    // popeqc expecting a bytes<32> value [hi=1, lo=2]:
    let mut bytes = [0u8; 32];
    bytes[0] = 2; // lo limb LE
    bytes[31] = 1; // hi byte
    let av = AlignedValue::new(
        Value(vec![ValueAtom(bytes.to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 32,
        })]),
    )
    .unwrap();
    let real = repr(&Op::Popeq {
        cached: true,
        result: av,
    });
    let ours = imms(&popeq(
        true,
        &LedgerValue::bytes(
            32,
            vec![
                ImpactElem::Imm(Fr::from(1u64)), // hi
                ImpactElem::Imm(Fr::from(2u64)), // lo
            ],
        ),
    ));
    assert_eq!(ours, real);
}

/// [`push_array`] is the one hand-laid `StateValue` encoder (the mixed
/// push `List.pushFront` needs), so its constant case must agree with
/// `StateValue::field_repr` element for element — tags, nesting and the
/// `3 | len << 4` packing.
#[test]
fn push_array_matches_field_repr() {
    let cell = u64_aligned(7);
    let real = repr(&Op::Push {
        storage: true,
        value: StateValue::Array(
            [
                StateValue::Cell(Sp::new(cell.clone())),
                StateValue::Null,
                StateValue::Null,
            ]
            .into(),
        ),
    });
    let ours = imms(&push_array(
        true,
        &[
            LedgerElem::Cell(LedgerValue::bytes(
                8,
                vec![ImpactElem::Imm(Fr::from(7u64))],
            )),
            LedgerElem::Null,
            LedgerElem::Null,
        ],
    ));
    assert_eq!(ours, real);
}

/// `rt-max-sizeof` against the value compactc actually emitted: the
/// fixture's `listHead` over a `Bytes<32>` element is `concat 0x27`, and
/// that immediate is `2 + max_sizeof`.
#[test]
fn max_sizeof_matches_compactc() {
    assert_eq!(2 + max_sizeof(&[AlignmentAtom::Bytes { length: 32 }]), 0x27);
    assert_eq!(max_sizeof(&[]), 2);
}

/// The worked example's constant streams (notes/ledger-abi.org §5).
#[test]
fn counter_increment_matches_annotated_golden() {
    let ops = counter_increment(0, 1);
    assert_eq!(imms(&ops[0]), vec![Fr::from(0x70u64), 1u64.into(), 1u64.into(), 0u64.into()]);
    assert_eq!(imms(&ops[1]), vec![Fr::from(0x0eu64), 1u64.into()]);
    assert_eq!(imms(&ops[2]), vec![Fr::from(0xa1u64)]);
}

/// `idx_key` with constant limbs must match the real Op encoding of the
/// same single-value-key idx.
#[test]
fn idx_key_matches_field_repr() {
    let mut bytes = [0u8; 32];
    bytes[0] = 0x2a;
    bytes[31] = 0x01;
    let av = AlignedValue::new(
        Value(vec![ValueAtom(bytes.to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 32,
        })]),
    )
    .unwrap();
    let real = repr(&Op::Idx {
        cached: false,
        push_path: false,
        path: vec![Key::Value(av)].into(),
    });
    let ours = imms(&idx_key(&LedgerValue::bytes(
        32,
        vec![
            ImpactElem::Imm(Fr::from(1u64)),                  // hi = byte 31
            ImpactElem::Imm(Fr::from(0x2au64)),               // lo = bytes 0..30
        ],
    )));
    assert_eq!(ours, real);
}

/// `emit_event` with a constant payload must match the real
/// `Op::Push` of the MIP-0002 wrapper Array followed by `Op::Log`.
#[test]
fn emit_event_matches_field_repr() {
    use midnight_onchain_state::state::StateValue;

    let payload_bytes: Vec<u8> = (1u8..=40).collect();
    let payload_av = AlignedValue::new(
        Value(vec![ValueAtom(payload_bytes.clone()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 40,
        })]),
    )
    .unwrap();
    let version_av = AlignedValue::new(
        Value(vec![ValueAtom(1u32.to_le_bytes().to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 4,
        })]),
    )
    .unwrap();
    let real_push = Op::Push {
        storage: false,
        value: StateValue::Array(
            vec![
                StateValue::Cell(Sp::new(version_av)),
                StateValue::Cell(Sp::new(field_key(10))),
                StateValue::Cell(Sp::new(payload_av)),
            ]
            .into(),
        ),
    };

    // 40 bytes = 2 limbs: [leftover 9 bytes = bytes 31..39, bytes 0..30].
    let hi = Fr::from_le_bytes(&(32u8..=40).collect::<Vec<_>>()).unwrap();
    let lo = Fr::from_le_bytes(&(1u8..=31).collect::<Vec<_>>()).unwrap();
    let payload = LedgerValue::bytes(40, vec![ImpactElem::Imm(hi), ImpactElem::Imm(lo)]);
    let ours = emit_event(1, 10, &payload);
    assert_eq!(imms(&ours[0]), repr(&real_push));
    assert_eq!(imms(&ours[1]), repr(&Op::Log));
}

/// `kernel_claim_contract_call`'s constant ops and mixed push header
/// against real Op encodings and the callOnce.zkir annotated stream:
/// swap = 0x40, idxpc effects\[3\] = [0x80,1,1,3], dup 0 = 0x30,
/// size = 0x04, push cell = [0x10, 1, 3, 0x20, 0x20, −2, limbs…],
/// concatc 160 = [0x17, 0xa0], push null = [0x10, 0x00], insc 2 = 0xa2.
#[test]
fn claim_contract_call_matches_field_repr() {
    use midnight_onchain_state::state::StateValue;

    let mut addr = [0u8; 32];
    addr[0] = 0xaa;
    addr[31] = 0x01;
    let mut ep = [0u8; 32];
    ep[0] = 0xbb;
    ep[31] = 0x02;
    let comm = Fr::from(0x1234u64);

    // The real rt-aligned-concat'd 3-atom cell.
    let comm_bytes: Vec<u8> = {
        let mut le = comm.as_le_bytes();
        while le.last() == Some(&0) {
            le.pop();
        }
        le
    };
    let av = AlignedValue::new(
        Value(vec![
            ValueAtom(addr.to_vec()).normalize(),
            ValueAtom(ep.to_vec()).normalize(),
            ValueAtom(comm_bytes).normalize(),
        ]),
        Alignment(vec![
            AlignmentSegment::Atom(AlignmentAtom::Bytes { length: 32 }),
            AlignmentSegment::Atom(AlignmentAtom::Bytes { length: 32 }),
            AlignmentSegment::Atom(AlignmentAtom::Field),
        ]),
    )
    .unwrap();

    let value = LedgerValue::new(
        vec![
            AlignmentAtom::Bytes { length: 32 },
            AlignmentAtom::Bytes { length: 32 },
            AlignmentAtom::Field,
        ],
        vec![
            ImpactElem::Imm(Fr::from(u64::from(addr[31]))),
            ImpactElem::Imm(Fr::from_le_bytes(&addr[..31]).unwrap()),
            ImpactElem::Imm(Fr::from(u64::from(ep[31]))),
            ImpactElem::Imm(Fr::from_le_bytes(&ep[..31]).unwrap()),
            ImpactElem::Imm(comm),
        ],
    );
    let ours = kernel_claim_contract_call(&value);

    let real: Vec<VmOp> = vec![
        Op::Swap { n: 0 },
        Op::Idx {
            cached: true,
            push_path: true,
            path: vec![Key::Value(field_key(3))].into(),
        },
        Op::Dup { n: 0 },
        Op::Size,
        Op::Push {
            storage: false,
            value: midnight_onchain_state::state::StateValue::Cell(Sp::new(av)),
        },
        Op::Concat {
            cached: true,
            n: 160,
        },
        Op::Push {
            storage: false,
            value: StateValue::Null,
        },
        Op::Ins { cached: true, n: 2 },
        Op::Swap { n: 0 },
    ];
    assert_eq!(ours.len(), real.len());
    for (op, real_op) in ours.iter().zip(&real) {
        assert_eq!(imms(op), repr(real_op));
    }
    // The annotated corpus bytes for the constant ops.
    assert_eq!(imms(&ours[1]), vec![Fr::from(0x80u64), 1u64.into(), 1u64.into(), 3u64.into()]);
    assert_eq!(imms(&ours[3]), vec![Fr::from(0x04u64)]);
    assert_eq!(imms(&ours[5]), vec![Fr::from(0x17u64), Fr::from(0xa0u64)]);
    assert_eq!(imms(&ours[6]), vec![Fr::from(0x10u64), Fr::from(0u64)]);
    assert_eq!(imms(&ours[7]), vec![Fr::from(0xa2u64)]);
}

/// `map_remove` against real Op encodings and the claim.zkir annotated
/// stream (:287-291): idxp = [0x70, 1, 1, 0], rem = 0x19, insc 1 = 0xa1.
#[test]
fn map_remove_matches_field_repr() {
    let key = LedgerValue::bytes(
        32,
        vec![ImpactElem::Imm(Fr::from(1u64)), ImpactElem::Imm(Fr::from(2u64))],
    );
    let ops = map_remove(0, &key);
    assert_eq!(ops.len(), 4);
    assert_eq!(
        imms(&ops[0]),
        vec![Fr::from(0x70u64), 1u64.into(), 1u64.into(), 0u64.into()]
    );
    assert_eq!(imms(&ops[2]), repr(&Op::Rem { cached: false }));
    assert_eq!(imms(&ops[2]), vec![Fr::from(0x19u64)]);
    assert_eq!(imms(&ops[3]), vec![Fr::from(0xa1u64)]);
}

/// `cell_write_coin` against real Op encodings and the notify.zkir
/// annotated stream: push field key = [0x10, 1, 1, 1, 0], dup 3 =
/// 0x33, idxc [1, stack] = [0x61, 1, 1, 1, −1] (opcode = 0x60 |
/// (path_len − 1), Key::Stack = −1), concatc 91 = [0x17, 0x5b],
/// ins 1 = 0x91.
#[test]
fn cell_write_coin_matches_field_repr() {
    let cm = LedgerValue::bytes(
        32,
        vec![ImpactElem::Imm(Fr::from(3u64)), ImpactElem::Imm(Fr::from(4u64))],
    );
    let coin = LedgerValue::new(
        vec![
            AlignmentAtom::Bytes { length: 32 },
            AlignmentAtom::Bytes { length: 32 },
            AlignmentAtom::Bytes { length: 16 },
        ],
        vec![
            ImpactElem::Imm(Fr::from(5u64)),
            ImpactElem::Imm(Fr::from(6u64)),
            ImpactElem::Imm(Fr::from(7u64)),
            ImpactElem::Imm(Fr::from(8u64)),
            ImpactElem::Imm(Fr::from(9u64)),
        ],
    );
    let ops = cell_write_coin(0, &cm, &coin);
    assert_eq!(ops.len(), 8);
    assert_eq!(
        imms(&ops[0]),
        vec![Fr::from(0x10u64), 1u64.into(), 1u64.into(), 1u64.into(), 0u64.into()]
    );
    assert_eq!(imms(&ops[1]), vec![Fr::from(0x33u64)]);
    assert_eq!(
        imms(&ops[3]),
        repr(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Value(field_key(1)), Key::Stack].into(),
        })
    );
    assert_eq!(
        imms(&ops[3]),
        vec![
            Fr::from(0x61u64),
            1u64.into(),
            1u64.into(),
            1u64.into(),
            Fr::from(0u64) - Fr::from(1u64),
        ]
    );
    // push coin: [0x10, Cell tag, 3 atoms, 0x20, 0x20, 0x10, limbs…]
    assert_eq!(
        imms(&ops[4])[..6],
        [
            Fr::from(0x10u64),
            1u64.into(),
            3u64.into(),
            0x20u64.into(),
            0x20u64.into(),
            0x10u64.into(),
        ]
    );
    assert_eq!(imms(&ops[5]), repr(&Op::Swap { n: 0 }));
    assert_eq!(imms(&ops[6]), vec![Fr::from(0x17u64), Fr::from(0x5bu64)]);
    assert_eq!(imms(&ops[7]), vec![Fr::from(0x91u64)]);
}

/// A `bytes<32>` commitment and a 3-atom `ShieldedCoinInfo`, the two
/// operands every coin arm takes.
fn coin_operands() -> (LedgerValue, LedgerValue) {
    (
        LedgerValue::bytes(
            32,
            vec![ImpactElem::Imm(Fr::from(3u64)), ImpactElem::Imm(Fr::from(4u64))],
        ),
        LedgerValue::new(
            vec![
                AlignmentAtom::Bytes { length: 32 },
                AlignmentAtom::Bytes { length: 32 },
                AlignmentAtom::Bytes { length: 16 },
            ],
            (5u64..10).map(|n| ImpactElem::Imm(Fr::from(n))).collect(),
        ),
    )
}

/// The six shared instructions, in the encodings all four arms embed:
/// dup `n` = 0x30 | n, push cm, idxc [(1), stack] = [0x61, 1, 1, 1, −1],
/// push coin (three atoms: 0x20, 0x20, 0x10), swap 0, concatc 91 =
/// [0x17, 0x5b].
fn assert_qualify_dance(ops: &[ImpactOp], dup_n: u64) {
    assert_eq!(imms(&ops[0]), repr(&Op::Dup { n: dup_n as u8 }));
    assert_eq!(imms(&ops[0]), vec![Fr::from(0x30u64 + dup_n)]);
    assert_eq!(
        imms(&ops[1])[..4],
        [Fr::from(0x10u64), 1u64.into(), 1u64.into(), 0x20u64.into()]
    );
    assert_eq!(
        imms(&ops[2]),
        repr(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Value(field_key(1)), Key::Stack].into(),
        })
    );
    assert_eq!(
        imms(&ops[2]),
        vec![
            Fr::from(0x61u64),
            1u64.into(),
            1u64.into(),
            1u64.into(),
            Fr::from(0u64) - Fr::from(1u64),
        ]
    );
    assert_eq!(
        imms(&ops[3])[..6],
        [
            Fr::from(0x10u64),
            1u64.into(),
            3u64.into(),
            0x20u64.into(),
            0x20u64.into(),
            0x10u64.into(),
        ]
    );
    assert_eq!(imms(&ops[4]), repr(&Op::Swap { n: 0 }));
    assert_eq!(imms(&ops[5]), vec![Fr::from(0x17u64), Fr::from(0x5bu64)]);
}

/// `set_insert_coin` against real Op encodings and the fixture's
/// `setInsertCoin.zkir`: `idxp [field]` then the dance at `dup 4`
/// (0x34), then `pushs null` (0x11 0x00), `ins 1` (0x91), `insc 1`
/// (0xa1) — `set_insert`'s tail with the element push replaced.
#[test]
fn set_insert_coin_matches_field_repr() {
    use midnight_onchain_state::state::StateValue;

    let (cm, coin) = coin_operands();
    let ops = set_insert_coin(0, &cm, &coin);
    assert_eq!(ops.len(), 10);
    assert_eq!(
        imms(&ops[0]),
        vec![Fr::from(0x70u64), 1u64.into(), 1u64.into(), 0u64.into()]
    );
    assert_qualify_dance(&ops[1..7], 4);
    assert_eq!(
        imms(&ops[7]),
        repr(&Op::Push {
            storage: true,
            value: StateValue::Null,
        })
    );
    assert_eq!(imms(&ops[7]), vec![Fr::from(0x11u64), Fr::from(0u64)]);
    assert_eq!(imms(&ops[8]), vec![Fr::from(0x91u64)]);
    assert_eq!(imms(&ops[9]), vec![Fr::from(0xa1u64)]);
}

/// `map_insert_coin` against real Op encodings and the fixture's
/// `mapInsertCoin.zkir`: the KEY push comes before the dance, which is
/// why the reach is `dup 5` (0x35) and not the `Set`'s 4.
#[test]
fn map_insert_coin_matches_field_repr() {
    let (cm, coin) = coin_operands();
    let key = LedgerValue::bytes(
        32,
        vec![ImpactElem::Imm(Fr::from(1u64)), ImpactElem::Imm(Fr::from(2u64))],
    );
    let ops = map_insert_coin(1, &key, &cm, &coin);
    assert_eq!(ops.len(), 10);
    assert_eq!(
        imms(&ops[0]),
        vec![Fr::from(0x70u64), 1u64.into(), 1u64.into(), 1u64.into()]
    );
    assert_eq!(
        imms(&ops[1]),
        vec![
            Fr::from(0x10u64),
            1u64.into(),
            1u64.into(),
            0x20u64.into(),
            1u64.into(),
            2u64.into(),
        ]
    );
    assert_qualify_dance(&ops[2..8], 5);
    assert_eq!(imms(&ops[8]), vec![Fr::from(0x91u64)]);
    assert_eq!(imms(&ops[9]), vec![Fr::from(0xa1u64)]);
}

/// `list_push_front_coin` against real Op encodings and the fixture's
/// `listPushFrontCoin.zkir`: eight instructions longer than
/// [`list_push_front`], and the pushed node is BLANK — `[0x11, 0x33,
/// 0x00, 0x00, 0x00]`, an `Array[3]` of three `Null`s — with the coin
/// put at `node[0]` by the `insc 1` that closes the dance.
#[test]
fn list_push_front_coin_matches_field_repr() {
    let (cm, coin) = coin_operands();
    let ops = list_push_front_coin(2, &cm, &coin);
    let plain = list_push_front(2, &coin);
    assert_eq!(ops.len(), plain.len() + 8);

    // The head — identical to `pushFront`'s, up to the node push.
    for (i, (mine, twin)) in ops.iter().zip(&plain).take(4).enumerate() {
        assert_eq!(imms(mine), imms(twin), "instruction {i}");
    }
    assert_eq!(
        imms(&ops[4]),
        vec![
            Fr::from(0x11u64),
            Fr::from(0x33u64),
            Fr::from(0u64),
            Fr::from(0u64),
            Fr::from(0u64),
        ]
    );
    // push 0u8 — the head slot the qualified coin is inserted at.
    assert_eq!(
        imms(&ops[5]),
        vec![Fr::from(0x10u64), 1u64.into(), 1u64.into(), 1u64.into(), 0u64.into()]
    );
    assert_qualify_dance(&ops[6..12], 7);
    assert_eq!(imms(&ops[12]), vec![Fr::from(0xa1u64)]);
    // …and the tail is `pushFront`'s, instruction for instruction.
    for (i, (mine, twin)) in ops[13..].iter().zip(&plain[5..]).enumerate() {
        assert_eq!(imms(mine), imms(twin), "tail instruction {i}");
    }
}

/// `set_insert` against real Op encodings (depositViaVault.zkir:
/// pushs null = [0x11, 0x00], ins = 0x91, insc = 0xa1).
#[test]
fn set_insert_matches_field_repr() {
    use midnight_onchain_state::state::StateValue;

    let ops = set_insert(2, &LedgerValue::bytes(1, vec![ImpactElem::Imm(Fr::from(7u64))]));
    assert_eq!(
        imms(&ops[2]),
        repr(&Op::Push {
            storage: true,
            value: StateValue::Null,
        })
    );
    assert_eq!(imms(&ops[2]), vec![Fr::from(0x11u64), Fr::from(0u64)]);
    assert_eq!(
        imms(&ops[3]),
        repr(&Op::Ins {
            cached: false,
            n: 1,
        })
    );
    assert_eq!(imms(&ops[3]), vec![Fr::from(0x91u64)]);
}

/// The read shapes' constant ops, against initialise.zkir's annotated
/// stream (test-caller-contract): dup 0 = 0x30, read idx of field 6 =
/// [0x50, 1, 1, 6], kernel-self reach = dup 2 + idxc [0].
#[test]
fn read_shape_constants_match_corpus_golden() {
    assert_eq!(imms(&dup(0)), vec![Fr::from(0x30u64)]);
    assert_eq!(imms(&dup(2)), vec![Fr::from(0x32u64)]);
    assert_eq!(
        imms(&idx_one(false, false, 6)),
        vec![Fr::from(0x50u64), 1u64.into(), 1u64.into(), 6u64.into()]
    );
    assert_eq!(
        imms(&ImpactOp::constant(&Op::Idx {
            cached: true,
            push_path: false,
            path: vec![Key::Value(field_key(0))].into(),
        })),
        vec![Fr::from(0x60u64), 1u64.into(), 1u64.into(), 0u64.into()]
    );
}

// --- M22 stage B1: the general path -------------------------------------

/// A `Bytes<32>` map key as both a real `AlignedValue` (for `Op`) and a
/// [`LedgerValue`] (for ours), with the same limbs.
fn b32_key() -> (AlignedValue, LedgerValue) {
    let mut bytes = [0u8; 32];
    bytes[0] = 0x2a; // lo limb
    bytes[31] = 0x01; // hi byte
    let av = AlignedValue::new(
        Value(vec![ValueAtom(bytes.to_vec()).normalize()]),
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 32,
        })]),
    )
    .unwrap();
    let lv = LedgerValue::bytes(
        32,
        vec![
            ImpactElem::Imm(Fr::from(1u64)),
            ImpactElem::Imm(Fr::from(0x2au64)),
        ],
    );
    (av, lv)
}

/// EVERY [`LedgerKey`] variant encodes as upstream's `Key::field_repr`.
///
/// This is the whole soundness claim of `LedgerKey`: the enum splits
/// `Key::Value(AlignedValue)` into a const-known field index and a
/// possibly-wire-bearing value, and adds nothing. If the split were
/// wrong, every nested path would be wrong in the same way.
#[test]
fn key_encoding_matches_field_repr() {
    fn ours(key: &LedgerKey) -> Vec<Fr> {
        let mut out = Vec::new();
        key.push_elems(&mut out);
        out.into_iter()
            .map(|e| match e {
                ImpactElem::Imm(f) => f,
                ImpactElem::Wire(_) => panic!("expected constant"),
            })
            .collect()
    }
    fn real(key: &Key) -> Vec<Fr> {
        let mut out = Vec::new();
        key.field_repr(&mut out);
        out
    }

    for index in [0u8, 1, 7, 255] {
        assert_eq!(
            ours(&LedgerKey::Field(index)),
            real(&Key::Value(field_key(index))),
            "field {index}"
        );
    }
    let (av, lv) = b32_key();
    assert_eq!(ours(&LedgerKey::Value(lv)), real(&Key::Value(av)));
    assert_eq!(ours(&LedgerKey::Stack), real(&Key::Stack));
}

/// [`idx_path`] is `Op::Idx`'s encoding at every depth and in all four
/// cached/pushPath corners — the opcode's low nibble is `len − 1`
/// (ops.rs:510-524, reduce-to-zkir.ss:586-601).
#[test]
fn idx_path_matches_field_repr() {
    let (av, lv) = b32_key();
    let cases: Vec<(Vec<LedgerKey>, Vec<Key>)> = vec![
        (vec![LedgerKey::Field(3)], vec![Key::Value(field_key(3))]),
        (
            vec![LedgerKey::Field(0), LedgerKey::Value(lv.clone())],
            vec![Key::Value(field_key(0)), Key::Value(av.clone())],
        ),
        (
            vec![
                LedgerKey::Field(6),
                LedgerKey::Value(lv.clone()),
                LedgerKey::Value(lv),
            ],
            vec![
                Key::Value(field_key(6)),
                Key::Value(av.clone()),
                Key::Value(av),
            ],
        ),
        (
            vec![LedgerKey::Field(1), LedgerKey::Stack],
            vec![Key::Value(field_key(1)), Key::Stack],
        ),
    ];
    for (ours, theirs) in cases {
        for (cached, push_path) in [(false, false), (true, false), (false, true), (true, true)] {
            assert_eq!(
                imms(&idx_path(cached, push_path, &ours)),
                repr(&Op::Idx {
                    cached,
                    push_path,
                    path: theirs.clone().into(),
                }),
                "depth {} cached={cached} pushPath={push_path}",
                ours.len()
            );
        }
    }
}

/// THE ADDITIVITY CLAIM, checked rather than asserted: every `u8` builder
/// is its `_at` twin on the one-element path, byte for byte. This is what
/// makes the widening free of movement for all 167 pre-existing circuits.
#[test]
fn the_u8_builders_are_the_one_element_path() {
    fn same(a: &[ImpactOp], b: &[ImpactOp], what: &str) {
        assert_eq!(a.len(), b.len(), "{what}: length");
        for (i, (x, y)) in a.iter().zip(b).enumerate() {
            assert_eq!(imms(x), imms(y), "{what}: op {i}");
        }
    }
    let (_, key) = b32_key();
    let one = [LedgerKey::Field(2)];
    same(&cell_write(2, &key), &cell_write_at(&one, &key), "cell_write");
    same(
        &counter_increment(2, 5),
        &counter_increment_at(&one, 5),
        "counter_increment",
    );
    same(
        &map_insert(2, &key, &key),
        &map_insert_at(&one, &key, &key),
        "map_insert",
    );
    same(&map_remove(2, &key), &map_remove_at(&one, &key), "map_remove");
    same(&set_insert(2, &key), &set_insert_at(&one, &key), "set_insert");
    same(&map_reset(2), &map_reset_at(&one), "map_reset");
    same(&list_reset(2), &list_reset_at(&one), "list_reset");
    same(
        &list_push_front(2, &key),
        &list_push_front_at(&one, &key),
        "list_push_front",
    );
    same(&list_pop_front(2), &list_pop_front_at(&one), "list_pop_front");
    same(
        &merkle_tree_insert(2, &key),
        &merkle_tree_insert_at(&one, &key),
        "merkle_tree_insert",
    );
    same(
        &merkle_tree_insert_index(2, &key, &key),
        &merkle_tree_insert_index_at(&one, &key, &key),
        "merkle_tree_insert_index",
    );
    same(
        &merkle_tree_reset(2, 8),
        &merkle_tree_reset_at(&one, 8),
        "merkle_tree_reset",
    );
    same(
        &historic_merkle_tree_insert(2, &key),
        &historic_merkle_tree_insert_at(&one, &key),
        "historic_merkle_tree_insert",
    );
    same(
        &historic_merkle_tree_insert_index(2, &key, &key),
        &historic_merkle_tree_insert_index_at(&one, &key, &key),
        "historic_merkle_tree_insert_index",
    );
    same(
        &historic_merkle_tree_reset_history(2),
        &historic_merkle_tree_reset_history_at(&one),
        "historic_merkle_tree_reset_history",
    );
    same(
        &historic_merkle_tree_reset(2, 8),
        &historic_merkle_tree_reset_at(&one, 8),
        "historic_merkle_tree_reset",
    );
    same(
        &cell_write_coin(2, &key, &key),
        &cell_write_coin_at(&one, &key, &key),
        "cell_write_coin",
    );
    same(
        &set_insert_coin(2, &key, &key),
        &set_insert_coin_at(&one, &key, &key),
        "set_insert_coin",
    );
    same(
        &map_insert_coin(2, &key, &key, &key),
        &map_insert_coin_at(&one, &key, &key, &key),
        "map_insert_coin",
    );
    same(
        &list_push_front_coin(2, &key, &key),
        &list_push_front_coin_at(&one, &key, &key),
        "list_push_front_coin",
    );
}

/// A two-element path against the stream compactc actually emits for
/// `mm.lookup(k).insert(k2, v)` — the `0x71 … 0x91 0xa2` the note
/// predicted from `ShieldedMultiSig`, decoded here from a probe compiled
/// with the pinned compactc:
///
/// ```text
/// 0x71 [1,1,0] [1,-2,k]    idxp [field 0, k]
/// 0x10 [1,1,-2,k2]         push k2
/// 0x11 [1,1,8,7]           pushs (cell u64 7)
/// 0x91                     ins 1
/// 0xa2                     insc 2
/// ```
#[test]
fn nested_map_insert_matches_compactc() {
    let key = LedgerValue::new(
        vec![AlignmentAtom::Field],
        vec![ImpactElem::Imm(Fr::from(11u64))],
    );
    let value = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(7u64))]);
    let path = [LedgerKey::Field(0), LedgerKey::Value(key.clone())];
    let ops = map_insert_at(&path, &key, &value);
    assert_eq!(ops.len(), 5);
    let field = Fr::from(0u64) - Fr::from(2u64);
    assert_eq!(
        imms(&ops[0]),
        vec![
            Fr::from(0x71u64),
            1u64.into(),
            1u64.into(),
            0u64.into(),
            1u64.into(),
            field,
            11u64.into()
        ]
    );
    assert_eq!(
        imms(&ops[1]),
        vec![Fr::from(0x10u64), 1u64.into(), 1u64.into(), field, 11u64.into()]
    );
    assert_eq!(
        imms(&ops[2]),
        vec![Fr::from(0x11u64), 1u64.into(), 1u64.into(), 8u64.into(), 7u64.into()]
    );
    assert_eq!(imms(&ops[3]), vec![Fr::from(0x91u64)]);
    assert_eq!(imms(&ops[4]), vec![Fr::from(0xa2u64)]);
}

/// A THREE-element path: the opcode nibble and the closing `insc` both
/// track `len(f)`, which is what a `Map<K, Map<K, Map<K, V>>>` write
/// compiles to (`0x72 … 0xa3`).
#[test]
fn three_level_path_tracks_the_depth() {
    let key = LedgerValue::new(
        vec![AlignmentAtom::Field],
        vec![ImpactElem::Imm(Fr::from(3u64))],
    );
    let path = [
        LedgerKey::Field(6),
        LedgerKey::Value(key.clone()),
        LedgerKey::Value(key.clone()),
    ];
    let ops = map_insert_at(&path, &key, &key);
    assert_eq!(imms(&ops[0])[0], Fr::from(0x72u64));
    assert_eq!(imms(&ops[4]), vec![Fr::from(0xa3u64)]);
}

/// PATH SUPPRESSION, both halves, at the depth where they come alive.
///
/// `map_reset(0)` is three instructions because `(suppress-null …)` and
/// `(suppress-zero …)` both fire; `map_reset_at([field, k])` is FIVE —
/// the `idxp [field 0]` and the `insc 1` reappear around the same middle.
/// Verified against compactc's own `a.lookup(k).resetToDefault()`.
#[test]
fn reset_suppression_comes_alive_at_depth_two() {
    let key = LedgerValue::new(
        vec![AlignmentAtom::Field],
        vec![ImpactElem::Imm(Fr::from(11u64))],
    );
    let field = Fr::from(0u64) - Fr::from(2u64);

    let flat = map_reset(0);
    assert_eq!(flat.len(), 3);
    assert_eq!(imms(&flat[0])[0], Fr::from(0x10u64));

    let ops = map_reset_at(&[LedgerKey::Field(0), LedgerKey::Value(key)]);
    assert_eq!(ops.len(), 5);
    assert_eq!(
        imms(&ops[0]),
        vec![Fr::from(0x70u64), 1u64.into(), 1u64.into(), 0u64.into()]
    );
    assert_eq!(
        imms(&ops[1]),
        vec![Fr::from(0x10u64), 1u64.into(), 1u64.into(), field, 11u64.into()],
        "the LAST path element is what gets pushed, not the field index"
    );
    assert_eq!(imms(&ops[2]), vec![Fr::from(0x11u64), 2u64.into()]);
    assert_eq!(imms(&ops[3]), vec![Fr::from(0x91u64)]);
    assert_eq!(imms(&ops[4]), vec![Fr::from(0xa1u64)]);
}

/// The two op families whose closing depth is NOT `len(f)`:
/// `List.pushFront` and `MerkleTree.insert` close at `len(f) + 1`, and
/// `HistoricMerkleTree.resetHistory` at `len(f) + 2`.
#[test]
fn the_off_by_one_closings_track_the_depth() {
    let key = LedgerValue::new(
        vec![AlignmentAtom::Field],
        vec![ImpactElem::Imm(Fr::from(1u64))],
    );
    let path = [LedgerKey::Field(1), LedgerKey::Value(key.clone())];

    let push = list_push_front_at(&path, &key);
    assert_eq!(*imms(&push[push.len() - 1]).last().unwrap(), Fr::from(0xa3u64));
    let pop = list_pop_front_at(&path);
    assert_eq!(imms(&pop[pop.len() - 1]), vec![Fr::from(0xa2u64)]);

    let mt = merkle_tree_insert_at(&path, &key);
    assert_eq!(imms(&mt[mt.len() - 1]), vec![Fr::from(0xa3u64)]);
    let mti = merkle_tree_insert_index_at(&path, &key, &key);
    assert_eq!(imms(&mti[mti.len() - 1]), vec![Fr::from(0xa2u64)]);

    let hmt = historic_merkle_tree_insert_at(&path, &key);
    assert_eq!(imms(&hmt[hmt.len() - 1]), vec![Fr::from(0xa3u64)]);
    let hist = historic_merkle_tree_reset_history_at(&path);
    assert_eq!(imms(&hist[hist.len() - 1]), vec![Fr::from(0xa4u64)]);
}

/// A NESTED `Cell` WRITE, which Compact reaches by a route that has
/// nothing to do with `Map` nesting.
///
/// `determine-ledger-paths.ss` BATCHES a contract's ledger fields into
/// segments of `maximum-ledger-segment-length` = 15 (langs.ss:851), so a
/// contract with sixteen fields gives every field a TWO-element path and
/// every top-level `Cell` write becomes a nested one. Compiled with the
/// pinned compactc, a 16-field contract's `f0 = v` is
///
/// ```text
/// 0x70 [1,1,0]        idxp [segment 0]
/// 0x10 [1,1,1,0]      push the field index
/// 0x11 [1,1,8,v]      pushs v
/// 0x91                ins 1
/// 0xa1                insc 1
/// ```
///
/// and `f15 = v` is the same with `[1, 14]`. Both suppressions are live.
/// No MinoCrab contract declares more than thirteen fields today, which
/// is why nothing had noticed; the general path is the fix, and the
/// derive's `at(index)` is what still has to learn it (stage B2).
#[test]
fn a_sixteen_field_contract_makes_every_cell_write_nested() {
    let v = LedgerValue::bytes(8, vec![ImpactElem::Imm(Fr::from(9u64))]);
    for (segment, index) in [(0u8, 0u8), (1, 14)] {
        let ops = cell_write_at(&[LedgerKey::Field(segment), LedgerKey::Field(index)], &v);
        assert_eq!(ops.len(), 5);
        assert_eq!(
            imms(&ops[0]),
            vec![
                Fr::from(0x70u64),
                1u64.into(),
                1u64.into(),
                u64::from(segment).into()
            ]
        );
        assert_eq!(
            imms(&ops[1]),
            vec![
                Fr::from(0x10u64),
                1u64.into(),
                1u64.into(),
                1u64.into(),
                u64::from(index).into()
            ]
        );
        assert_eq!(
            imms(&ops[2]),
            vec![Fr::from(0x11u64), 1u64.into(), 1u64.into(), 8u64.into(), 9u64.into()]
        );
        assert_eq!(imms(&ops[3]), vec![Fr::from(0x91u64)]);
        assert_eq!(imms(&ops[4]), vec![Fr::from(0xa1u64)]);
    }
}

/// The four coin arms' `dup` reaches are compactc's formulas in `len(f)`,
/// and they agree with stage A's four constants at depth 1.
///
/// The depth-2 row is compactc's, not arithmetic: a probe declaring
/// `Map<K, Set<QSCI>>`, `Map<K, Map<K, QSCI>>` and `Map<K, List<QSCI>>`
/// compiles to `dup 6` / `dup 7` / `dup 9`.
#[test]
fn the_coin_reaches_are_compactcs_formulas() {
    assert_eq!(
        [
            cell_coin_dup(1),
            set_coin_dup(1),
            map_coin_dup(1),
            list_coin_dup(1)
        ],
        [3, 4, 5, 7],
        "stage A's CELL/SET/MAP/LIST_COIN_DUP"
    );
    assert_eq!(
        [
            cell_coin_dup(2),
            set_coin_dup(2),
            map_coin_dup(2),
            list_coin_dup(2)
        ],
        [5, 6, 7, 9]
    );
    let (_, key) = b32_key();
    let path = [LedgerKey::Field(0), LedgerKey::Value(key.clone())];
    // `dup 7` is the second instruction of a nested Map.insertCoin (after
    // the idxp and the key push it is the third).
    let ops = map_insert_coin_at(&path, &key, &key, &key);
    assert_eq!(imms(&ops[2]), vec![Fr::from(0x37u64)]);
}

/// AN ADT-VALUED `insertDefault` PUSHES THE ADT'S INITIAL VALUE, not a
/// zero cell — `VMstate-value-ADT` discards the value and expands the
/// ADT's `(initial-value …)` (reduce-to-zkir.ss:424-433). Against
/// compactc's `a.insertDefault(k)` on `Map<Field, Map<Field, Uint<64>>>`,
/// which emits `0x11 0x02` (the empty map) where the flat form emits
/// `0x11 [1,1,8,0]`.
#[test]
fn adt_valued_insert_default_pushes_the_initial_value() {
    let key = LedgerValue::new(
        vec![AlignmentAtom::Field],
        vec![ImpactElem::Imm(Fr::from(11u64))],
    );
    let flat = map_insert_default_at(&field_path(0), &key, vec![U64_ATOM]);
    assert_eq!(
        imms(&flat[2]),
        vec![Fr::from(0x11u64), 1u64.into(), 1u64.into(), 8u64.into(), 0u64.into()]
    );

    let nested = map_insert_adt_default_at(&field_path(0), &key, empty_map());
    assert_eq!(imms(&nested[2]), vec![Fr::from(0x11u64), 2u64.into()]);
    assert_eq!(
        imms(&nested[2]),
        imms(&map_reset(0)[1]),
        "the initial value is the one resetToDefault writes"
    );

    let list = map_insert_adt_default_at(&field_path(1), &key, empty_list());
    assert_eq!(imms(&list[2]), imms(&list_reset(1)[1]));

    let counter = map_insert_adt_default_at(&field_path(2), &key, empty_counter());
    assert_eq!(
        imms(&counter[2]),
        vec![Fr::from(0x11u64), 1u64.into(), 1u64.into(), 8u64.into(), 0u64.into()]
    );
}

// ---- the deploy state's values (notes/ledger-header.org) ---------------------

/// A Cell of ZEROS, as a deploy state stores it, is the circuit's default:
/// its field representation is exactly [`default_value`]'s zero limbs, for
/// every atom kind a slot type is made of — so the deploy builder's default
/// Cell and a circuit's `resetToDefault`-shaped write (`cell_write_at` of
/// `default_value`) are one value. Zeros given at full width normalize to
/// the same stored value (FAB drops trailing zero bytes).
#[test]
fn a_stored_zero_cell_is_the_default_values_limbs() {
    use midnight_transient_crypto::fab::ValueReprAlignedValue;
    let b = |length| AlignmentAtom::Bytes { length };
    for atoms in [
        vec![b(1)],
        vec![b(8)],
        vec![b(32)],
        vec![b(2), b(3)],
        vec![b(1), b(32)],
        vec![AlignmentAtom::Field],
        vec![AlignmentAtom::Compress],
        vec![AlignmentAtom::Field, AlignmentAtom::Field],
        vec![b(24), b(8), b(24), b(8), AlignmentAtom::Field],
    ] {
        let empty = stored_cell(atoms.clone(), vec![Vec::new(); atoms.len()]);
        let StateValue::Cell(ref av) = empty else {
            panic!("stored_cell builds a Cell");
        };
        let mut limbs: Vec<Fr> = Vec::new();
        ValueReprAlignedValue((**av).clone()).field_repr(&mut limbs);
        let zeros: Vec<Fr> = default_value(atoms.clone())
            .elems()
            .iter()
            .map(|e| match e {
                ImpactElem::Imm(f) => *f,
                ImpactElem::Wire(_) => panic!("default_value is constant"),
            })
            .collect();
        assert_eq!(limbs, zeros, "{atoms:?}");
        let full_width: Vec<Vec<u8>> = atoms
            .iter()
            .map(|a| match a {
                AlignmentAtom::Bytes { length } => vec![0; *length as usize],
                _ => vec![0],
            })
            .collect();
        assert!(stored_cell(atoms.clone(), full_width) == empty, "{atoms:?}");
    }
}

/// A `Bytes<32>` ending in NUL bytes is stored TRIMMED (the placeholder
/// magic keeps 26 of its 32), under the one-atom `bytes<32>` alignment —
/// the form compactc's constructor writes (P0b's oracle: 26 bytes stored).
#[test]
fn a_magic_is_stored_trimmed_under_one_bytes32_atom() {
    let mut magic = [0u8; 32];
    magic[..26].copy_from_slice(b"mip-0099:ledger-header[v1]");
    let cell = stored_cell(
        vec![AlignmentAtom::Bytes { length: 32 }],
        vec![magic.to_vec()],
    );
    let StateValue::Cell(ref av) = cell else {
        panic!("stored_cell builds a Cell");
    };
    assert_eq!(av.value.0.len(), 1);
    assert_eq!(av.value.0[0].0, b"mip-0099:ledger-header[v1]".to_vec());
    assert_eq!(
        av.alignment,
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Bytes {
            length: 32
        })])
    );
}

/// The two lists must agree: one stored value per atom.
#[test]
#[should_panic(expected = "stored atoms for alignment")]
fn a_stored_cell_needs_one_value_per_atom() {
    let _ = stored_cell(vec![AlignmentAtom::Bytes { length: 8 }], vec![]);
}

/// A reset HistoricMerkleTree is the declared value with ONE history
/// entry — the blank tree's root, valued Null — which is what
/// `history_append` leaves (the VM-run twin of this is minocrab-std's
/// `v3_state`, and compactc's JS agrees in project 00002's T4b).
#[test]
fn a_reset_historic_tree_remembers_the_blank_root() {
    let reset = historic_merkle_tree_reset_value(10);
    let declared = empty_historic_merkle_tree_value(10);
    let (StateValue::Array(ref reset), StateValue::Array(ref declared)) = (reset, declared) else {
        panic!("both are Arrays");
    };
    assert_eq!(reset.len(), 3);
    assert!(reset.get(0) == declared.get(0), "the blank tree");
    assert!(reset.get(1) == declared.get(1), "next index 0");
    let (Some(StateValue::Map(history)), Some(StateValue::Map(empty))) =
        (reset.get(2), declared.get(2))
    else {
        panic!("the history is a Map");
    };
    assert!(empty.is_empty());
    assert_eq!(history.size(), 1);
    let entry = history.iter().next().expect("one entry");
    let (ref root, ref value) = *entry;
    // The root of a blank tree is the field element zero, stored as the
    // empty `field` atom.
    assert_eq!(
        root.alignment,
        Alignment(vec![AlignmentSegment::Atom(AlignmentAtom::Field)])
    );
    assert!(**value == StateValue::Null);
}
