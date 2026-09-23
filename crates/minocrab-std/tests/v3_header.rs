//! LEDGER HEADERS, laid out (notes/ledger-header.org; FR-001–FR-004,
//! FR-012): a standard at `root[0]` of every block that embeds it, the
//! block's own fields at compactc's layout of those fields alone moved one
//! root slot along, wherever the standard is declared.
//!
//! The exhaustive half of the rule — every body size 0..=256, every field —
//! is `FieldPath::in_layout`'s unit test in `v3::ledger`, pinned against
//! `batch`. This file is the DERIVE's half: real `#[derive(Ledger)]`
//! blocks, flat and segmented, each checked field by field against the
//! same fields without the standard (compactc's layout, the oracle), plus
//! the header's own shapes, declaration-order independence, and a stream
//! whose headed circuits are byte-identical to its compactc twin's.
//!
//! The compile-time rejections (FR-005) are doctests on
//! `v3::LedgerHeader` (and, for `Signet`, on `signet_flow::Signet`).

use minocrab::v3::{Circuit3, Compiled3};
use minocrab::Public;
use minocrab_std::v3::blind::{Add, Max};
use minocrab_std::v3::{
    label, pad32, ArgPath, BlockLayout, CircuitArg, Disclose, FieldPath, Ledger, LedgerCell,
    LedgerCounter, LedgerField, LedgerHeader, LedgerMap, LedgerWidth, Placement, Stream,
    StreamSpec, Uint,
};
use minocrab_zkir::v3::to_zkir_string;

type U64 = Uint<64, Public>;

// ---- the standards ----------------------------------------------------------------

/// Magic-only: a Cell at `[0]`.
#[derive(LedgerHeader)]
struct Mip0099;

impl LedgerHeader for Mip0099 {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
}

/// Two fields: an Array at `[0]` — magic `[0, 0]`, `version` `[0, 1]`,
/// `admins` `[0, 2]`.
#[derive(LedgerHeader)]
struct Versioned {
    version: LedgerCounter,
    admins: LedgerMap<U64, U64>,
}

impl LedgerHeader for Versioned {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
}

#[test]
fn a_standard_is_width_zero_at_the_root() {
    assert_eq!(<Mip0099 as LedgerWidth>::WIDTH, 0);
    assert_eq!(<Mip0099 as LedgerWidth>::PLACEMENT, Placement::RootHeader);
    assert!(<Mip0099 as LedgerWidth>::KINDS.is_empty());
    assert_eq!(<Versioned as LedgerWidth>::WIDTH, 0);
    assert_eq!(<Versioned as LedgerWidth>::PLACEMENT, Placement::RootHeader);
    assert_eq!(<LedgerField as LedgerWidth>::PLACEMENT, Placement::Body);
    assert_eq!(
        <Mip0099 as LedgerHeader>::MAGIC[..26],
        *b"mip-0099:ledger-header[v1]"
    );
    assert!(<Mip0099 as LedgerHeader>::MAGIC[26..]
        .iter()
        .all(|b| *b == 0));
}

// ---- blocks: every body field against compactc's layout of the body alone --------

/// A block of `LedgerField`s (their paths are observable), headed or not,
/// plus a `paths()` listing every body field's path in declaration order.
macro_rules! field_block {
    ($name:ident, [$($f:ident)*]) => {
        #[derive(Ledger)]
        struct $name {
            $($f: LedgerField,)*
        }

        impl $name {
            fn paths(&self) -> Vec<Vec<u8>> {
                vec![$(self.$f.field_path().as_slice().to_vec()),*]
            }
        }
    };
    ($name:ident, std: $std:ty, [$($f:ident)*]) => {
        #[derive(Ledger)]
        struct $name {
            std: $std,
            $($f: LedgerField,)*
        }

        impl $name {
            fn paths(&self) -> Vec<Vec<u8>> {
                vec![$(self.$f.field_path().as_slice().to_vec()),*]
            }

            fn magic(&self) -> Vec<u8> {
                self.std.magic().field_path().as_slice().to_vec()
            }
        }
    };
}

/// Headed = compactc's paths of the same fields with the first element + 1,
/// and nothing at `root[0]`.
fn assert_moved_one_root_slot(headed: &[Vec<u8>], compactc: &[Vec<u8>], what: &str) {
    assert_eq!(headed.len(), compactc.len(), "{what}");
    for (k, (h, c)) in headed.iter().zip(compactc).enumerate() {
        let mut expected = c.clone();
        expected[0] += 1;
        assert_eq!(h, &expected, "{what}, field {k}");
        assert_eq!(h.len(), c.len(), "{what}, field {k}: depth is compactc's");
    }
}

field_block!(H0, std: Mip0099, []);
field_block!(P1, [f0]);
field_block!(H1, std: Mip0099, [f0]);
field_block!(P3, [f0 f1 f2]);
field_block!(H3, std: Mip0099, [f0 f1 f2]);
field_block!(P14, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13]);
field_block!(H14, std: Mip0099, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13]);
field_block!(P15, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14]);
field_block!(H15, std: Mip0099, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14]);
field_block!(P16, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15]);
field_block!(H16, std: Versioned, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15]);
field_block!(P30, [
    f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
    f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
]);
field_block!(H30, std: Mip0099, [
    f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
    f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
]);

/// Spec User Story 1: flat bodies go to `[1..=n]` (fifteen fields give a
/// sixteen-entry root), segmented ones keep compactc's depth one root slot
/// along — through the real derive, for 0, 1, 3, 14, 15, 16 and 30 own
/// fields, magic-only and multi-field standards.
#[test]
fn the_derive_lays_a_headed_body_out_one_root_slot_along() {
    // No own fields: the standard alone, the root one entry (P2 builds it).
    assert_eq!(H0::new().magic(), [0]);
    assert!(H0::new().paths().is_empty());
    // The magic is at `[0]` (or `[0, 0]`) in every one of them.
    for magic in [
        H1::new().magic(),
        H3::new().magic(),
        H14::new().magic(),
        H15::new().magic(),
        H30::new().magic(),
        SixteenFirst::new().magic(),
    ] {
        assert_eq!(magic, [0]);
    }
    assert_eq!(H16::new().magic(), [0, 0]);
    assert_moved_one_root_slot(&H1::new().paths(), &P1::new().paths(), "1");
    assert_moved_one_root_slot(&H3::new().paths(), &P3::new().paths(), "3");
    assert_moved_one_root_slot(&H14::new().paths(), &P14::new().paths(), "14");
    assert_moved_one_root_slot(&H15::new().paths(), &P15::new().paths(), "15");
    assert_moved_one_root_slot(&H16::new().paths(), &P16::new().paths(), "16");
    assert_moved_one_root_slot(&H30::new().paths(), &P30::new().paths(), "30");
    // The spec's literal scenarios.
    assert_eq!(
        H15::new().f14.field_path().as_slice(),
        &[15],
        "16-entry root"
    );
    assert_eq!(H16::new().f0.field_path().as_slice(), &[1, 0]);
    assert_eq!(H16::new().f1.field_path().as_slice(), &[2, 0]);
    assert_eq!(H16::new().f15.field_path().as_slice(), &[2, 14]);
    // …and each is what the layout function says.
    assert_eq!(
        H30::new().f29.field_path().as_slice(),
        FieldPath::in_layout(BlockLayout::headed(30), 29).as_slice()
    );
}

/// The header's own paths depend on no block: the magic at `[0]` or
/// `[0, 0]`, a multi-field standard's fields at `[0, i + 1]`.
#[test]
fn the_header_is_at_the_root_whatever_the_block() {
    let h16 = H16::new();
    assert_eq!(h16.std.magic().field_path().as_slice(), &[0, 0]);
    // `admins` is a Map, whose path is observable; `version`, a Counter,
    // shows its `[0, 1]` through the ops it emits (below).
    assert_eq!(h16.std.admins.field_path().as_slice(), &[0, 2]);
    assert_eq!(H3::new().std.magic().field_path().as_slice(), &[0]);
    assert_eq!(H30::new().std.magic().field_path().as_slice(), &[0]);
}

/// A header field is an ordinary slot at its header path: the standard's
/// `version.increment` is byte-identical to a Counter declared at `[0, 1]`
/// by hand, and `admins.member` to a Map at `[0, 2]`.
#[test]
fn a_header_field_emits_the_ops_of_a_slot_at_its_header_path() {
    let via_standard = compile(|c| H16::new().std.version.increment(c, 1));
    let version: LedgerCounter = LedgerCounter::at_path(&[0, 1]);
    let by_hand = compile(|c| version.increment(c, 1));
    assert_eq!(zkir(via_standard), zkir(by_hand));
    let via_standard = compile(|c| {
        let k = key(c);
        let _ = H16::new().std.admins.member(c, &k);
    });
    let by_hand = compile(|c| {
        let k = key(c);
        let admins: LedgerMap<U64, U64> = LedgerMap::at_path(&[0, 2]);
        let _ = admins.member(c, &k);
    });
    assert_eq!(zkir(via_standard), zkir(by_hand));
}

// ---- declaration-order independence (FR-003) ---------------------------------------

#[derive(Ledger)]
struct First {
    std: Versioned,
    a: LedgerField,
    b: LedgerMap<U64, U64>,
    c: LedgerField,
}

#[derive(Ledger)]
struct Middle {
    a: LedgerField,
    b: LedgerMap<U64, U64>,
    std: Versioned,
    c: LedgerField,
}

#[derive(Ledger)]
struct Last {
    a: LedgerField,
    b: LedgerMap<U64, U64>,
    c: LedgerField,
    std: Versioned,
}

field_block!(SixteenFirst, std: Mip0099, [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15]);

#[derive(Ledger)]
struct SixteenLast {
    f0: LedgerField,
    f1: LedgerField,
    f2: LedgerField,
    f3: LedgerField,
    f4: LedgerField,
    f5: LedgerField,
    f6: LedgerField,
    f7: LedgerField,
    f8: LedgerField,
    f9: LedgerField,
    f10: LedgerField,
    f11: LedgerField,
    f12: LedgerField,
    f13: LedgerField,
    f14: LedgerField,
    f15: LedgerField,
    std: Mip0099,
}

/// T1b: first, middle or last, the standard's position in the struct
/// changes nothing — the other fields keep their relative order and the
/// same paths, and the header is where it always is.
#[test]
fn where_the_standard_is_declared_does_not_matter() {
    let (f, m, l) = (First::new(), Middle::new(), Last::new());
    for (a, b, c, std) in [
        (&f.a, &f.b, &f.c, &f.std),
        (&m.a, &m.b, &m.c, &m.std),
        (&l.a, &l.b, &l.c, &l.std),
    ] {
        assert_eq!(a.field_path().as_slice(), &[1]);
        assert_eq!(b.field_path().as_slice(), &[2]);
        assert_eq!(c.field_path().as_slice(), &[3]);
        assert_eq!(std.magic().field_path().as_slice(), &[0, 0]);
        assert_eq!(std.admins.field_path().as_slice(), &[0, 2]);
    }
    // Segmented: sixteen fields, the standard first or last.
    let last = SixteenLast::new();
    let last_paths: Vec<Vec<u8>> = [
        &last.f0, &last.f1, &last.f2, &last.f3, &last.f4, &last.f5, &last.f6, &last.f7, &last.f8,
        &last.f9, &last.f10, &last.f11, &last.f12, &last.f13, &last.f14, &last.f15,
    ]
    .iter()
    .map(|f| f.field_path().as_slice().to_vec())
    .collect();
    assert_eq!(SixteenFirst::new().paths(), last_paths);
    assert_eq!(last.std.magic().field_path().as_slice(), &[0]);
}

// ---- a stream in a headed block: byte-identical to its compactc twin ------------------

/// The sig-net outbox's stream shape, `(nonce, last seen)` by `(Add, Max)`.
struct Nonces;

impl StreamSpec for Nonces {
    type Key = U64;
    type Body = U64;
    type Head = U64;
    type State = (U64, U64);
    type Step = (Add, Max);

    fn head(_c: &mut Circuit3, body: &U64) -> U64 {
        *body
    }

    fn delta(c: &mut Circuit3, head: &U64) -> (U64, U64) {
        (Uint::from_field_unchecked(c.constant(1u64)), *head)
    }
}

#[derive(Ledger)]
struct HeadedStream {
    before: LedgerCell<U64>,
    std: Mip0099,
    nonces: Stream<Nonces>,
}

/// compactc's layout of the same body behind one leading field — for a flat
/// body, exactly the headed layout.
#[derive(Ledger)]
struct LeadingStream {
    lead: LedgerField,
    before: LedgerCell<U64>,
    nonces: Stream<Nonces>,
}

label! {
    Key = "the key";
    Body = "the body";
}

fn compile(body: impl FnOnce(&mut Circuit3)) -> Compiled3 {
    let mut c = Circuit3::new();
    body(&mut c);
    c.finish(false)
}

fn zkir(compiled: Compiled3) -> String {
    to_zkir_string(&compiled.ir).expect("the IR serializes")
}

fn key(c: &mut Circuit3) -> U64 {
    let k = <Uint<64> as CircuitArg>::declare(c, &ArgPath::root("k"));
    k.constrain(c);
    k.disclose_as::<Key>(c)
}

fn two_args(c: &mut Circuit3) -> (U64, U64) {
    let k = <Uint<64> as CircuitArg>::declare(c, &ArgPath::root("k"));
    let b = <Uint<64> as CircuitArg>::declare(c, &ArgPath::root("b"));
    k.constrain(c);
    b.constrain(c);
    (k.disclose_as::<Key>(c), b.disclose_as::<Body>(c))
}

/// FR-011 for `Stream`: it keeps the block's layout, so its bodies, its two
/// accumulator cells and its two snapshot maps are all headed — insert,
/// take and combine emit exactly what the compactc twin's do.
#[test]
fn a_headed_stream_is_its_compactc_twin_byte_for_byte() {
    const H: HeadedStream = HeadedStream::new();
    const L: LeadingStream = LeadingStream::new();
    assert_eq!(H.before.index(), 1);
    assert_eq!(L.before.index(), 1);
    assert_eq!(L.lead.field_path().as_slice(), &[0]);
    assert_eq!(H.std.magic().field_path().as_slice(), &[0]);
    let insert = |s: &Stream<Nonces>| {
        zkir(compile(|c| {
            let (k, b) = two_args(c);
            s.insert(c, &k, &b);
        }))
    };
    assert_eq!(insert(&H.nonces), insert(&L.nonces), "insert");
    let take = |s: &Stream<Nonces>| {
        zkir(compile(|c| {
            let (k, _) = two_args(c);
            let _ = s.take(c, &k);
        }))
    };
    assert_eq!(take(&H.nonces), take(&L.nonces), "take");
    let combine = |s: &Stream<Nonces>| {
        zkir(compile(|c| {
            let (_k, h) = two_args(c);
            let zero = Uint::from_field_unchecked(c.constant(0u64));
            s.combine(c, (zero, h));
        }))
    };
    assert_eq!(combine(&H.nonces), combine(&L.nonces), "combine");
    // …and the headed stream is NOT where an unheaded one would be.
    const PLAIN: Stream<Nonces> = Stream::at_block(6, 1);
    assert_ne!(insert(&H.nonces), insert(&PLAIN), "the header moved it");
}
