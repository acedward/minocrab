//! `opaque.compact` — Compact's `Opaque<'ts-type'>` in every position it can
//! occupy, through [`minocrab_std::v3::Opaque`] (M15,
//! notes/opaque-bridging.org).
//!
//! Not a corpus contract, for M14's reason: the corpus has 74 `Opaque` nodes
//! and none of them is in a v3 artifact (only the three sig-net sources carry
//! `--feature-zkir-v3`, and their four are all `Secp256k1Point`). So the
//! source is ours, lives beside its differential at `tests/fixtures/opaque/`,
//! and was compiled with the PINNED compactc.
//!
//! **AN OPAQUE IS IN THE CIRCUIT.** One native slot, no constraint, one FAB
//! `compress` atom — and the value in that slot is
//! `transient_commit(bytes, len)`, zero for the empty value. So it is a
//! BINDING COMMITMENT, not a handle: [`Opaque::eq`] decides equality of the
//! TS-side values, and `default` is the field zero because upstream
//! special-cases the empty byte string. Nothing else is offered, because
//! nothing else exists — the commitment is one-way.
//!
//! | circuit | Compact | what it pins |
//! |---|---|---|
//! | `opArg` | one `Opaque<"string">` argument | one input slot, NO constraint instruction |
//! | `opRet` | returns it | one output slot, same type |
//! | `opEq` | `a == b` | one `test_eq` over two commitments |
//! | `opDefault` | `default<Opaque<"string">>` | the immediate `0x00` |
//! | `opCell` | a `Cell` write | the `compress` atom as the Impact immediate `-0x01` |
//! | `opWitness` | a witness returning one | `private_input`, no constraint |
//! | `opMapValue` | a `Map` VALUE | `-0x01` in the value position beside a `b32` key |
//! | `opMapKey` | a `Map` KEY | `-0x01` in the key position |
//! | `opSet` | `Set` insert then member | the two ops a Compact `Set` is made of |
//! | `opMaybe` | `Maybe<Opaque<…>>` | tag limb then payload limb |
//! | `opBytes` | a SECOND ts-type | that the two do not unify |
//! | `opStruct` | an opaque beside a `Uint<8>` | slot order, and that only the neighbour is constrained |
//! | `opPoint` | `Secp256k1Point` | the curve spelling compactc publishes as `Opaque` |
//! | `opJubjub` | `JubjubPoint` | the same, over two `field` atoms |
//!
//! The last two are why this fixture also closes a BUG rather than only
//! adding a feature: compactc's ABI spells both point types
//! `Alias { name, Opaque { tsType: name } }`, our reader refused them, and the
//! erc20-vault's own `initialize` was therefore not flattenable
//! (notes/opaque-bridging.org §0b).

use minocrab::v3::Circuit3;
use minocrab::Public;
use minocrab_std::v3::{
    contract, label, ts, Bool, CircuitArg, Disclose, Discloses, JubjubPoint, Ledger, LedgerCell,
    LedgerCounter, LedgerMap, LedgerSet, Maybe, Opaque, Secp256k1Point, Uint, B32,
};

/// `Opaque<"string">`, at whichever visibility — the type this whole module is
/// about, written once so the circuits below read like the Compact source.
pub type OpaqueStr<V = minocrab::Private> = Opaque<ts::Str, V>;
/// `Opaque<"Uint8Array">`.
pub type OpaqueBytes<V = minocrab::Private> = Opaque<ts::Uint8Array, V>;

label! {
    /// The opaque value, whose disclosure records its COMMITMENT — which is
    /// all the circuit ever held.
    Name = "name";
    Other = "other";
    Tag = "tag";
    Key = "key";
    Point = "point";
}

/// THE LEDGER BLOCK — declaration order is the field index, matching the
/// fixture's `export ledger` block one for one.
///
/// Every shape an opaque can be stored in is here, which is the point: the
/// `compress` atom has to travel through a `Cell`, both halves of a `Map`, a
/// `Set` element and a `Maybe` payload, and each is a different position in
/// the Impact push encoding.
#[derive(Ledger)]
pub struct OpaqueLedger {
    pub dummy: LedgerCounter,
    pub cell: LedgerCell<OpaqueStr<Public>>,
    pub bytes_cell: LedgerCell<OpaqueBytes<Public>>,
    pub maybe: LedgerCell<Maybe<OpaqueStr<Public>, Public>>,
    pub names: LedgerSet<OpaqueStr<Public>>,
    pub by_hash: LedgerMap<B32<Public>, OpaqueStr<Public>>,
    pub by_name: LedgerMap<OpaqueStr<Public>, Uint<64, Public>>,
    pub response_key: LedgerCell<Secp256k1Point<Public>>,
    pub jubjub_key: LedgerCell<JubjubPoint<Public>>,
}

/// The contract's ledger block.
pub const OPAQUE: OpaqueLedger = OpaqueLedger::new();

/// `struct Tagged { tag: Uint<8>, name: Opaque<"string"> }` — an opaque inside
/// `#[derive(CircuitArg)]`, whose generated `constrain` runs the table over
/// both slots and emits for exactly one of them.
#[derive(CircuitArg)]
pub struct Tagged {
    pub tag: Uint<8>,
    pub name: OpaqueStr,
}

#[contract]
impl OpaqueLedger {
    /// `export circuit opArg(x: Opaque<"string">): [] { dummy.increment(1); }`
    ///
    /// The whole circuit is the argument declaration, and the argument declaration
    /// emits NO constraint — which is the one thing this circuit exists to pin.
    #[circuit]
    pub fn op_arg(c: &mut Circuit3, x: OpaqueStr) -> Discloses<()> {
        let _ = x;
        OPAQUE.dummy.increment(c, 1);
        Discloses::of(())
    }

    /// `export circuit opRet(x: Opaque<"string">): Opaque<"string"> { … return x; }`
    ///
    /// Returning is disclosing (M9 phase 2), so the label is in the signature.
    #[circuit(output = "name")]
    pub fn op_ret(c: &mut Circuit3, x: OpaqueStr) -> Discloses<Name, OpaqueStr<Public>> {
        OPAQUE.dummy.increment(c, 1);
        Discloses::of(x.disclose_as::<Name>(c))
    }

    /// `export circuit opEq(a, b: Opaque<"string">): Boolean { return a == b; }`
    ///
    /// One `test_eq`. Sound as an equality on the TS-side values, because the two
    /// slots hold their commitments (see the module docs).
    #[circuit(output = "equal")]
    pub fn op_eq(
        c: &mut Circuit3,
        a: OpaqueStr,
        b: OpaqueStr,
    ) -> Discloses<(Name, Other), Bool<Public>> {
        OPAQUE.dummy.increment(c, 1);
        let a = a.disclose_as::<Name>(c);
        let b = b.disclose_as::<Other>(c);
        Discloses::of(Bool::from_field_unchecked(a.eq(c, b)))
    }

    /// `export circuit opDefault(): [] { cell = default<Opaque<"string">>; }`
    ///
    /// The empty value's commitment is the field zero, so this is one constant
    /// that inlines as the Impact immediate `0x00` — no ceremony on either side.
    #[circuit]
    pub fn op_default(c: &mut Circuit3) -> Discloses<()> {
        let empty = OpaqueStr::<Public>::default_value(c);
        OPAQUE.cell.write(c, &empty);
        Discloses::of(())
    }

    /// `export circuit opCell(x: Opaque<"string">): [] { cell = disclose(x); }`
    #[circuit]
    pub fn op_cell(c: &mut Circuit3, x: OpaqueStr) -> Discloses<Name> {
        let x = x.disclose_as::<Name>(c);
        OPAQUE.cell.write(c, &x);
        Discloses::of(())
    }

    /// `export circuit opWitness(): [] { cell = disclose(w_name()); }`
    ///
    /// A witnessed opaque is a bare `private_input` with no constraint — there is
    /// no range to check and no canonicity to enforce, because a `compress` atom
    /// admits any value.
    #[circuit]
    pub fn op_witness(c: &mut Circuit3) -> Discloses<Name> {
        let name = OpaqueStr::from_field_unchecked(c.witness());
        let name = name.disclose_as::<Name>(c);
        OPAQUE.cell.write(c, &name);
        Discloses::of(())
    }

    /// `export circuit opMapValue(k: Bytes<32>, v: Opaque<"string">): []
    /// { by_hash.insert(disclose(k), disclose(v)); }`
    #[circuit]
    pub fn op_map_value(c: &mut Circuit3, k: B32<minocrab::Private>, v: OpaqueStr) -> Discloses<(Key, Name)> {
        let k = k.disclose_as::<Key>(c);
        let v = v.disclose_as::<Name>(c);
        OPAQUE.by_hash.insert(c, &k, &v);
        Discloses::of(())
    }

    /// `export circuit opMapKey(k: Opaque<"string">): []
    /// { by_name.insert(disclose(k), 1); }`
    ///
    /// An opaque as a map KEY, which is the position where a wrong atom would
    /// silently key a different entry.
    #[circuit]
    pub fn op_map_key(c: &mut Circuit3, k: OpaqueStr) -> Discloses<Key> {
        let k = k.disclose_as::<Key>(c);
        let one: Uint<64, Public> = Uint::from_field_unchecked(c.constant(minocrab::Fr::from(1u64)));
        OPAQUE.by_name.insert(c, &k, &one);
        Discloses::of(())
    }

    /// `export circuit opSet(k: Opaque<"string">): Boolean
    /// { names.insert(disclose(k)); return names.member(disclose(k)); }`
    #[circuit(output = "member")]
    pub fn op_set(c: &mut Circuit3, k: OpaqueStr) -> Discloses<Key, Bool<Public>> {
        let k = k.disclose_as::<Key>(c);
        OPAQUE.names.insert(c, &k);
        Discloses::of(*OPAQUE.names.member(c, &k))
    }

    /// `export circuit opMaybe(x: Opaque<"string">): []
    /// { maybe = some<Opaque<"string">>(disclose(x)); }`
    ///
    /// The tag's limb then the payload's — the payload occupies its slot either
    /// way, which is the fixed-width rule Compact's `Maybe` already follows and
    /// M11's `Flagged` names.
    #[circuit]
    pub fn op_maybe(c: &mut Circuit3, x: OpaqueStr) -> Discloses<Name> {
        let x = x.disclose_as::<Name>(c);
        let some = Maybe {
            is_some: Bool::from_field_unchecked(c.constant(minocrab::Fr::from(1u64))),
            value: x,
        };
        OPAQUE.maybe.write(c, &some);
        Discloses::of(())
    }

    /// `export circuit opBytes(x: Opaque<"Uint8Array">): []
    /// { bytes_cell = disclose(x); }`
    ///
    /// The second ts-type. Its whole job is that `OpaqueStr` and `OpaqueBytes` are
    /// DIFFERENT Rust types: writing this value to `OPAQUE.cell` does not compile,
    /// which is the same rejection compactc makes ("expected right-hand side of =
    /// to have type `Opaque<"string">` but received `Opaque<"Uint8Array">`").
    #[circuit]
    pub fn op_bytes(c: &mut Circuit3, x: OpaqueBytes) -> Discloses<Name> {
        let x = x.disclose_as::<Name>(c);
        OPAQUE.bytes_cell.write(c, &x);
        Discloses::of(())
    }

    /// `export circuit opStruct(w: Tagged): [] { cell = disclose(w.name); }`
    #[circuit]
    pub fn op_struct(c: &mut Circuit3, w: Tagged) -> Discloses<(Tag, Name)> {
        let _ = w.tag.disclose_as::<Tag>(c);
        let name = w.name.disclose_as::<Name>(c);
        OPAQUE.cell.write(c, &name);
        Discloses::of(())
    }

    /// `export circuit opPoint(p: Secp256k1Point): []
    /// { response_key = disclose(p); }`
    ///
    /// compactc publishes this argument as `Opaque<"Secp256k1Point">` under an
    /// `Alias` of the same name, and our ABI reader used to refuse it — which is
    /// why the erc20-vault's own `initialize` was not flattenable. The leaf itself
    /// has existed since M9 phase 5; what M15 fixed is the READER.
    #[circuit]
    pub fn op_point(c: &mut Circuit3, p: Secp256k1Point) -> Discloses<Point> {
        let p = p.disclose_as::<Point>(c);
        OPAQUE.response_key.write(c, &p);
        Discloses::of(())
    }

    /// `export circuit opJubjub(p: JubjubPoint): [] { jubjub_key = disclose(p); }`
    ///
    /// The other curve spelling, over two `field` atoms instead of five mixed
    /// ones.
    #[circuit]
    pub fn op_jubjub(c: &mut Circuit3, p: JubjubPoint) -> Discloses<Point> {
        let p = p.disclose_as::<Point>(c);
        OPAQUE.jubjub_key.write(c, &p);
        Discloses::of(())
    }
}
