//! `header_small.compact` and `header_n15.compact` — COMPACTC PARITY OF A
//! HEADED BLOCK (notes/ledger-header.org; spec 00002 User Story 5, FR-010,
//! SC-005), and `header_n16.compact`, the size at which it ends.
//!
//! A team that deploys through compactc's generated JS writes the Compact
//! twin of a headed contract with the standard's magic as its FIRST field,
//! written by the constructor (`magic = pad(32, "…")`). For a body of at
//! most fourteen fields that twin and minocrab's headed block are the SAME
//! contract: compactc keeps fifteen fields or fewer in one flat root, the
//! magic at `[0]` and field `k` at `[k]`, which is exactly the headed rule —
//! the standard at `[0]`, compactc's layout of the body one root slot along.
//! Checked at two sizes, four own fields (`header_small`: a Cell, a Counter,
//! a Map and a never-written `Bytes<32>`) and fourteen (`header_n15`:
//! compactc's flat root at its widest, fifteen entries):
//!
//! 1. `identical_instruction_streams` — every circuit's canonical ZKIR is
//!    compactc's, the differential machinery every port here uses.
//! 2. `the_layout_is_compactcs` — every field's path is the one compactc's
//!    own `contract-info.json` records.
//! 3. `the_initial_state_is_compactcs` — `initial_state()` serializes to what
//!    compactc's generated `initialState` serializes, byte for byte
//!    (`tests/fixtures/initial_state/header_*.state.hex`, produced in node by
//!    project 00002's JS oracle; provenance in each file's header), with no
//!    `set`: the standard's magic is already in it. With compactc's three
//!    empty operations registered, it is compactc's WHOLE `ContractState`.
//! 4. `the_reader_finds_the_magic_in_both` — `v3::discriminator` returns the
//!    magic on compactc's serialized states (the whole one included: a state
//!    carrying compactc's own operations) and on minocrab's deployed twins.
//!
//! THE NEGATIVE CONTROL, `header_n16` (P0b's Probe B `n16`): with FIFTEEN own
//! fields the two part ways, by design. compactc segments the sixteen fields
//! (the magic at `[0, 0]`, the fields at `[1, 0]..[1, 14]`); the headed rule
//! keeps the body flat behind the standard (the magic at `[0]`, the fields at
//! `[1]..[15]`, a sixteen-entry root). The tests assert that minocrab's
//! layout is the headed rule's, that the port is NOT compactc's, and that the
//! difference is exactly that: the same sixteen leaves in the same order
//! under another root shape, and for the circuit the same write at another
//! path. Past fourteen own fields a Compact twin cannot deploy a headed
//! contract's state; minocrab's builder does.
//!
//! IT IS A TEST-ONLY SET OF CONTRACTS: nothing here enters the frozen
//! snapshots or the ZKIR dump.

#[path = "ledger_deploy/deploy.rs"]
mod deploy;

use midnight_onchain_state::state::{ContractOperation, ContractState, EntryPointBuf, StateValue};
use midnight_storage::db::InMemoryDB;
use midnight_storage::storage::{Array, HashMap as StorageHashMap};
use minocrab::v3::{Circuit3, Compiled3};
use minocrab::{Private, Public};
use minocrab_std::v3::{
    circuit, contract_state_discriminator, discriminator, implements, label, pad32, Disclose,
    Discloses, FieldPath, Ledger, LedgerCell, LedgerCounter, LedgerHeader, LedgerMap, Uint, B32,
};
use minocrab_zkir::v3::{to_zkir_string, IrSource};

label! {
    Val = "value";
    Key = "key";
}

type U64 = Uint<64, Public>;
type B32P = B32<Public>;
type State = StateValue<InMemoryDB>;

// ---- the standard ------------------------------------------------------------------

/// The fixtures' placeholder standard: magic-only, a Cell at `[0]` — what
/// each Compact twin's constructor writes as its first field.
#[derive(LedgerHeader)]
struct Mip0099;

impl LedgerHeader for Mip0099 {
    const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
}

/// `f = disclose(v)` for one Cell — every Cell-writing circuit below.
macro_rules! write_v {
    ($name:ident, $cell:expr) => {
        #[circuit]
        fn $name(c: &mut Circuit3, v: Uint<64, Private>) -> Discloses<(Val,)> {
            let v = v.disclose_as::<Val>(c);
            $cell.write(c, &v);
            Discloses::of(())
        }
    };
}

// ---- header_small: four own fields ---------------------------------------------------

/// `header_small.compact`'s block: the magic, then `value`, `count`,
/// `balances`, `owner` — declaration order is the field index.
#[derive(Ledger)]
struct HeaderSmall {
    std: Mip0099,
    value: LedgerCell<U64>,
    count: LedgerCounter,
    balances: LedgerMap<B32P, U64>,
    owner: LedgerCell<B32P>,
}

const HEADER_SMALL: HeaderSmall = HeaderSmall::new();

// `export circuit setValue(v: Uint<64>): [] { value = disclose(v); }`
write_v!(set_value, HEADER_SMALL.value);

/// `export circuit bump(): [] { count.increment(1); }`
#[circuit]
fn bump(c: &mut Circuit3) -> Discloses<()> {
    HEADER_SMALL.count.increment(c, 1);
    Discloses::of(())
}

/// `export circuit credit(k: Bytes<32>, v: Uint<64>): []
/// { balances.insert(disclose(k), disclose(v)); }`
#[circuit]
fn credit(c: &mut Circuit3, k: B32<Private>, v: Uint<64, Private>) -> Discloses<(Key, Val)> {
    let k = k.disclose_as::<Key>(c);
    let v = v.disclose_as::<Val>(c);
    HEADER_SMALL.balances.insert(c, &k, &v);
    Discloses::of(())
}

// ---- header_n15: fourteen own fields, the widest flat root ------------------------------

/// `header_n15.compact`'s block: the magic, then `f1..f14` — `f8` a Counter,
/// `f14` a Map, every other a `Uint<64>` Cell.
#[derive(Ledger)]
struct HeaderN15 {
    std: Mip0099,
    f1: LedgerCell<U64>,
    f2: LedgerCell<U64>,
    f3: LedgerCell<U64>,
    f4: LedgerCell<U64>,
    f5: LedgerCell<U64>,
    f6: LedgerCell<U64>,
    f7: LedgerCell<U64>,
    f8: LedgerCounter,
    f9: LedgerCell<U64>,
    f10: LedgerCell<U64>,
    f11: LedgerCell<U64>,
    f12: LedgerCell<U64>,
    f13: LedgerCell<U64>,
    f14: LedgerMap<U64, U64>,
}

const HEADER_N15: HeaderN15 = HeaderN15::new();

// `export circuit wFirst(v: Uint<64>): [] { f1 = disclose(v); }`
write_v!(w_first, HEADER_N15.f1);

/// `export circuit bump(): [] { f8.increment(1); }`
#[circuit]
fn bump_n15(c: &mut Circuit3) -> Discloses<()> {
    HEADER_N15.f8.increment(c, 1);
    Discloses::of(())
}

/// `export circuit credit(k: Uint<64>, v: Uint<64>): []
/// { f14.insert(disclose(k), disclose(v)); }` — the root's last entry.
#[circuit]
fn credit_n15(
    c: &mut Circuit3,
    k: Uint<64, Private>,
    v: Uint<64, Private>,
) -> Discloses<(Key, Val)> {
    let k = k.disclose_as::<Key>(c);
    let v = v.disclose_as::<Val>(c);
    HEADER_N15.f14.insert(c, &k, &v);
    Discloses::of(())
}

// ---- header_n16: the negative control ---------------------------------------------------

/// minocrab's headed port of `header_n16.compact`: the standard, then
/// fifteen own `Uint<64>` cells — flat behind the standard.
#[derive(Ledger)]
struct HeaderN16 {
    std: Mip0099,
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

const HEADER_N16: HeaderN16 = HeaderN16::new();

/// The same sixteen fields WITHOUT a standard — the magic a plain
/// `Bytes<32>` cell declared first — which is compactc's layout of the
/// Compact twin (T4b's `C16`). It pins that the compactc side is modelled
/// right, so the headed port's difference is the headed rule's and nothing
/// else.
#[derive(Ledger)]
struct PlainN16 {
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

const PLAIN_N16: PlainN16 = PlainN16::new();

/// `f15`'s two paths, placed by hand: the headed rule's and compactc's.
const AT_15: LedgerCell<U64> = LedgerCell::at_path(&[15]);
const AT_1_14: LedgerCell<U64> = LedgerCell::at_path(&[1, 14]);

// `export circuit wLast(v: Uint<64>): [] { f15 = disclose(v); }`, four ways.
write_v!(w_last_headed, HEADER_N16.f15);
write_v!(w_last_plain, PLAIN_N16.f15);
write_v!(write_at_15, AT_15);
write_v!(write_at_1_14, AT_1_14);

// ---- instruments --------------------------------------------------------------------

/// compactc's artifact for one fixture circuit.
fn theirs(fixture: &str, name: &str) -> IrSource {
    let path = format!(
        "{}/tests/fixtures/{fixture}/out/zkir/{name}.zkir",
        env!("CARGO_MANIFEST_DIR")
    );
    minocrab_zkir::v3::read_zkir(&path).expect("the pinned compactc's artifact parses")
}

/// Serialized ZKIR with every `%name.index` identifier replaced by
/// `%<order of first appearance>` — the canonicalization every differential
/// here uses, over both sides' folded IR.
fn canonical(ir: &IrSource) -> String {
    let ir = &minocrab_ir::v3::passes::folded(ir);
    let text = to_zkir_string(ir).expect("serializes");
    let mut renames: Vec<(String, String)> = Vec::new();
    let mut out = String::with_capacity(text.len());
    let mut rest = text.as_str();
    while let Some(at) = rest.find('%') {
        out.push_str(&rest[..at]);
        rest = &rest[at..];
        let end = rest[1..]
            .find(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == '.'))
            .map(|i| i + 1)
            .unwrap_or(rest.len());
        let name = &rest[..end];
        let next = renames.len();
        let canon = match renames.iter().find(|(from, _)| from == name) {
            Some((_, to)) => to.clone(),
            None => {
                let to = format!("%{next}");
                renames.push((name.to_string(), to.clone()));
                to
            }
        };
        out.push_str(&canon);
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

/// The operands of every `impact` instruction of a serialized circuit, a
/// wire written `%wire`.
fn impacts(ir: &IrSource) -> Vec<Vec<String>> {
    let text = to_zkir_string(&minocrab_ir::v3::passes::folded(ir)).expect("serializes");
    let json: serde_json::Value = serde_json::from_str(&text).expect("the artifact is JSON");
    json["instructions"]
        .as_array()
        .expect("instructions")
        .iter()
        .filter(|i| i["op"] == "impact")
        .map(|i| {
            i["inputs"]
                .as_array()
                .expect("operands")
                .iter()
                .map(|v| match v.as_str() {
                    Some(s) if s.starts_with('%') => "%wire".to_string(),
                    Some(s) => s.to_string(),
                    None => panic!("an operand that is not a string: {v}"),
                })
                .collect()
        })
        .collect()
}

/// compactc's own layout: `contract-info.json`'s `ledger[]`, name → path
/// (`index` is a bare number at depth 1, a list below).
fn compactc_layout(fixture: &str) -> Vec<(String, Vec<u8>)> {
    let text = std::fs::read_to_string(format!(
        "{}/tests/fixtures/{fixture}/out/compiler/contract-info.json",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("the pinned compactc's contract-info is committed");
    let json: serde_json::Value = serde_json::from_str(&text).expect("contract-info is JSON");
    let byte = |v: &serde_json::Value| -> u8 {
        u8::try_from(v.as_u64().expect("an index is a number")).expect("an index fits a byte")
    };
    json["ledger"]
        .as_array()
        .expect("a ledger")
        .iter()
        .map(|field| {
            let path = match &field["index"] {
                serde_json::Value::Array(elems) => elems.iter().map(byte).collect(),
                index => vec![byte(index)],
            };
            (field["name"].as_str().expect("a name").to_string(), path)
        })
        .collect()
}

/// A block's layout as the derive gave it: `magic` first (the standard's
/// handle, or a plain field of that name), then each named field.
macro_rules! layout {
    ($block:expr, magic: $magic:expr; $($field:ident),* $(,)?) => {
        vec![
            ("magic".to_string(), $magic.field_path().as_slice().to_vec()),
            $((stringify!($field).to_string(), $block.$field.field_path().as_slice().to_vec()),)*
        ]
    };
}

/// A fixture's bytes: the hex after its `#` provenance lines.
fn oracle(name: &str) -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/initial_state")
        .join(format!("{name}.state.hex"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let hex: String = text
        .lines()
        .filter(|line| !line.starts_with('#'))
        .flat_map(|line| line.trim().chars())
        .collect();
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

/// A serialized, tagged `ContractState`, read back with the pinned ledger.
fn contract_of(bytes: &[u8]) -> ContractState<InMemoryDB> {
    midnight_serialize::tagged_deserialize(bytes).expect("compactc's bytes are a ContractState")
}

fn contract_bytes(contract: &ContractState<InMemoryDB>) -> Vec<u8> {
    let mut bytes = Vec::new();
    midnight_serialize::tagged_serialize(contract, &mut bytes)
        .expect("a contract state serializes");
    bytes
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// `ours` serializes (data-only) to the oracle's bytes; `what` says whose.
fn assert_same_bytes(what: &str, ours: &[u8], theirs: &[u8]) {
    assert!(
        ours == theirs,
        "{what}: minocrab's bytes ({}) differ from compactc's ({})\nours:   {}\ntheirs: {}",
        ours.len(),
        theirs.len(),
        hex(ours),
        hex(theirs),
    );
}

/// A state tree's shape, leaves elided.
#[derive(Debug, PartialEq)]
enum Shape {
    Leaf,
    Array(Vec<Shape>),
}

fn shape(state: &State) -> Shape {
    match state {
        StateValue::Array(items) => Shape::Array(
            (0..items.len())
                .map(|i| shape(items.get(i).expect("in range")))
                .collect(),
        ),
        _ => Shape::Leaf,
    }
}

/// Every leaf, depth first — the tree read in path order.
fn leaves(state: &State) -> Vec<State> {
    match state {
        StateValue::Array(items) => (0..items.len())
            .flat_map(|i| leaves(items.get(i).expect("in range")))
            .collect(),
        leaf => vec![leaf.clone()],
    }
}

fn array(items: Vec<State>) -> State {
    StateValue::Array(Array::from(items))
}

// ---- T6: parity --------------------------------------------------------------------

/// Every parity circuit: its fixture, compactc's artifact name, our builder.
fn cases() -> Vec<(&'static str, &'static str, fn() -> Compiled3)> {
    vec![
        ("header_small", "setValue", set_value as fn() -> Compiled3),
        ("header_small", "bump", bump),
        ("header_small", "credit", credit),
        ("header_n15", "wFirst", w_first),
        ("header_n15", "bump", bump_n15),
        ("header_n15", "credit", credit_n15),
    ]
}

/// CLAIM 1, the headline: for both sizes, every circuit of the headed port
/// IS compactc's — op for op, immediate for immediate.
#[test]
fn identical_instruction_streams() {
    for (fixture, name, build) in cases() {
        assert_eq!(
            canonical(&build().ir),
            canonical(&theirs(fixture, name)),
            "{fixture}::{name}: the headed port differs from compactc's magic-first twin"
        );
    }
}

/// Every `.zkir` compactc produced for the three fixtures has a case: the
/// parity cases above, and `header_n16`'s `wLast` in the negative control.
#[test]
fn every_fixture_circuit_is_covered() {
    for fixture in ["header_small", "header_n15", "header_n16"] {
        let dir = format!(
            "{}/tests/fixtures/{fixture}/out/zkir",
            env!("CARGO_MANIFEST_DIR")
        );
        let mut compiled: Vec<String> = std::fs::read_dir(&dir)
            .expect("the fixture is compiled")
            .map(|entry| {
                entry
                    .expect("a readable entry")
                    .file_name()
                    .to_string_lossy()
                    .trim_end_matches(".zkir")
                    .to_string()
            })
            .collect();
        compiled.sort();
        let mut covered: Vec<String> = cases()
            .iter()
            .filter(|(f, _, _)| *f == fixture)
            .map(|(_, n, _)| n.to_string())
            .chain((fixture == "header_n16").then(|| "wLast".to_string()))
            .collect();
        covered.sort();
        assert_eq!(compiled, covered, "{fixture}");
    }
}

/// CLAIM 2: every field — the magic included — is where compactc's own
/// `contract-info.json` puts it: `[0]`, then `[1]..[n]`, one flat root.
#[test]
fn the_layout_is_compactcs() {
    let small =
        layout!(HEADER_SMALL, magic: HEADER_SMALL.std.magic(); value, count, balances, owner);
    assert_eq!(small, compactc_layout("header_small"));
    assert_eq!(small.last().map(|(_, p)| p.as_slice()), Some(&[4u8][..]));

    let n15 = layout!(HEADER_N15, magic: HEADER_N15.std.magic();
        f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14);
    assert_eq!(n15, compactc_layout("header_n15"));
    for (k, (_, path)) in n15.iter().enumerate() {
        assert_eq!(path, &[k as u8], "field {k}: depth 1, its own index");
    }
}

/// CLAIM 3: `initial_state()` — the standard's magic already in it, nothing
/// `set` — is compactc's generated `initialState`, byte for byte; and the
/// ledger deploys it and stores it verbatim.
#[test]
fn the_initial_state_is_compactcs() {
    for (name, state) in [
        ("header_small", HeaderSmall::initial_state().build()),
        ("header_n15", HeaderN15::initial_state().build()),
    ] {
        let ours = deploy::data_only_bytes(state.clone());
        let theirs = oracle(name);
        assert_same_bytes(name, &ours, &theirs);
        assert_eq!(ours.len(), if name == "header_small" { 323 } else { 410 });
        assert!(
            deploy::deploy(state.clone()).data() == state,
            "{name}: the ledger stores the state it was given"
        );
    }
}

/// …and compactc's WHOLE `ContractState` — the one its JS hands a deployer,
/// with `credit`, `setValue` and `bump` registered as operations without a
/// verifier key — is the twin's state with the same three operations.
#[test]
fn the_whole_contract_state_is_compactcs() {
    let mut operations = StorageHashMap::new();
    for entry in ["credit", "setValue", "bump"] {
        operations = operations.insert(
            EntryPointBuf(entry.as_bytes().to_vec()),
            ContractOperation::new(None, None),
        );
    }
    let ours = ContractState::new(
        HeaderSmall::initial_state().build(),
        operations,
        Default::default(),
    );
    let theirs = oracle("header_small_full");
    assert_eq!(theirs.len(), 519);
    assert_same_bytes("header_small_full", &contract_bytes(&ours), &theirs);
}

/// CLAIM 4: the reader finds the magic on compactc's serialized states —
/// the data-only form and the whole one, whose operations are compactc's
/// own — and on minocrab's twins, built and deployed.
#[test]
fn the_reader_finds_the_magic_in_both() {
    for name in ["header_small", "header_small_full", "header_n15"] {
        let bytes = oracle(name);
        assert_eq!(
            contract_state_discriminator(&bytes).expect("compactc's bytes are a ContractState"),
            Some(Mip0099::MAGIC),
            "{name}: compactc's own bytes"
        );
        assert!(
            implements::<Mip0099>(contract_of(&bytes).data.get_ref()),
            "{name}: compactc's twin claims the standard"
        );
    }
    let whole = contract_of(&oracle("header_small_full"));
    assert_eq!(
        whole.operations.size(),
        3,
        "compactc registers three operations"
    );

    for (name, state) in [
        ("header_small", HeaderSmall::initial_state().build()),
        ("header_n15", HeaderN15::initial_state().build()),
    ] {
        assert_eq!(discriminator(&state), Some(Mip0099::MAGIC), "{name}: built");
        assert!(implements::<Mip0099>(&state), "{name}: claims the standard");
        let deployed = deploy::deploy(state);
        assert_eq!(
            contract_state_discriminator(&contract_bytes(&deployed.contract()))
                .expect("the ledger's own bytes are a ContractState"),
            Some(Mip0099::MAGIC),
            "{name}: minocrab's twin, deployed and read back"
        );
    }
}

// ---- the negative control: fifteen own fields ----------------------------------------------

/// minocrab's layout of fifteen own fields is the HEADED RULE's (the magic at
/// `[0]`, field `k` at `in_block(15, k - 1)` + 1 = `[k]`, a sixteen-entry
/// root), and compactc's is its segmentation (`[0, 0]`, `[1, k - 1]`): every
/// path differs. The plain port reproduces compactc's `contract-info.json`,
/// so the compactc side is modelled right.
#[test]
fn negative_control_the_layout_is_the_headed_rules_not_compactcs() {
    let headed = layout!(HEADER_N16, magic: HEADER_N16.std.magic();
        f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15);
    let plain = layout!(PLAIN_N16, magic: PLAIN_N16.magic;
        f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15);
    let theirs = compactc_layout("header_n16");
    assert_eq!(plain, theirs, "the plain port is compactc's layout");

    assert_eq!(headed[0].1, [0], "the magic at [0]");
    assert_eq!(theirs[0].1, [0, 0], "compactc's magic at [0, 0]");
    for k in 1..=15usize {
        let mut rule = FieldPath::in_block(15, k - 1).as_slice().to_vec();
        rule[0] += 1;
        assert_eq!(headed[k].1, rule, "f{k}: the headed rule");
        assert_eq!(headed[k].1, [k as u8], "f{k}: flat, one root slot along");
        assert_eq!(theirs[k].1, [1, k as u8 - 1], "f{k}: compactc's segment");
    }
    for ((name, ours), (_, compactcs)) in headed.iter().zip(&theirs) {
        assert_ne!(ours, compactcs, "{name}: the two layouts share no path");
    }
}

/// The circuit: the headed `wLast` is NOT compactc's, and the difference is
/// exactly the path. The same write placed by hand at `[15]` is the headed
/// port; at `[1, 14]` it is compactc's. On the wire: compactc's depth-2 write
/// is `idxp [1]; push 14; pushs v; ins 1; insc 1`, the headed depth-1 write
/// `push 15; pushs v; ins 1` — the value's push is the same instruction.
#[test]
fn negative_control_the_circuit_differs_exactly_by_the_path() {
    let compactcs = theirs("header_n16", "wLast");
    let theirs_c = canonical(&compactcs);
    assert_eq!(
        canonical(&w_last_plain().ir),
        theirs_c,
        "the plain port IS compactc's"
    );
    let ours = canonical(&w_last_headed().ir);
    assert_ne!(ours, theirs_c, "the headed port is not compactc's");
    assert_eq!(
        ours,
        canonical(&write_at_15().ir),
        "ours: the write at [15]"
    );
    assert_eq!(
        theirs_c,
        canonical(&write_at_1_14().ir),
        "compactc's: the write at [1, 14]"
    );

    let wire = |ops: &[&str]| ops.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    let value_push = wire(&["0x11", "0x01", "0x01", "0x08", "%wire"]);
    assert_eq!(
        impacts(&compactcs),
        vec![
            wire(&["0x70", "0x01", "0x01", "0x01"]),
            wire(&["0x10", "0x01", "0x01", "0x01", "0x0e"]),
            value_push.clone(),
            wire(&["0x91"]),
            wire(&["0xa1"]),
        ],
        "compactc: idxp [1]; push cell 14; pushs v; ins 1; insc 1"
    );
    assert_eq!(
        impacts(&w_last_headed().ir),
        vec![
            wire(&["0x10", "0x01", "0x01", "0x01", "0x0f"]),
            value_push,
            wire(&["0x91"]),
        ],
        "headed: push cell 15; pushs v; ins 1"
    );
}

/// The initial state: NOT compactc's bytes, and the difference is exactly
/// the root's shape. The same sixteen leaves in the same order (the magic,
/// then fifteen zero `Uint<64>` cells); minocrab's root is flat (sixteen
/// entries, the ledger accepts it), compactc's is `[[magic], [15 cells]]`;
/// and re-nesting minocrab's leaves into compactc's shape gives compactc's
/// bytes exactly (`b_n16.state.hex`: the JS oracle's state for Probe B
/// `n16`, which `header_n16.compact` repeats verbatim — P4 checked the
/// oracle gives the committed fixture the same bytes). The reader finds the
/// magic in both.
#[test]
fn negative_control_the_state_differs_exactly_by_the_root_shape() {
    let ours = HeaderN16::initial_state().build();
    let theirs_bytes = oracle("b_n16");
    let theirs = contract_of(&theirs_bytes).data.get_ref().clone();
    assert_ne!(
        deploy::data_only_bytes(ours.clone()),
        theirs_bytes,
        "the headed state is not compactc's"
    );

    assert_eq!(
        shape(&ours),
        Shape::Array((0..16).map(|_| Shape::Leaf).collect())
    );
    assert_eq!(
        shape(&theirs),
        Shape::Array(vec![
            Shape::Array(vec![Shape::Leaf]),
            Shape::Array((0..15).map(|_| Shape::Leaf).collect()),
        ])
    );
    let (ours_leaves, theirs_leaves) = (leaves(&ours), leaves(&theirs));
    assert_eq!(ours_leaves.len(), 16);
    assert!(
        ours_leaves == theirs_leaves,
        "the same leaves, in the same order"
    );

    let renested = array(vec![
        array(vec![ours_leaves[0].clone()]),
        array(ours_leaves[1..].to_vec()),
    ]);
    assert_same_bytes(
        "the headed leaves under compactc's root",
        &deploy::data_only_bytes(renested),
        &theirs_bytes,
    );

    // The plain port's state, with the constructor's write, IS compactc's.
    let mut plain = PlainN16::initial_state();
    plain.set(PLAIN_N16.magic.field_path(), ours_leaves[0].clone());
    assert_same_bytes(
        "the plain port",
        &deploy::data_only_bytes(plain.build()),
        &theirs_bytes,
    );

    // The reader is indifferent to the difference: the first leaf either way.
    assert_eq!(discriminator(&ours), Some(Mip0099::MAGIC));
    assert_eq!(discriminator(&theirs), Some(Mip0099::MAGIC));
    // …and the ledger deploys the sixteen-entry root compactc's JS cannot build.
    assert!(deploy::deploy(ours.clone()).data() == ours);
}
