//! LEDGER HEADERS (notes/ledger-header.org): a STANDARD claims `root[0]`,
//! the first block of a contract's ledger, and its 32-byte [`LedgerHeader::MAGIC`]
//! sits at the first leaf, where a generic reader finds it without any
//! per-contract code.
//!
//! A standard is a type its author publishes once:
//!
//! ```
//! use minocrab::Public;
//! use minocrab_std::v3::{pad32, Ledger, LedgerCell, LedgerCounter, LedgerHeader, Uint};
//!
//! /// Magic-only: a Cell at `[0]`.
//! #[derive(LedgerHeader)]
//! struct Mip0099;
//! impl LedgerHeader for Mip0099 {
//!     const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
//! }
//!
//! /// Any contract embeds it as one field, declared anywhere.
//! #[derive(Ledger)]
//! struct Counter {
//!     value: LedgerCell<Uint<64, Public>>,
//!     std: Mip0099,
//!     count: LedgerCounter,
//! }
//! const C: Counter = Counter::new();
//!
//! assert_eq!(C.std.magic().field_path().as_slice(), &[0]);
//! assert_eq!(C.value.index(), 1); // compactc's [0], one root slot along
//! assert_eq!(C.count.index(), 2);
//! ```
//!
//! THE RULE, all of it:
//!
//! - `#[derive(LedgerHeader)]` gives the type `LedgerWidth::WIDTH = 0` and
//!   `PLACEMENT = Placement::root_header::<Self>()`. The block's width
//!   sums therefore leave it out, and `#[derive(Ledger)]` lays the body out
//!   HEADED ([`super::BlockLayout::headed`]): compactc's segmentation of the
//!   other fields alone, at a frozen fifteen, every path's first element + 1.
//!   Where the standard is declared does not matter; depths are compactc's.
//! - A UNIT struct is magic-only: a Cell at `[0]`. A struct with NAMED
//!   fields is an Array at `[0]` of `1 + n` entries: the magic at `[0, 0]`,
//!   field `i` at `[0, i + 1]`, `n <= 15` (the ledger's sixteen). Each field
//!   is a single-field std slot ([`HeaderField`]) and reads and writes
//!   through its ordinary typed API.
//! - The magic is not a field. It has no write and no reset: [`Magic`]
//!   carries only its path, and its value comes from the deploy state.
//! - One standard per block (E0080); an all-zero magic is E0080 (it is what
//!   an unset `Bytes<32>` cell holds, so no reader could tell it from none).
//!   Both hold however the standard is written: `Placement::root_header`
//!   is the only way to claim `root[0]` and checks the magic,
//!   `#[derive(Ledger)]` counts the standards and checks each one's zero
//!   `WIDTH` ([`super::standards`]), and `StateBuilder::magic` and
//!   [`super::implements`] check the magic again for their `S`. A standard
//!   hidden inside a hand-written group slot is the one case no type can
//!   see; its block's `initial_state()` refuses it by name (see
//!   `LedgerWidth`).
//!
//! A magic is a CLAIM, not proof: the deploy state is the deployer's, and a
//! maintenance authority can install a circuit that writes `root[0]`.
//! Pair it with a verifier-key check where it matters.

use super::ledger::{BlockLayout, FieldPath, LedgerWidth, Placement};

/// A STANDARD: a type that claims `root[0]` of every ledger block that
/// embeds it, and the 32 bytes a reader finds there.
///
/// Written by hand beside `#[derive(LedgerHeader)]`, which does the rest
/// (the width, the placement, the constructors and the checks):
///
/// ```
/// use minocrab_std::v3::{pad32, LedgerHeader};
///
/// #[derive(LedgerHeader)]
/// struct Mip0099;
/// impl LedgerHeader for Mip0099 {
///     const MAGIC: [u8; 32] = pad32(b"mip-0099:ledger-header[v1]");
/// }
/// ```
///
/// The placeholder above is the tests' and examples' (a future MIP fixes
/// the real format); do not deploy it outside test networks.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is laid out as a ledger standard but names no magic",
    label = "`#[derive(LedgerHeader)]` needs `impl LedgerHeader for {Self}`",
    note = "write `impl LedgerHeader for {Self} {{ const MAGIC: [u8; 32] = pad32(b\"…\"); }}` \
            beside the derive: the magic is the standard's own constant, so the \
            standard's author states it once"
)]
pub trait LedgerHeader: LedgerWidth {
    /// The discriminator at the first leaf (`[0]`, or `[0, 0]` for a
    /// standard with fields). Not all zero — E0080 wherever the standard is
    /// used as one: its placement (`Placement::root_header`), its deploy
    /// state (`StateBuilder::magic`), a reader's `implements`, and the
    /// derive's own check.
    const MAGIC: [u8; 32];
}

/// `s` NUL-padded to 32 bytes — Compact's `pad(32, "…")`, in `const`, for
/// writing a [`LedgerHeader::MAGIC`]. E0080 when `s` is longer than 32.
///
/// The ledger stores a `Bytes<32>` cell with its trailing zero bytes
/// stripped; a reader pads it back, so the value round-trips.
pub const fn pad32(s: &[u8]) -> [u8; 32] {
    assert!(
        s.len() <= 32,
        "a ledger magic is 32 bytes: pad32 takes at most 32"
    );
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < s.len() {
        out[i] = s[i];
        i += 1;
    }
    out
}

/// A standard's MAGIC as a slot: where it is, and nothing to write it with.
///
/// Returned by the `magic()` method `#[derive(LedgerHeader)]` gives the
/// standard. No `write`, no `reset_to_default`: the value is the deploy
/// state's, so no circuit written against the typed API can change it.
/// A circuit that needs the value uses the constant
/// (`<S as LedgerHeader>::MAGIC`); there is no in-circuit read here.
#[derive(Clone, Copy)]
pub struct Magic {
    path: FieldPath,
}

impl Magic {
    /// The magic at `path` — `[0]` or `[0, 0]`, and nowhere else: a
    /// standard is `root[0]`, a Cell there or an Array whose entry 0 is the
    /// magic. For the derive's expansion (and a hand-written standard's
    /// `magic()`), not for call sites. E0080 in a `const`, a panic naming
    /// the rule otherwise.
    #[doc(hidden)]
    pub const fn at_path(path: &[u8]) -> Self {
        assert!(
            matches!(path, [0] | [0, 0]),
            "a standard's magic is at [0] (a magic-only standard) or [0, 0] (one with fields): \
             a standard claims root[0], and its magic is the first leaf there"
        );
        Magic {
            path: FieldPath::of(path),
        }
    }

    /// The magic's path: `[0]` for a magic-only standard, `[0, 0]` for one
    /// with fields — whatever the contract.
    pub const fn field_path(&self) -> FieldPath {
        self.path
    }
}

pub(super) mod sealed {
    /// Sealing [`super::HeaderField`]: the std slot types, and no
    /// downstream others.
    pub trait HeaderField {}
}

/// The slot types a standard may own besides its magic: the eight
/// single-field std slots (Cell, Counter, Map, Set, List, MerkleTree,
/// HistoricMerkleTree, and the untyped `LedgerField`). Sealed.
///
/// A group slot has more than one field and a path of its own layout, and
/// a `Signet`-reading slot needs the block's Signet — none of them fits one
/// entry of the header Array, so each is a missing impl here.
#[diagnostic::on_unimplemented(
    message = "`{Self}` cannot be a field of a ledger standard",
    label = "a standard's fields are single-field std ledger slots",
    note = "a standard is one Array at root[0] — the magic, then one entry per field — so \
            each field is ONE ledger field: a LedgerCell, LedgerCounter, LedgerMap, \
            LedgerSet, LedgerList, LedgerMerkleTree, LedgerHistoricMerkleTree or \
            LedgerField. A group slot (Signet, Pending, Fired, Outbox, Stream) or another \
            standard belongs in the contract's body instead"
)]
pub trait HeaderField: LedgerWidth + sealed::HeaderField {}

/// The magic check: E0080 on 32 zero bytes. `#[derive(LedgerHeader)]`
/// emits it, and `Placement::root_header`, `StateBuilder::magic` and
/// `implements` run it on their standard in an inline `const`.
#[doc(hidden)]
pub const fn assert_magic(magic: &[u8; 32]) {
    let mut i = 0;
    let mut zero = true;
    while i < 32 {
        if magic[i] != 0 {
            zero = false;
        }
        i += 1;
    }
    assert!(
        !zero,
        "a standard's MAGIC is all zero bytes: that is what an unset `Bytes<32>` cell \
         holds, so a reader could not tell this standard from a contract with none. \
         Give it a non-zero value, e.g. pad32(b\"…\")"
    );
}

/// `#[derive(LedgerHeader)]`'s field check, over every field's
/// `LedgerWidth`: one ledger field each, no Signet response kind, and not a
/// standard. E0080 otherwise. (The [`HeaderField`] bound says the same as a
/// missing impl; this is the backstop in the width terms the layout uses.)
#[doc(hidden)]
pub const fn assert_header_fields(widths: &[usize], kinds: &[&[u8]], placements: &[Placement]) {
    let mut i = 0;
    while i < widths.len() {
        assert!(
            widths[i] == 1,
            "a standard's fields are single-field ledger slots: one field of this \
             standard is a group (WIDTH != 1) or another standard (WIDTH 0)"
        );
        assert!(
            kinds[i].is_empty(),
            "a standard's fields settle no Signet response kind: a Signet slot needs \
             the block's Signet, which lives in the body"
        );
        assert!(
            !placements[i].is_root_header(),
            "a standard cannot contain another standard: root[0] has one owner"
        );
        i += 1;
    }
}

/// The derive's per-field bound, as a `const` item: E0277 when the field's
/// type is not a [`HeaderField`], with that trait's message.
#[doc(hidden)]
pub const fn header_field<T: HeaderField>() {}

/// A standard is at `root[0]` only in a headed layout: `#[derive(Ledger)]`
/// always gives one when a standard is present, so this fires only for a
/// hand-built `at_layout` call. E0080 in a `const`.
#[doc(hidden)]
pub const fn assert_headed(layout: BlockLayout) {
    assert!(
        layout.is_headed(),
        "a standard is placed only in a headed layout: its root[0] would collide \
         with the body's first field under compactc's. Declare it in a \
         #[derive(Ledger)] block, which gives the block a headed layout"
    );
}
