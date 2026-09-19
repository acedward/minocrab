//! `bounded_ledger.compact` — a `Uint<0..1>` in LEDGER position, through
//! [`minocrab_std::v3::BoundedUint`] (M31, notes/version-bump.org "Bump 1 —
//! 2026-09-05" §"Family E", notes/bounded-integers.org §3).
//!
//! WHY THIS IS A SECOND FIXTURE BESIDE `bounded.compact`. compactc issue
//! #588 (fixed 0.33.108, "\[skip-changelog\] Fix alignment width for bounded
//! integers with maxval=0") gives a `Uint<0..1>` a ONE-byte alignment on the
//! Impact op when it sits in LEDGER position, where our prior pin
//! (0.33.0-rc.2) gave it zero — still writing one (always-zero) value in the
//! transcript either way. `bounded.compact`'s own `b1` circuit takes
//! `Uint<0..1>` as an ARGUMENT, and compactc's compiled `b1.zkir` is
//! byte-identical under both compilers: argument position never moved. Only
//! ledger position did, and no corpus artifact and no existing fixture puts
//! a `Uint<0..1>` there — hence this fixture, compiled fresh under the
//! PINNED (0.34.0) compactc.
//!
//! WHAT IT PINS, and against what. `bounded_differential`'s own ABI check
//! (`compactc_s_abi_agrees_with_the_leafs`) reads compactc's own `maxval`
//! out of `contract-info.json` and reconstructs the FAB alignment with
//! `uint_atom_bytes` — the SAME formula this crate's lowering uses — so a
//! wrong formula agrees with itself and that check can never see it. This
//! fixture's differential instead compares the actual Impact operand bytes
//! our lowering emits against the ones in the COMPILED `.zkir`, so a wrong
//! `uint_atom_bytes` fails it regardless of what our own formula believes.

use minocrab::v3::Circuit3;
use minocrab::Public;
use minocrab_std::v3::{Assumed, contract, label, BoundedUint, Disclose, Discloses, Ledger, LedgerCell};

label! {
    /// The one value this fixture ever discloses.
    X = "x";
}

/// `export ledger cell: Uint<0..1>;` — the whole ledger block.
#[derive(Ledger)]
pub struct BoundedLedger {
    pub cell: LedgerCell<BoundedUint<1, Public>>,
}

/// The contract's ledger block.
pub const BOUNDED_LEDGER: BoundedLedger = BoundedLedger::new();

#[contract]
impl BoundedLedger {
    /// `export circuit blWrite(x: Uint<0..1>): [] { cell = disclose(x); }` —
    /// the write whose Impact op carries the alignment byte the M31 probe
    /// showed moving (`0x00` -> `0x01`).
    #[circuit]
    pub fn bl_write(c: &mut Circuit3, x: BoundedUint<1>) -> Discloses<X> {
        let x = x.disclose_as::<X>(c);
        BOUNDED_LEDGER.cell.write(c, &x);
        Discloses::of(())
    }

    /// `export circuit blRead(): Uint<0..1> { return cell; }` — the mirror
    /// check a write-only fixture would miss: the read side carries the
    /// same alignment byte in its own Impact op.
    #[circuit(output = "cell")]
    pub fn bl_read(c: &mut Circuit3) -> Assumed<BoundedUint<1, Public>> {
        BOUNDED_LEDGER.cell.read(c)
    }
}
