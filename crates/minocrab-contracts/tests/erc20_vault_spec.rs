//! The erc20-vault PROPERTY HARNESS — spec ≡ circuit ≡ ledger ≡ compactc,
//! at scale, for all seventeen circuits.
//!
//! Each generated case is checked on five links
//! (notes/vault-optimization.org §"Binding circuit ≡ spec"):
//!
//! 1. **Acceptance agreement.** The spec is a total function; the circuit
//!    either accepts the witness or does not. They must agree, both ways.
//!    This is the link that catches "the circuit proves a different
//!    statement than we think".
//! 2. **PI-equality, re-anchored.** The preimage's transcript IS the
//!    reference op stream's `field_repr`, and the PI vector is exactly the
//!    transcript plus the skipped Impacts' zeros — length closure.
//! 3. **Ledger execution.** The same op stream runs through the real
//!    Impact VM against a real pre-state, and the `Effects` it produces
//!    must be exactly the ones the spec declared. That is the equality
//!    `ledger/src/semantics.rs:1441` enforces on chain.
//! 4. **Reference VM.** Every accepted run is re-validated by
//!    `IrSource::check`, so a MinoCrab simulator bug cannot hide a circuit
//!    bug.
//! 5. **compactc.** Every accepted case goes through the comparator against
//!    compactc's own artifact (external review §3.2 / §7.5).
//!
//! Case count: `PROPTEST_CASES=1000000 cargo test --release` for the
//! gating run; the default is deliberately modest because the settle
//! circuits simulate an in-circuit secp256k1 verification per case.

use midnight_transient_crypto::proofs::{ProofPreimage, Zkir};
use midnight_transient_crypto::repr::FieldRepr;
use minocrab_sim::v3::{assert_call_compatible, simulate};
use proptest::prelude::*;

mod vault;

use vault::artifact::Circuit;
use vault::exec::{self, PreState};
use vault::gen;
use vault::model::*;
use vault::prims::VmOp;
use vault::spec::{self, Effect, Outcome};

/// Would applying the spec's counter increments overflow a `u64`?
///
/// The vault has NO counter-overflow guard: `signetRequestNonce` at
/// `u64::MAX` still passes every circuit assert, and it is the Impact VM
/// that refuses (`OnchainProgramError::ArithmeticOverflow`) when `Addi`
/// runs. Circuit-level acceptance and ledger-level acceptance genuinely
/// differ there, so the harness models the split rather than papering
/// over it. (Reaching it needs 2^64 requests; recorded, not a finding.)
fn counter_would_overflow(effects: &[Effect], pre: &PreState) -> bool {
    effects.iter().any(|e| match e {
        Effect::CounterInc { field, by } => {
            let cur = match *field {
                SIGNET_REQUEST_NONCE => pre.request_nonce,
                INITIALISED => pre.initialised,
                _ => 0,
            };
            cur.checked_add(*by).is_none()
        }
        _ => false,
    })
}

/// The whole per-case check. Returns `Err(reason)` so proptest reports the
/// failing scenario rather than panicking inside a helper.
fn check_case(
    circuit: Circuit,
    outcome: &Outcome,
    pre: &PreState,
    self_addr: &[u8; 32],
    ops: &[VmOp],
    pi: &ProofPreimage,
) -> Result<(), String> {
    let ir = circuit.ir();
    // --- 1. acceptance agreement ---------------------------------------
    let run = simulate(&ir, pi);
    let circuit_accepts = run.is_ok();
    if circuit_accepts != outcome.accepts() {
        return Err(format!(
            "acceptance disagreement: spec {:?}, circuit accepts = {circuit_accepts}{}",
            outcome.guard(),
            match &run {
                Err(e) => format!(" ({e})"),
                Ok(_) => String::new(),
            }
        ));
    }
    let Ok(run) = run else {
        return Ok(());
    };

    // --- 4. reference VM on every accepted run --------------------------
    let skips = ir
        .check(pi)
        .map_err(|e| format!("simulator accepted but the reference VM rejected: {e}"))?;
    if skips != run.pi_skips {
        return Err("reference VM and simulator disagree on pi_skips".into());
    }

    // --- 5. compactc: the generated preimage through THE comparator -----
    assert_call_compatible(&ir, circuit.corpus(), pi);

    // --- 2. PI-equality, re-anchored to OUR op stream -------------------
    // `simulate` already checks each TAKEN Impact's inputs elementwise
    // against `pi.public_transcript_inputs`, which is `field_repr(ops)`;
    // what it does not check is that the transcript holds nothing BEYOND
    // what the circuit consumed. Length closure does: every transcript
    // element is consumed by exactly one taken Impact input, and every
    // skipped Impact contributes exactly its count of zeros.
    let mut expected = Vec::new();
    for op in ops {
        op.field_repr(&mut expected);
    }
    if expected != pi.public_transcript_inputs {
        return Err("the preimage's transcript is not field_repr of the reference ops".into());
    }
    let skipped: usize = run.pi_skips.iter().flatten().sum();
    let prefix = 1 + usize::from(run.comm_comm.is_some());
    if run.pis.len() != prefix + expected.len() + skipped {
        return Err(format!(
            "PI vector length {} != {prefix} + transcript {} + skipped zeros {skipped}",
            run.pis.len(),
            expected.len()
        ));
    }

    // --- 3. ledger execution: declared effects == computed effects ------
    match exec::run(pre, self_addr, ops) {
        Ok(ex) => spec::check_effects(outcome.effects(), pre, &ex),
        Err(e) => {
            if counter_would_overflow(outcome.effects(), pre) {
                Ok(())
            } else {
                Err(format!("the Impact VM rejected the reference op stream: {e}"))
            }
        }
    }
}

macro_rules! property {
    ($name:ident, $circuit:expr, $gen:expr, $spec:expr, |$s:ident| $env:expr) => {
        proptest! {
            #![proptest_config(gen::config())]
            #[test]
            fn $name($s in $gen) {
                let outcome = $spec(&$s);
                let env: &Env = $env;
                let r = check_case($circuit, &outcome, &$s.pre_state(), &env.self_addr, &$s.ops(), &$s.preimage());
                prop_assert!(r.is_ok(), "{r:?}");
            }
        }
    };
}

property!(initialise_matches_spec, Circuit::Initialise, gen::initialise(), spec::spec_initialise, |s| &s.env);
property!(approve_stata_matches_spec, Circuit::ApproveStata, gen::approve_stata(), spec::spec_approve_stata, |s| &s.env);
property!(approve_router_matches_spec, Circuit::ApproveRouter, gen::approve_router(), spec::spec_approve_router, |s| &s.env);
property!(start_deposit_matches_spec, Circuit::StartDeposit, gen::start_deposit(), spec::spec_start_deposit, |s| &s.env);
property!(complete_deposit_matches_spec, Circuit::CompleteDeposit, gen::complete_deposit(), spec::spec_complete_deposit, |s| s.env());
property!(start_withdraw_matches_spec, Circuit::StartWithdraw, gen::start_withdraw(), spec::spec_start_withdraw, |s| &s.env);
property!(complete_withdraw_matches_spec, Circuit::CompleteWithdraw, gen::complete_withdraw(), spec::spec_complete_withdraw, |s| s.env());
property!(refund_withdraw_matches_spec, Circuit::RefundWithdraw, gen::refund_withdraw(), spec::spec_refund_withdraw, |s| s.env());
property!(start_swap_matches_spec, Circuit::StartSwap, gen::start_swap(), spec::spec_start_swap, |s| &s.env);
property!(complete_swap_matches_spec, Circuit::CompleteSwap, gen::complete_swap(), spec::spec_complete_swap, |s| s.env());
property!(refund_swap_matches_spec, Circuit::RefundSwap, gen::refund_swap(), spec::spec_refund_swap, |s| s.env());
property!(start_supply_matches_spec, Circuit::StartSupply, gen::start_supply(), spec::spec_start_supply, |s| &s.env);
property!(complete_supply_matches_spec, Circuit::CompleteSupply, gen::complete_supply(), spec::spec_complete_supply, |s| s.env());
property!(refund_supply_matches_spec, Circuit::RefundSupply, gen::refund_supply(), spec::spec_refund_supply, |s| s.env());
property!(start_redeem_matches_spec, Circuit::StartRedeem, gen::start_redeem(), spec::spec_start_redeem, |s| &s.env);
property!(complete_redeem_matches_spec, Circuit::CompleteRedeem, gen::complete_redeem(), spec::spec_complete_redeem, |s| s.env());
property!(refund_redeem_matches_spec, Circuit::RefundRedeem, gen::refund_redeem(), spec::spec_refund_redeem, |s| s.env());

// ---- the deploy state (project 00002, notes/ledger-header.org) ------------------------

/// The vault's DERIVED deploy state is this harness's pre-state model at its
/// fresh values: the same segmented skeleton (`[[6 fields], [15 fields]]`)
/// and every field's default, by two independent routes — the model's
/// hand-written field list with `segment_of`, and `#[derive(Ledger)]`'s
/// layout with each slot type's initial value (`initial_state()`).
///
/// The two values that are the DEPLOYER's are supplied to both sides: the
/// sealed signer (a `LedgerField`, which the builder leaves Null) is set to
/// the model's cell, and the MPC key — which the model starts Null, since
/// every spec case initializes it — is given the value compactc's
/// `initialState` gives a fresh `Secp256k1Point` cell, its identity (pinned
/// against compactc's JS in `tests/ledger_deploy.rs`).
#[test]
fn the_derived_initial_state_is_the_models_fresh_state() {
    use midnight_onchain_state::state::StateValue;
    use minocrab::Public;
    use minocrab_contracts::erc20_vault::{Vault, VAULT};
    use minocrab_std::v3::{LedgerRepr, Secp256k1Point};
    use vault::prims::{bytesn_value, cell};

    let mut state = Vault::initial_state();
    state.set(
        VAULT.signet_signer.field_path(),
        cell(bytesn_value(32, &[0; 32])),
    );
    let StateValue::Cell(ref identity) = minocrab_ledger::stored_cell(
        Secp256k1Point::<Public>::atoms(),
        Secp256k1Point::<Public>::default_stored(),
    ) else {
        unreachable!("stored_cell builds a Cell")
    };
    let model = PreState {
        mpc_response_key: Some((**identity).clone()),
        ..PreState::default()
    };
    assert!(state.build() == model.state());
}
