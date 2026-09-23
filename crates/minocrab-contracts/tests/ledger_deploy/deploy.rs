//! DEPLOYING A BLOCK'S INITIAL STATE on the in-process Midnight 2.x ledger
//! (notes/ledger-header.org): `initial_state().build()` wrapped into a
//! `ContractState` and a `ContractDeploy`, put through the ledger's own
//! `Transaction::well_formed`, and applied to a fresh `LedgerState` — the
//! code the node runs, without the node. The same path as
//! `support::signet_call::deploy_singleton` and minocrab-publisher's
//! `tests/support`, built with the publisher's intent helpers; only the
//! fixed rng seed is test-only.
//!
//! The contract carries NO operations: a deploy must give every operation a
//! verifier key (`VerifierKeyNotSet`), and none of the tests that use this
//! needs one — they run circuits against the deployed `data` through
//! `QueryContext::query` (the executor), which is where a circuit meets the
//! ledger's state. What the deploy proves is that the ledger ACCEPTS the
//! state (its shape, its sixteen-entry roots, its sealed magic) under its
//! LIMITS, with a computable fee, and stores it verbatim. Only balancing is
//! off: nothing here can pay (see `unbalanced_strictness`).

use midnight_base_crypto::time::{Duration, Timestamp};
use midnight_coin_structure::contract::ContractAddress;
use midnight_ledger::semantics::{TransactionContext, TransactionResult};
use midnight_ledger::structure::{ContractDeploy, LedgerState};
use midnight_ledger::verify::WellFormedStrictness;
use midnight_onchain_runtime::context::BlockContext;
use midnight_onchain_state::state::{ContractState, StateValue};
use midnight_storage::db::InMemoryDB;
use minocrab_publisher::intent::{build_intent, preimage_tx};
use rand::rngs::StdRng;
use rand::SeedableRng;

/// The network the deploys are made on.
pub const NETWORK_ID: &str = "local-test";
/// The intent's segment (never 0, the guaranteed segment).
const SEGMENT: u16 = 1;

/// A deployed contract: the ledger after the deploy, and the address.
pub struct Deployed {
    pub ledger: LedgerState<InMemoryDB>,
    pub address: ContractAddress,
}

impl Deployed {
    /// The contract's state as the LEDGER holds it now.
    pub fn contract(&self) -> ContractState<InMemoryDB> {
        self.ledger
            .index(self.address)
            .expect("the deployed contract is in the ledger state")
    }

    /// Its `data`: the state tree the circuits index into.
    pub fn data(&self) -> StateValue<InMemoryDB> {
        self.contract().data.get_ref().clone()
    }
}

/// `data` as a contract's whole state: no operations, the default
/// maintenance authority, an empty balance — `ContractState::new`, which
/// wraps `data` in `ChargedState::new`.
pub fn contract_state(data: StateValue<InMemoryDB>) -> ContractState<InMemoryDB> {
    ContractState::new(
        data,
        midnight_storage::storage::HashMap::new(),
        Default::default(),
    )
}

/// The tagged serialization of [`contract_state`] — the JS oracle's
/// `data-only` form (`new ContractState()` with only `data` set, then
/// `serialize()`), so a byte comparison is a comparison of `data`.
pub fn data_only_bytes(data: StateValue<InMemoryDB>) -> Vec<u8> {
    let mut bytes = Vec::new();
    midnight_serialize::tagged_serialize(&contract_state(data), &mut bytes)
        .expect("a contract state serializes");
    bytes
}

/// The ledger's default strictness with BALANCING off, and nothing else.
///
/// Balancing is off because nothing here can pay a DUST fee: the workspace
/// has no wallet, so a deploy cannot carry the fee inputs that balancing
/// asks for (the singleton's deploy gate does the same). With balancing
/// off, `well_formed` also swallows an error from the fee calculation, so
/// the fee is computed separately below and must succeed.
///
/// LIMITS stay ON. `enforce_limits` (the default) is the transaction-size
/// check: `well_formed` refuses a transaction whose serialized size exceeds
/// the ledger's `transaction_byte_limit`. The block limits and the
/// time-to-dismiss bound are not `enforce_limits`'s: they come from the
/// separate `fees(params, true)` call in `deploy` below
/// (`BlockLimitExceeded`, `OutsideTimeToDismiss`), which must be `Ok`. Both
/// apply to every deploy here, the sixteen-entry roots and the
/// 256-own-field block included.
fn unbalanced_strictness() -> WellFormedStrictness {
    let mut s = WellFormedStrictness::default();
    s.enforce_balancing = false;
    assert!(
        s.enforce_limits,
        "the ledger's default strictness enforces limits"
    );
    s
}

/// `ContractDeploy` `data` into a fresh ledger, `well_formed` it and `apply`
/// it. Panics, with the ledger's own error, if either refuses.
pub fn deploy(data: StateValue<InMemoryDB>) -> Deployed {
    let tblock = Timestamp::from_secs(0);
    let ledger: LedgerState<InMemoryDB> = LedgerState::new(NETWORK_ID);
    let mut rng = StdRng::seed_from_u64(0x0002_0de9);
    let deploy = ContractDeploy::new(&mut rng, contract_state(data));
    let address = deploy.address();
    let intent =
        build_intent(&mut rng, vec![], tblock + Duration::from_secs(3600)).add_deploy(deploy);
    let tx = preimage_tx(NETWORK_ID, SEGMENT, intent);
    // The fee the node would charge: computable (no block-limit or
    // time-to-dismiss error), though nothing pays it here.
    tx.fees(&ledger.parameters, true)
        .unwrap_or_else(|e| panic!("the deploy's fee cannot be computed: {e:?}"));
    let vtx = tx
        .well_formed(&ledger, unbalanced_strictness(), tblock)
        .unwrap_or_else(|e| panic!("the deploy is not well formed: {e:?}"));
    let context = TransactionContext {
        ref_state: ledger.clone(),
        block_context: BlockContext {
            tblock,
            ..BlockContext::default()
        },
        whitelist: None,
    };
    let (after, result) = ledger.apply(&vtx, &context);
    assert!(
        matches!(result, TransactionResult::Success(_)),
        "the deploy must apply: {result:?}"
    );
    Deployed {
        ledger: after,
        address,
    }
}
