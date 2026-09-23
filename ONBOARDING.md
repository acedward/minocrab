# Onboarding

The day-one path, a map of the `notes/`, and the first hour's jargon.
Everything here exists elsewhere in more depth; this is the order to read
it in.

## Day one, in order

1. [README.md](README.md) — what MinoCrab is, side-by-side with Compact,
   the feature tour, the stability tiers.
2. [VERIFICATION.md](VERIFICATION.md) — where the confidence comes from:
   which artifact is warranted by what (PI-equality, spec harness,
   byte-gates), suite by suite.
   Then [TRUST.md](TRUST.md) — where the suites stop: the source files a
   human must read, with a read order and a time budget.
3. [notes/ledger-abi.org](notes/ledger-abi.org) §6 — the equivalence
   criterion everything hangs off: same typed I/O plus identical
   `pis`/`pi_skips` on a shared `ProofPreimage`, instruction streams free
   to differ.
4. [notes/architecture.org](notes/architecture.org) — the layer map
   (ZKIR bindings → IR builder → eDSL → stdlib → simulator).
5. [notes/review-queue.org](notes/review-queue.org) — what has had human
   eyes, and what is still agent-only.
6. [CONTRIBUTING.md](CONTRIBUTING.md) — before your first change.

## The notes, mapped — read this when …

| note | read when |
|---|---|
| [api-safety-survey.org](notes/api-safety-survey.org) | you wonder what a malicious prover could do that tests can't see — the survey method + findings A1..B4 |
| [architecture.org](notes/architecture.org) | you need the crate/layer map |
| [benchmark.org](notes/benchmark.org) | you want the working history behind BENCHMARK.md's numbers |
| [borsh-format.org](notes/borsh-format.org) | you touch the wire format — records, attested outputs, the kind byte, the TS decoder |
| [bounded-integers.org](notes/bounded-integers.org) | you touch `Uint<0..n>` / `BoundedUint` |
| [builtin-lowering.org](notes/builtin-lowering.org) | you need how a Compact builtin lowers (FAB limbs, `Bytes<32>` = `[hi, lo]`, …) |
| [coin-arms-nested-adts.org](notes/coin-arms-nested-adts.org) | you touch `insertCoin`/`pushFrontCoin` or nested ledger ADTs |
| [compact-findings.org](notes/compact-findings.org) | you hit something odd in compactc itself — known upstream quirks |
| [const-generics.org](notes/const-generics.org) | you size a circuit family by const generics (and the deliberate skips) |
| [contract-api.org](notes/contract-api.org) | you touch `#[circuit]`, `CircuitArg`, disclosure declarations — the M9 design of record |
| [corpus-sources.org](notes/corpus-sources.org) | you wonder where a corpus artifact comes from or how to bump one |
| [ergonomic-parity.org](notes/ergonomic-parity.org) | you wonder why opt-lineage and port share one vocabulary (the self-address cache) and why the forks don't collapse |
| [external-review-triage.org](notes/external-review-triage.org) | you want the triage of the 2026-08 external review |
| [formal-verification-options.org](notes/formal-verification-options.org) | you touch Kani/Lean — the staging, the Agda ground truth, the R4 record |
| [interface-crates.org](notes/interface-crates.org) | you touch `#[interface]` or the generated interface crates |
| [ir-passes.org](notes/ir-passes.org) | you write or judge an IR pass — the accept/reject lists and why CSE/DCE are rejected |
| [kernel-tokens.org](notes/kernel-tokens.org) | you touch the kernel primitives or token stdlib |
| [lean-port.org](notes/lean-port.org) | you touch the Lean proofs (`crates/*/lean/`) — the construct inventory, the model-vs-extraction decision, the limitations discussion |
| [ledger-abi.org](notes/ledger-abi.org) | you touch anything on-chain-facing — state layout, Impact framing, the comm commitment |
| [ledger-adts.org](notes/ledger-adts.org) | you touch List/Set/Map/MerkleTree lowering |
| [ledger-header.org](notes/ledger-header.org) | you embed a standard (`#[derive(LedgerHeader)]`), build a deploy state (`initial_state()`), or read a contract's discriminator — fork work, decisions listed for review |
| [library-api.org](notes/library-api.org) | you touch the public surface — the tier boundary, the Pass contract, the CLI |
| [manager-port.org](notes/manager-port.org) | you look at the AA-manager contract |
| [midnight-code-reuse.org](notes/midnight-code-reuse.org) | you wonder which upstream crate to reuse for something |
| [newtype-survey.org](notes/newtype-survey.org) | you add a same-shaped-different-meaning value — the adopted/refused families |
| [opaque-bridging.org](notes/opaque-bridging.org) | you touch `Opaque<'ts-type'>` or the curve-point leaves |
| [readme-research.org](notes/readme-research.org) | you rewrite the README |
| [review-queue.org](notes/review-queue.org) | you want to know what a human has actually reviewed |
| [signet-corpus.org](notes/signet-corpus.org) | you touch the sig-net contracts — the corpus inventory |
| [taint-lint.org](notes/taint-lint.org) | the taint lint fires, or you extend its marking rules |
| [vault-optimization.org](notes/vault-optimization.org) | you touch the optimized vault — every avenue, measured |
| [vault-vocabulary.org](notes/vault-vocabulary.org) | you rename anything in the vault — the misfiling incident that names carry |
| [version-bump.org](notes/version-bump.org) | anything fires after a pin moves — THE DRIFT TAXONOMY |
| [zkir.org](notes/zkir.org) | you need the ZKIR/toolchain lay of the land, release channels, hashes |

## Glossary, for the first hour

- **PI-equality** — two artifacts accept the same `ProofPreimage` with
  identical public-input streams (`pis`/`pi_skips`). The strongest
  warrant in the repo: "same statement". Instruction streams may differ.
- **FAB** — field-aligned binary, Midnight's encoding of typed values as
  field-element *limbs*. A `Bytes<32>` is two limbs `[hi, lo]` (1 + 31
  bytes); a `bytes n` atom is `ceil(n/31)` limbs, leftover first.
- **The four vault artifacts** — `erc20_vault` (the compat **port**,
  PI-equal to compactc: the differential warrant), `_opt` (M10
  optimized: own statement, spec-harness warrant), `_borsh` (opt on the
  M11 wire format), `_modern` (the showcase twin, byte-identical to
  borsh). Four forks in lockstep is a *feature*: each link in
  `compactc ≡ port ≡ opt ≡ borsh ≡ modern` is a separately-asserted
  warrant, and the divergence ledgers make leaving a link's coverage an
  explicit, reviewed edit.
- **Zero movement** — the serialized ZKIR of every circuit is
  byte-identical across a change. The default expectation for API work;
  proven by dump comparison, not claimed.
- **The fold** — `fold_immediate_copies`: a `Copy` of an immediate is a
  rename, folded before instruction-for-instruction comparison so both
  sides are normalised the same way.
- **k / rows** — Halo2 cost: `rows` is occupied rows, `k` is the padded
  table's log2 size. **Prove time and RAM track 2^k, not rows** — a row
  cut only pays when it crosses a power-of-two boundary.
- **Impact** — Midnight's on-chain VM; circuits emit its op stream as
  guarded public inputs, which the ledger re-executes and checks.
- **Guarded / `_under`** — an op under a branch condition: the guard is
  an operand of the Impact instruction, and a false guard absorbs zeros.
- **The taint lint** — the static instrument for hash-preimage limbs
  that no honest-input test can check. Its baseline is frozen; new
  findings fail CI.
- **M-numbers** (M0..M25) — milestones, in `milestones.org`; closed ones
  are summarized there with pointers into `notes/`. A citation like
  "M10 rung i" means that milestone's recorded decision.
- **`.bytes()`** — the one way OUT of a value-meaning newtype; grep for
  it to find every place a distinction is deliberately dropped.
