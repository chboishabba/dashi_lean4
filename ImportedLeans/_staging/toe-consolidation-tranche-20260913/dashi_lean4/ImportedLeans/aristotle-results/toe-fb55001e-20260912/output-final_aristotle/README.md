This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# DASHI all-TOE cutset — 2026-08-21

This is a read-only synthesis bundle assembled from the current local sources.

* `Agda/` contains the complete active DASHI corpus, Cubical library, and the
  `Monster/`, `MDL/`, and root Agda modules. It includes the current `Everything`
  tranches and the Cuisine material at `Agda/DASHI/Culture/Cuisine/`.
* `Lean/` contains the current canonical Lean checkout, including the completed
  `Synthesis/` spine returned by Aristotle project `bf6411b6-e62e-4ce1-8ede-7772440fd988`.

*(Superseded, 2026-09-10.)* The header above describes the original 2026-08-21
cutset, when the Yang--Mills and Navier--Stokes lanes were excluded by
path/name filter. That policy was retired by the full-source round and is not
in force: every lane -- YM, NS, RH, Monster/Moonshine/Base369/J-invariant,
DOI/QID/Dewey/Wikidata, law, ecology, optics and the rest -- is now indexed and
retained, with status and missing edges recorded rather than the path dropped.
See `SPINE_CONSOLIDATION_20260910.md`.

No claim should be inferred from conceptual names:
trace imports, definitions, theorem statements, proof terms, assumptions, and
any `postulate`/`axiom`/`sorry`-like placeholders before treating a connection
as established.

The first requested focus is food/cookery as a concrete cross-domain test case,
while retaining the full non-YM/non-NS corpus for genuine dependency discovery.

## Reports

* `NS_LATEST_TRANCHE_LINEAGE.md` — **intake, index and lineage of the
  2026-09-12 NS Aristotle source tranche**
  (`ns-latest-source-tranche-to-toe-20260912.tar.gz`, sha256 `138da4e92958…`,
  21 730/21 730 `SHA256SUMS` entries verified `OK`, manifest and payload equal,
  source-only). The NS-relevant payload is preserved verbatim under
  `Provenance/ns-latest-20260912/payload/`. Contains: the delivery check, the
  per-path delta against this corpus (17 905 identical, 1 592 divergent,
  2 231 absent), the clean round trip of the ten divergent Lean aggregates, the
  exact consumers and transports of `SpineRateBlockAdapter`,
  `GramConsumerFactorisation`, `SlotKernelAntiParallel` and
  `RateBlockGramBound`, the bidirectional lineage map against the public
  forced-blowup corpus and the DASHI Agda lane, and seven exactly-stated open
  seams. Indices: `NS_LATEST_INDEX.csv`, `NS_LATEST_DECLS.csv`,
  `NS_LATEST_IMPORT_EDGES.csv`, `NS_LATEST_DELTA.csv`, `NS_LATEST_LINEAGE.csv`,
  `NS_LATEST_SUMMARY.json`; regenerate with `scripts/ns_latest_index.py`.
  The delivered sources were not built (the NS lane is not on this project's
  build surface); the one new spine module written on the back of that intake,
  `Lean/Spine/RateBlockSchurPiCarrier.lean` — the `WithLp.toLp 2` transport that
  puts the rate-block Schur kernel on the plain `Fin n → ℂ` carrier the NS lane
  uses — is built and axiom-audited here.
* `NS_OPENAI_ARCHAEOLOGY.md` — **intake and proof archaeology of the public
  OpenAI `NavierStokesAndEuler` Lean proof** (repository
  <https://github.com/openai/NavierStokesAndEuler>, pinned commit
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, archive sha256 `d1daa3dc44ed…`,
  2671/2671 `SHA256SUMS` entries verified `OK`, manifest and payload equal).
  Payload preserved verbatim under `Provenance/openai-ns-20260912/`. Contains:
  the full source index (`NS_OPENAI_INDEX.csv`, `NS_OPENAI_DECLS.csv`,
  `NS_OPENAI_IMPORT_EDGES.csv`), the endpoint derivation chains, the scope table
  separating the upstream forced-blowup result (Clay C/D) from the DASHI
  global-regularity programme, a chronological archaeology of the DASHI Lean and
  Agda NS lanes (the enstrophy/BKM chain, the scalar Bony donors, the
  R145/R180/R580–R585 lineage, the Round-504 terminal cutset, the 2026-09-09
  rate-block Gram worker result), the two common carriers now owned in
  `Lean/Spine/GronwallComparison.lean` and `Lean/Spine/GramLedger.lean`, and the
  exact remaining obligations.  Regenerate the indices with
  `scripts/ns_openai_index.py` and `scripts/ns_lineage_map.py`.
* `SPINE_CONSOLIDATION_20260910.md` — **intake of the combined Lean + Agda
  consolidation tranche** (Lean donor `c5b9a072…`, Agda donor `a866c675…`,
  archive sha256 `b532063341a2…`, 20 074 manifest entries, all 20 076
  `SHA256SUMS` entries verified `OK`). Per-path disposition (15 930 + 187
  identical, 3 913 adopted, 43 divergences where the local version is retained
  and the donor version preserved verbatim under
  `Provenance/spine-20260910/`, 1 staged build artefact), the post-intake
  dependency frontier for both languages, declarations shared across three or
  more lanes, the two byte-duplicate JMD modules this tranche creates, and six
  concrete proposed `Spine` adapters. No lane excluded; no build run, by
  instruction. Indices: `SPINE_INDEX.csv`, `SPINE_IMPORT_EDGES.csv`,
  `SPINE_DIVERGENCES.csv`, `SPINE_FRONTIER.csv`, `SPINE_FRONTIER_POST.csv`,
  `SPINE_SHARED_DECLS.csv`, `SPINE_SHARED_DECLS_FOCUSED.csv`,
  `SPINE_INTAKE_LEDGER.csv`, `SPINE_INDEX_SUMMARY.json`.

* `TOE_XPOLLINATION_FULL_SOURCE_20260910.md` — **the full-source
  cross-pollination intake** (donor `1d3cb03c…`, archive sha256
  `8a48678a…`, 15,952 Agda payload entries plus the NS worker supplement, all
  15,958 checksums verified). Supersedes the topic-filtered 2026-09-09 policy:
  every path is indexed and preserved regardless of lane. 1,822 modules
  adopted, 1,752 reconciled, 28 conflicts kept with reasons; unresolved import
  edges fall from 241 in 67 files to 153 in 34; the ten previously missing
  generic `DASHI.Core.*BidiExact` kernels arrive, making all ten Aristotle
  reciprocal-garden owners dependency-complete. Indices in `XPOLL_INDEX.csv`,
  `XPOLL_IMPORT_EDGES.csv`, `XPOLL_LEDGER.csv`, `XPOLL_DIVERGENCES.csv`,
  `XPOLL_FRONTIER.csv`, `XPOLL_MISSING_TARGETS.csv`, `XPOLL_HUBS.csv`,
  `XPOLL_SHARED.csv`; additive rollup in
  `Agda/DASHI/EverythingCrossPollination20260910.agda`; NS worker files under
  `Provenance/ns_worker_result/`. The round's one machine-checked result is
  `Lean/Spine/RateBlockSchur.lean`. No Agda kernel receipt, no Clay/YM/NS/RH
  closure.

* `TOE_TRANCHE_INTAKE_20260909.md` — **intake of the combined NS/YM/RH/TOE
  Agda source handoff** (donor commit `7f08c070…`, 6 758 manifest entries, all
  checksums verified): what was adopted (129 new + 90 reconciled non-YM/NS
  modules), what was reviewed and refused and why, the mechanical import
  receipt (241 unresolved edges before and after — unchanged), and the honest
  frontier. Per-path provenance in `TOE_TRANCHE_INTAKE_20260909_LEDGER.csv`;
  the adopted set is rolled up additively by
  `Agda/DASHI/EverythingTrancheIntake20260909.agda`. No Agda kernel receipt is
  claimed, and no Clay, Yang–Mills or Riemann result is asserted.

* `TOE_ARISTOTLE_RECIPROCAL_GARDEN.md` — **the Aristotle/Wikidata reciprocal
  garden**: the integration of the Aristotle archive under
  `Lean/DASHI/output-final_aristotle` (now built as the `AristotleArchive`
  library), the nine sorry-free Lean owners under
  `Lean/Integration/Kernel/Aristotle/` that instantiate the generic garden
  kernels on the archive's real Wikidata semantics — truthy statement families,
  snak absence versus `novalue`, `full ⊇ sourced ⊇ reliable`, sound-but-not-
  complete pruned type modules, strand-indexed promotion, coverage schemas,
  coverage-residual salience and content/revision identity — the Agda reverse
  owners (source only, no Agda kernel receipt), the dependency map and the
  frontier.
* `TOE_KERNEL_CONSOLIDATION.md` — **the shared inference kernel**: the residual
  refinement calculus, discriminating probes, the four merge modes, the
  telemetry/authority constraints, selective reopening and the closed loop with
  its termination theorem, plus the thin instances (including the proof that the
  continuous parameter-region lane *is* the kernel's iterated refinement).  Lean
  sources under `Lean/Integration/Kernel/`.
* `TOE_CONSUMER_QUOTIENT.md` — **the consumer-quotient round**: the Agda
  refresh taken from the latest handoff bundle (non-YM/NS only, with counts),
  the new `Integration.Kernel.Quotient` core — consumer indistinguishability,
  descent as refinement, strict refinement, consumer-relative inverse and exact
  reopening — and the five thin instances built on it (finite frontier orders,
  point-in-time fibres, candidate-versus-admitted objects, situated valuation,
  and announcement-versus-evidence-stage provenance), with the honest frontier
  of what remains unproved.  Lean sources `Lean/Integration/Kernel/Quotient.lean`
  and `Lean/Integration/Kernel/Instances/`.
* `TOE_BASE369_HEISENBERG.md` — the Base369/Monster lane: the finite Heisenberg
  group over `𝔽₃ⁿ` with proved group laws, symplectic nondegeneracy and centre,
  the Schrödinger module with its Fourier point projector, the irreducibility
  theorem, and the explicit refusal that dimension equality implies
  representation identity.  Lean sources `Lean/Integration/Base369Heisenberg.lean`
  and `Lean/Integration/Base369Schrodinger.lean`.
* `TOE_GLOBAL_MAP.md` — the corpus-wide integration map: Agda import/dependency
  provenance, the four-level classification of every cross-domain claim with its
  Lean witness, the proved boundaries and the record/Bool sockets, and the
  frontier of exact remaining obligations. Its machine-checked counterpart is
  `Lean/Integration/Registry.lean`; the spine root is `Lean/Integration.lean`.
* `CUISINE_DEPENDENCY_MAP.md`, `CUISINE_FOUR_LEVEL_MAP.md`,
  `CUISINE_TOE_TRANSPORT.md` — the cuisine probe.
* `RH_BRIDGE_REPORT.md`, `SPINE_REPORT.md` — the analytic probe and the common
  spine.
* `TOE_WELD_REPORT.md`, `TOE_GAUGE_DESCENT_REPORT.md` — the welded observer
  schema, and gauge reduction with observational descent.
* `TOE_PRESENTATION_INDEPENDENCE_REPORT.md` — the latest tranche: enumeration
  independence and the closed form of the transverse certificate, composite
  gauge redundancy as preimage-subgroup algebra, sufficiency (tower-relative and
  intrinsic), the SSP observational threshold, orbit–stabilizer residual bounds,
  certificate-pays-defect budgets, the Schur-complement core, the
  invariant/equivariant/gauge-sensitive consumer classification, and the
  exact/approximate intertwiner tiers — with the exact remaining obligations.
* `TOE_COMMON_OWNERS_REPORT.md` — the common-owner refactor: one owner for the
  commuting square (`Integration.StructureMorphism`), finite reindexing owned
  once (`Spine.FiniteReindex`), the first non-finite `U(1)` gauge instance, the
  certified-margin/relative-defect/normalisation gate, the typed residual
  taxonomy, path transport and monotone obstructions, equivariance obstructions,
  multiscale law descent, commutator observability and its descent level, the
  base/fibre/transport/measurement bundle, field-controlled dynamics and
  attractors, contrast and two-boundary conditioning — with the dependency map
  and the exact remaining obligations.

## TOE sewing round — where to start

| document | contents |
|---|---|
| `TOE_SEWING_MAP.md` | the main report: owner set, the seven-class taxonomy, rows 1–24 lane by lane, collected negatives, coverage, and the frontier of next obligations.  Row counts quoted there are compiler evaluations of `Integration.SewingRegistry.kindCensus`, not hand-maintained numbers |
| `TOE_LEVEL_II_SPINE.md` | the Level-II consolidation (rows 61–69): the four reusable owners — consumer-indexed adequacy, the collision owner, separability/contrast, language-indexed reachability — the eight welds onto them, the dependency map, and the exact remaining obligations |
| `TOE_LEVEL_II_DISCHARGE.md` | the Level-II discharge and stress-test tranche (rows 70–81): welds 62/63/67 sharpened, the fibre-averaging pipeline classified arrow by arrow, three independent corpus tables discharging one rectangle obstruction, the pipeline/repair dichotomy, exhaustiveness on a proof-producing carrier, and the frontier extractor |
| `TOE_LEVEL_III_PROBE.md` | the claim-transport probe: when may a locally valid claim cross a stage boundary?  The generic warrant and its negative, four source-exact lanes (formalisation, authority, empirical, entitlement), the registry read as a transition system on classes, and the verdict that every composition failure found reduces to the four frozen Level-II owners |
| [`TOE_EVIDENCE_GOVERNANCE.md`](TOE_EVIDENCE_GOVERNANCE.md) | the evidence-governance round: the claim-transport geometry interface and its reconciliation theorem, evidence-indexed promotion with an executable gate proved closed on all sixteen open rows, the free-field/Boolean-sink audit, the mirror drift guard, the derived (advisory) frontier queue, the falsification probe of non-functional transport shapes, and the new prediction axis (envelopes, tightening, status propagation with no epistemic laundering) |
| [`TOE_EXPERIMENT_CALCULUS.md`](TOE_EXPERIMENT_CALCULUS.md) | the executable experiment calculus (Stage 3): the typed quantity/law graph and its rejection of dimensionally ill-formed sums, covariance propagation and the three-way uncertainty budget that never collapses to one number, protocols as interventions bridged to the reachability owner, risk as a consumer of the same state model, measurement-value analysis with a minimality theorem, failure localisation and repair, data-driven model selection under a declared instrument tolerance, the `ExperimentSpec → ExperimentPrediction` compiler with its guarantees, and two independent domain instances (lithium electrochemistry, thermal diffusion) run through the unchanged calculus — with the dependency map and the exact remaining obligations.  Lean: `Lean/Integration/Experiment/` |
| [`TOE_STAGE4_INFERENCE.md`](TOE_STAGE4_INFERENCE.md) | continuous deterministic scientific inference (Stage 4): continuously parameterised hypothesis families with surviving parameter regions, monotone evidence and set-valued prediction/risk envelopes proved to be closed intervals; sensitivities certified as partial derivatives with the chain rule and covariance propagation kept as separate layers; continuous-time experiment dynamics with trajectory uniqueness and endpoint/peak/integral/threshold consumers; the milestone instance (a parameterised discharge ODE, a measured series, a derived region, propagated envelopes, a next-measurement choice, and a falsified family) plus a nonlinearly parameterised portability instance; and the separated structure/parameter-evidence/validation receipts with the proposal-is-not-acceptance repair frontier — with the dependency map and the exact remaining obligations, probability explicitly not yet included.  Lean: `Lean/Integration/Experiment/` |
| [`TOE_STAGE5_INFERENCE.md`](TOE_STAGE5_INFERENCE.md) | weighted inference, several parameters and certified propagation (Stage 5): Bayes' rule over a finite hypothesis family returned as a genuine probability mass function, with the support identity, the division-free Bayes factor, sequential-equals-batch updating, and the bridge proving the posterior's support lies inside the surviving parameter region while a region determines no weights; surviving regions in several parameters — convex and closed for affine families, interval envelopes over connected regions, and the identifiability dichotomy in which fewer readings than parameters always leave an unresolved direction for rank reasons; certified quantity-graph edges whose declared sensitivities are proved to be partial derivatives, together with a compiler field that computes the propagated variance and is proved to be `Cov.push`; and measurement discrimination for non-affine families by separation modulus, with the proof that this ranks guarantees rather than regions.  Lean: `Lean/Integration/Experiment/` |
| [`TOE_STAGE6_INFERENCE.md`](TOE_STAGE6_INFERENCE.md) | calibrated dynamical inference (Stage 6): coverage/calibration semantics, in which a sampling model gives a genuine coverage probability, the Stage-4 tolerance region is proved to be a coverage-one procedure under bounded noise, Bonferroni intersection holds, and no function turns a reported region into a level — keeping prediction envelope, credible region and confidence region provably distinct; continuous Bayesian inference with a density prior on a compact interval, normalisation, Bayes odds, sequential-equals-batch updating and the bridge proving the posterior's support lies inside the surviving deterministic region while the region determines no density; an uncertainty budget derived from the certified graph derivatives and the input covariance, with contribution shares that sum to one, a dominant input and a measurement-selection theorem by actual variance reduction; nonlinear local identifiability from the Jacobian, with local injectivity from an antilipschitz derivative and the rank obstruction that too few measurements always leave an invisible direction no tolerance repairs; trajectory sensitivities satisfying the variational equation, unique on the window with a Grönwall modulus and a worked instance verifying the interchange with ∂/∂θ; repair obligations as six classes behind a refutability gate, with the unrestricted patch generator proved to fit everything, predict nothing and be inadmissible; and one synthetic dynamical experiment carried end to end through every lane.  Lean: `Lean/Integration/Experiment/` |
| [`TOE_QFTGR_FRONTIER.md`](TOE_QFTGR_FRONTIER.md) | the QFT/GR common-variation round: an audit of the Agda common-action / stress-weld lane at master `758e1cfa` (which arrows are checked proof terms, which are record-field obligations, which are `Bool` ledgers), the collapse of that frontier into six statements, and the four of them that are now Lean theorems — pairing separation with its exact spanning condition, the finite-cutoff→continuum stress theorem in which the continuum tensor is *derived* (Banach–Steinhaus plus Riesz) rather than postulated, sector aggregation commuting with the cutoff limit, one common metric-variation language with the stress weld, and the one-dimensional source-coordinate second-derivative law — together with eight negatives showing each hypothesis is load-bearing, and the exact remaining obligations.  Lean: `Lean/Integration/Variation/` |
| [`TOE_INGESTION_CONSOLIDATION.md`](TOE_INGESTION_CONSOLIDATION.md) | the ingestion/consolidation round: what was mined out of the supplied handoff archive before it was deleted (328 Agda modules, 2 427 Lean sources, Yang–Mills and Navier–Stokes paths skipped), the seven Lean modules promoted into the built `Synthesis` library, the repaired `AgdaMirror` build glob, the mechanical promotion classifier and the 58 imported modules it lifted into the new built `Promoted` library, and four new owners — contract adequacy and the free-field/ledger audit (`Integration.RecordConstraintAdequacy`), the ingested→elaborates→wired→audited→cited promotion ladder with the proof that presence in the store does not determine build status (`Integration.CorpusPromotion`), the repairs of the vacuous gauge, spin and unitary contracts (`Synthesis.ContractRepair`), and typed bridges with their four statuses, including the proof that bridge existence is directional (`Integration.BridgeStatus`) — with the dependency map and the exact remaining obligations |
| [`MIRROR_DRIFT_MANIFEST.json`](MIRROR_DRIFT_MANIFEST.json) | pinned source digests for the mirrors the Level-II/III spine consumes; regenerate and check with `scripts/mirror_drift.py` |
| `CORPUS_INVENTORY.md` | the generated corpus inventory (with `corpus_index.json` and `corpus_lanes.csv`) |
| `PR_HEADS_STATUS.md` | what was and was not found of the PR_HEADS surfaces named in the handoff |
| `scripts/corpus_inventory.py` | the indexer that regenerates the inventory |

Machine-checked counterparts: `Lean/Integration/SewingTaxonomy.lean` (the seven
classes and the provenance schema) and `Lean/Integration/SewingRegistry.lean`
(the rows, plus meta-theorems including `no_row_claims_agda_typechecked` and
`no_branch_only_rows`).

No Agda checker was run in this environment; no row claims an Agda typecheck.
