# JMD / SOLFUNMEME Lean-corpus and DASHI interoperability companion

**Date:** 2026-11-09. **Source of truth for proof ownership:** [dashi_agda / JMDImageOwnerRoadmap](https://github.com/chboishabba/dashi_agda/blob/chatgpt/jmd-image-owner-roadmap-20261109/Docs/roadmap/JMDImageOwnerRoadmap.md). This Lean document is an *interop discovery* roadmap, not evidence that declarations have been transported or kernel-checked.

## External corpus: actual source supplied by JMD

- GitHub-wide Lean repository search, sorted by update: https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc
- JMD reported **17.9k** matches on 2026-11-09; this is a changing GitHub search estimate, not 17.9k downloaded repositories.
- JMD's **~1,242 starred Lean repositories**: https://github.com/jmikedupont2?language=lean&tab=stars (personal curated subset).
- **Implemented exporter (this PR):** [`scripts/export_jmd_stars.py`](../../scripts/export_jmd_stars.py). Run `python scripts/export_jmd_stars.py` (optionally set `GITHUB_TOKEN`). Outputs `scripts/jmd_starred_all.csv`, `scripts/jmd_starred_primary_lean.csv` and `scripts/jmd_starred_summary.json`. This exports public starred repositories only, not the GitHub-wide 17.9k search. No live harvest is claimed.
- **Independent global collector (this PR):** [`scripts/collect_github_lean_corpus.py`](../../scripts/collect_github_lean_corpus.py). Run `GITHUB_TOKEN=... python scripts/collect_github_lean_corpus.py`. It recursively partitions `language:Lean` by creation date, checkpoints raw pages, deduplicates by numeric GitHub repository ID, and writes `docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv` plus `summary.json`. This is a GitHub language-classifier corpus, not a Lean 4 kernel-checked corpus.
- JMD's earlier **~21k** was an independent approximate global estimate. Do not merge the three counts.
- JMD's canonical references: https://github.com/meta-introspector/solfunmeme-metameme/issues/1 (not the global Lean manifest).

**P0C confirmed:** the source query is found. **P0C still open:** a versioned repository-ID roster, revision SHAs, licences, completeness and freshness receipts. GitHub Search API typically limits a single query to its first 1,000 results; enumerate by disjoint `created:` partitions, split overfull intervals recursively, persist raw queries/results, dedup by numeric repository IDs, and revalidate moving HEADs. Never describe `language:Lean` as a Lean4-kernel-checked corpus.

## P0 / P1 / P2 schedule

| Stage | Deliverables | Status |
|---|---|---|
| P0 image source IDs | Consume Agda-side image manifest; use SHA-256 as image attribution/reference, not proof authority | corresponding Agda branch contains manifest |
| P0 declaration ownership | Check existing `dashi_lean4` owners and prior mappings before new port | OPEN |
| P0 global corpus harvest | partitioned GitHub source enumeration with timestamp, repo ID, clone URL, commit, licence, language, fork/archived state | collector implemented; live harvest OPEN |
| P1 CFSG selected map | `AxiomMath/CFSG` → Agda original Monster/Y443 selected nonabelian generator-action correspondence | OPEN |
| P1 VOA selected map | `Fedor-Popov/Lean_VOA` → existing Agda graded VOA selected sector and all-mode operations | OPEN |
| P1 Stacks selected map | `AxiomMath/Stacks` → Agda Grothendieck category-of-elements / fibration / sheaf owners | OPEN |
| P1 newspace and Hecke | TauCeti Hecke character and Agda `AristotleHecke*` recurrence/parity owners | PARTIAL owners; full signatures OPEN |
| P2 proof transport | selected theorem statements with translated hypotheses, equality of mathematical objects and independently recorded Lean/Agda kernel checks | OPEN |
| P2 compiler runtime | Lean → Rust JIT / Blaze source reconstruction observation; side-effect/termination/resource semantics explicit | OPEN |
| P3 user-facing | verified theorem cards, source provenance, JMD image hash refs and transparent unproved labels | OPEN |

## Exact remaining lemma/contract targets (names proposed, not present declarations)

1. `leanCorpusPartitionCoverage`: enumerate all disjoint search windows and prove coverage over frozen search criteria, or record the absence of a frozen snapshot.
2. `leanCorpusDedupByRepoId`: same repository appears only once, forks retain distinct IDs.
3. `leanCorpusRevisionLicenseReceipt`: immutable source revision, license, attribution, retrieval instant and language classification.
4. `cfsgToAgdaSelectedGeneratorActionSameObject`: compare original selected presentations and group actions, not merely group orders.
5. `popovVOAToAgdaSelectedAllModes`: source-to-source algebra structures, Jacobi and locality assumptions.
6. `axiomStacksToAgdaGrothendieckFibreTransport`: preserve base category, fibre objects, morphisms, composition and identity.
7. `taucetiNewspaceCharacterToAgdaHeckeParity`: same level, weight, nebentypus, normalization and action.
8. `leanAgdaTheoremAssumptionParity`: explicitly list postulates, external theorems and imported axioms; don't equate two checked files without semantic translation.
9. `jitSelectedExecutionObservationCommutes`: runtime results correspond to pinned source and selected kernel theorem; negative controls required.
10. `jmdImageSourceProvenanceSurvivesBridge`: human attribution and image hash persist without granting any mathematical claim from visual material.

## Governance / boundaries

- **Reuse → unify duplicates → extend → construct**. Do not regenerate already-owned Hecke multiplicativity, or conflate 0-Hecke sorting with classical modular Hecke algebra.
- Agda remains golden for DASHI. Lean is independent upstream proof authority and an interop partner, not an automatic translation certificate.
- Original JMD/meta-introspector attribution, Aristotle/Harmonic attribution for imported arithmetic, AxiomMath and Popov author provenance must survive.
- Don't disclose unpublished DASHI Yang–Mills proof text. Existing open physical E1/D1/D2/N1/G1 gates are not promoted by a heuristic spectral image.
- No CI-dependency, no Docker requirement; pinned local checker receipts are preferred.
- The image SHA-256 hashes are exact byte identities for provided originals, not copyright or publication permissions.

## Source pointers

- https://github.com/AxiomMath/CFSG
- https://github.com/AxiomMath/Stacks
- https://github.com/Fedor-Popov/Lean_VOA
- https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/AristotleMathSourceParityExact.agda
- https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Moonshine/AristotleHeckeGeneralPrimePowerDecompositionExact.agda


> **2026-11-09 superseding scope note:** Formal Lean/Agda declarations and checked proof dependencies are the core. SLR/PNF is optional downstream; the reported 8,764/1,996 star counts and 20.4k dynamic global-search display supersede earlier estimates. See the appended formal-first section.

## 2026-11-09 correction: formal-first worlding and AO reconciliation

**Priority correction:** Agda and Lean source declarations and checked proofs are **the primary/sole mathematical substrate**. Do **not** put SLR, PNF, embeddings, Rust, dashboards, or language-as-algebra extraction in the critical path to mathematical matching. Those are optional projections and indexes. The programme is **link → cross-pollinate → deduplicate → world** all source declarations, while preserving the difference between exact equality, definitional equality, proven equivalence, implication, reuse, conjectural analogy, and source-only resemblance.

The objective is a provenance-indexed **formal declaration world**, not a flat list of repositories:

`source repo + revision + file + declaration + type + universe parameters + hypotheses + axioms + imports + proof status`
→ typed edges (`dependsOn`, `definitionallyEqual`, `provedEquivalent`, `implies`, `isTransportOf`, `sameSource`, `suggestedAnalogy`, `refutes`)
→ reusable mathematical objects / explicit residual goals.

**No semantic equivalence from hashes alone:** repository ID identifies a GitHub repository; blob SHA identifies bytes; declaration fingerprints identify normalized syntax only relative to an explicitly recorded Lean/Agda version, imports, elaboration context and normalization protocol. They cannot establish theorem equivalence without checked correspondence.

### AO owners to reuse in Agda before introducing interfaces

| Existing owner | Intended use |
|---|---|
| `DASHI/Core/ProofDebtRouterExact.agda` | classify the outstanding result: mathematics, formalization, source parity, missing data, or already-owned dependency |
| `DASHI/Interop/ProofArchaeologyCoarseFineAdapterExact.agda` | coarse candidate identification followed by exact statement and hypothesis checks |
| `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda` | source-specific proof-owner ledger |
| `DASHI/Core/DependencyDerivedMinimalInvalidationBidiExact.agda` | affected dependents only when new proofs or revisions arrive |
| `DASHI/Core/DependencyWeightedDiagnosisSchedulerBidiExact.agda` | prioritise shared blocker discharge |
| `DASHI/Reasoning/AristotleSelectiveImplicationReopeningExact.agda` | selective implication/certificate reopening |
| `DASHI/Interop/BroadMathProvenanceDependencyGraphExact.agda` | mathematical dependency and attribution graph |
| `DASHI/Wikimedia/JmdLeanIntegratedMachineLineageExact.agda` | JMD source and cross-prover lineage |
| `.autonomous-orchestrator/registry.json` | reuse assigned worker owners; no new orchestration substrate |

These are **located source files**, not assertions of ready-made whole-corpus support. Kernel check and inspect their precise reusable signatures before extending anything.

### Updated priorities and exact deliverables

- **P0:** finish image→Agda declaration ownership; pin and validate both Lean corpus exports; inventory existing `dashi_agda` and `dashi_lean4` declarations and corresponding provenance.
- **P1:** build declaration-level import/assumption/proof-dependency edges directly from elaborated Lean and parsed/checked Agda. Avoid treating repo names, theorem names, or README descriptions as proofs.
- **P2:** partition duplicate claims into `same bytes`, `same AST under context`, `same mathematical statement`, `one implies other`, `transport with proof`, or `unverified candidate`. Keep all source identities and licenses.
- **P3:** world the connected components: canonical mathematical referent (where justified), every original declaration, exact transport paths, unsatisfied hypotheses and affected downstream lemmas. Never quotient by an unproved equivalence.
- **P4:** AO search and reuse across components, trace shortest justified proof dependencies, select highest shared missing lemma, then kernel-check in the owner language. Agda adjudicates DASHI; Lean adjudicates source Lean. The cross-prover relation itself needs an explicit theorem/interpretation check.
- **P5:** optional SLR/PNF/Blaze interfaces for presentation/navigation and runtime observation, **not** formal-proof authority.

**Exact remaining bridge contracts (proposed signatures, not discharged lemmas):**
`leanDeclarationExtractMatchesElaboratedType`;
`agdaDeclarationExtractMatchesKernelCheckedType`;
`assumptionClosurePreservedUnderCrossLanguageBridge`;
`sameNormalizedSyntaxRequiresSameContext`;
`provedEquivalentDeclarationsCanBeSafelyWorlded`;
`unprovedAnalogyNeverPromotedToEquivalence`;
`sourceProvenanceSurvivesWorldDedup`;
`foreignProofDischargesOnlyMatchedGoal`;
`minimalDependencyReopeningAfterCorpusUpdate`;
`existingOwnerDominatesNewConstruction`.

### Live corpus correction

At this tranche, JMD's **starred repositories** export is reported committed in `dashi_lean4` PR #105 with **8,764** total and **1,996** Lean-primary-language starred repositories. The **independent GitHub-wide** Lean search displayed **20.4k** results in the user's latest observation; the separately running partitioned collector had previously reported **16,604** unique entries at 178 pages / 27 partitions. These are distinct observation instants/scopes, not a discrepancy that may be erased by changing one count into the other. GitHub search results are mutable.

### First-page GitHub-wide Lean triage (2026-11-09)

These ten repositories were located as public, non-archived GitHub repositories. This is **repository discovery only**; no theorem signatures, Lean build receipts or mathematical equivalences are asserted.

| Repository | Candidate formal-work lane | Next evidence required |
|---|---|---|
| `VladimirMarko/conaled` | unknown pending source inspection | inspect `lakefile`, declarations and domain |
| `itakura-hidetoshi/4d-mass-gap` | candidate Yang–Mills / mass-gap comparison | inspect exact 4D hypotheses and independence of source proofs; no Clay promotion |
| `TauCetiProject/TauCetiRoadmapJobs` | roadmap/worker coordination | distinguish task metadata from verified Lean declarations |
| `grwtsk/math` | mathematical discovery/provenance | pin actual theorem statements, proof status and imports |
| `emberian/minidregg` | zk/fhe/effect semantics candidate | inspect exact structures and theorems |
| `the-omega-institute/trureturing` | automated discovery and proof frontiers | inspect checked theorem objects versus discovery metadata |
| `scottnarmstrong/KAM-dev` | KAM analytic dynamics | discover exact positive-measure KAM lemma signatures |
| `TauCetiProject/TauCetiRoadmap` | human/AI Lean task routing | keep roadmap tasks distinct from proof declarations |
| `Verified-zkEVM/PolyFun` | polynomial functors, interaction trees, algebraic effects | direct high-alpha match candidate for JMD syntax/laws/handlers; theorem-by-theorem comparison required |
| `SolidiKeY/solidity-lean` | executable semantics and formal compiler contracts | identify language semantics/verified correspondence, not runtime claims |

**Highest-alpha first-page cross-pollination candidate:** `Verified-zkEVM/PolyFun` ↔ JMD's program syntax/laws/handlers ↔ existing DASHI program-semantics/effects machinery. **Highest-risk overclaim:** `itakura-hidetoshi/4d-mass-gap` is only a candidate comparison; repo name cannot discharge YM E1/D1/D2/N1/G1.

Reference: https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc . User-provided 20.4k display is not a stable GitHub-wide count.


## 2026-11-09 formal-world completion cut — privacy-preserving, declaration-first

**Scope:** Only formal Agda/Lean sources and mathematical dependencies belong in the critical path. The GitHub-wide search landing page (20.4k dynamic matches reported 2026-11-09) was an *illustrative sample*, **not** a task to evaluate or contact each recently updated repository. In particular, `itakura-hidetoshi/4d-mass-gap` is not an approved collaboration target or evidence of resolving a Clay gap. **Do not open external PRs, file external issues, message external maintainers, upload unpublished DASHI material, or push private work to third-party repositories.** Internal source comparisons must respect authorship and repository visibility. Public PRs may contain source pointers and generic interfaces, but not unpublished mathematical content.

### Phase gates: formal mathematical world, not metadata index

| Phase | Deliverable | Acceptance tests / exact remaining result | Status |
|---|---|---|---|
| **F0: sources** | Immutable image-to-claim pointers; Agda/Lean repo+commit inventory, independent starred/global corpus imports | F0.1 `allJmdImageClaimsHaveOwnerOrOpenClassification`; F0.2 `starsManifestRepoIdsUnique`; F0.3 `globalLeanPartitionReceiptsComplete`; F0.4 `sourceVisibilityAndAttributionPreserved` | images and starred export available, global full export and exact image declarations OPEN |
| **F1: declarations** | Versioned Lean and Agda declaration inventories with elaborated type, universe parameters, parameters/implicit instance assumptions, axioms, import closure and declaration/term identifiers | F1.1 `leanDeclarationIndexFaithfulToPinnedKernelEnvironment`; F1.2 `agdaDeclarationIndexFaithfulToPinnedKernelEnvironment`; F1.3 `declarationImportClosureSound` | OPEN |
| **F2: typed edges** | Direct formal dependencies and candidate cross-library edges; distinguish verbatim duplicate, definitional equality, mathematical equivalence, implication, interpretation, and analogy | F2.1 `edgeKindDoesNotPromoteUnprovedCandidate`; F2.2 `directImportDependencyEdgesAreSourceFaithful`; F2.3 `crossProverTranslationPreservesAssumptions` | OPEN |
| **F3: dedup/world** | Shared mathematical referents only after proof; preserve multiple proofs, licenses, and declarations as separate source identities | F3.1 `provedEquivalenceWorldingIsCongruent`; F3.2 `distinctProofAndProvenanceNotCollapsed`; F3.3 `unverifiedCandidateNeverDefinesQuotient` | OPEN |
| **F4: AO max-cut** | Existing-owner lookup followed by proof-debt classification, dependency cone computation, shared missing-lemma selection | F4.1 `ownerFirstNoUnnecessaryReproof`; F4.2 `proofDebtRoutingRespectsCertificateStatus`; F4.3 `minimalDependencyReopeningPreservesUnaffectedNodes`; F4.4 `chosenGapHasExplicitDownstreamConsumers` | partial prior AO modules, corpus instantiation OPEN |
| **F5: certified transports** | At least one end-to-end selected Hecke witness and then Monster/VOA/Karp/categorical target comparison | F5.1 `selectedHeckeCrossRepoStatementParity`; F5.2 `selectedHeckeTransportKernelChecked`; F5.3 `negativeControlDistinguishesNonEquivalentStatements`; downstream open lemmas separately tracked | OPEN |
| **F6: optional projections** | SLR/PNF/Blaze/game navigation of the *already checked* world | F6.1 `projectionDoesNotBecomeProofAuthority` | DEFERRED |

All `F*.x` names above are **proposed new integration contracts**, not existing checked declarations. Avoid writing dozens of wrappers: each should be an actual lemma or a concrete ingestion/runtime acceptance predicate, with its source evidence specified.

### Existing AO theorem owners and exact reuse points

- `DASHI/Core/ProofDebtRouterExact.agda`: `routeDebt`, `sourceEstablishedAlignedDeferredIsCertificationDebt`, `sourceEstablishedAlignedDeferredIsNotMathematicalDebt`, `SourceIdentity`, `StatementAlignmentReceipt`, `FullyAligned`, `SourceAlignedDeferredTheorem`, `CertifiedKnownTheorem`. **Do not treat a source receipt as an inhabitant of the target theorem.**
- `DASHI/Interop/ProofArchaeologyCoarseFineAdapterExact.agda`: `proofAnchorReopenExact`, `proofAnchorObserverSeparating`, `surfacePlusResidualDeterminesAnchor`. The coarse view is not enough without the fine historical/provenance residual.
- `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`: `IdentityStatus` (`sameObjectProved`, `structuralAncestor`, `candidateAlias`, `notSameObject`, `unresolvedIdentity`) and `PaymentStatus` (`paid`, `conditionalPayment`, `unpaid`, `notApplicable`); canonical Ibrahim policy favours explicit owner → typed dependency → typed generalisation. **Adapt** the typed classification, do not pass unproved candidate aliases as same-object proofs.
- `DASHI/Core/DependencyDerivedMinimalInvalidationBidiExact.agda`: `AffectedSemanticAxis`, `derivedExplicitInvalidation`, `derivedInvalidationIsContainedInEveryCover`, `canonicalMinimalInvalidationReceipt`.
- `DASHI/Core/DependencyWeightedDiagnosisSchedulerBidiExact.agda`: `DependencyPriorityPolicy`, `WeightedDebugCandidate`; dependency weight is declared priority, **not** truth/confidence probability.
- `DASHI/Reasoning/AristotleSelectiveImplicationReopeningExact.agda`: `semanticChangeReopensAristotleSearchPolicy`, `semanticChangeReopensAristotleActionTransitively`, `reopenableNotRefuted`, `reopenableNotProved`.
- `DASHI/Wikimedia/JmdLeanIntegratedMachineLineageExact.agda`: `IntegratedDeclarationBinding`, `mkIntegratedDeclarationBinding` retain attribution; source presence alone is not execution or an imported Agda proof.

### First two vertical slices, exact residual dependencies

**Slice H — existing Hecke owners, cheapest proof-bearing regression.** Starting owners: `AristotleHeckeRecurrenceCoreExact`, `AristotleHeckeGeneralPrimePowerDecompositionExact`, `AristotleHeckeWordsSourceParityExact`, and `AristotleMathSourceParityExact`. Do not rebuild squarefree multiplicativity. Unpaid: extract source/target statement signatures and normalization, prove the selected same-statement receipt, record the original `Nat` Hecke packaging / raw prime-power grouping / finite separating bound as separate outstanding statements where still unpaid, and produce checked positive and negative controls. The source-side arithmetic theorem is a donor, not proof of any executable representation or whole operator algebra by itself.

**Slice W — nontrivial mathematical world.** Establish a typed world component that contains two original source declarations plus a *checked* interpretation/implication path; preserve their distinct proofs, source identifiers, assumptions and any open hypotheses. Feed a genuinely remaining target back to `ProofDebtRouterExact` and `DependencyDerivedMinimalInvalidationBidiExact`. Repeat on Monster/Y443, Popov VOA, Stacks indexed fibres and Karp/FRACTRAN only after searching their current existing owners. No source-name-based promotion.

### Definition of done for the next PR iteration

1. Extract a small real Lean/Agda declaration corpus at pinned commits **directly through each proof system**, rather than inferring theorem types from GitHub search descriptions.
2. Emit a machine-readable identity/dependency ledger with source SHA, original declaration names and types, checker version, axioms, explicit equivalence/implication receipts, and unresolved obligations.
3. Prove or kernel-check at least one nontrivial selected bridge; add one deliberately non-equivalent negative-control pair.
4. Show AO finds a previously owned theorem rather than generating a redundant proof; separately show how an unpaid target is routed without being declared solved.
5. Record the precise integration gate results and provenance in the roadmaps, without sending the work to an external repository.

**Privacy rule:** repo search and normal reading of publicly available declarations are fine. Distribution of DASHI's unpublished material to unaffiliated repositories is forbidden unless separately and explicitly authorized.


## 2026-11-09 maximum-cut reconciliation after full PR archaeology

**This section supersedes earlier speculative F0–F5 missing-capability rows.** Source archaeology identified existing implementations. Do not reimplement them. The next proof work begins at *integration of those implementations with actual source declarations*.

### Confirmed existing owners, not gaps

- `dashi_agda/tools/agda_preflight/agda_preflight/ast_index.py`: Agda AST signatures, imports, clauses and record/data structures.
- `repository_discovery.py` / `semantic_extension.py`: repository DB `normalized_signature`, `signature_sha256`, `body_sha256`, `repo_refs`, `related_symbols`, `discovery_receipt` and candidate evidence.
- `proof_router.py` / `external_proof_bridge.py`: proof debt and external source/verification receipt routing, explicitly not automatic theorem proof.
- `dashi_agda` PR **#1212**: OpenAI math corpus source atlas, symbol snowball and owner routing; `dashi_lean4` PR **#78**: source declaration index, candidate-owner matrix, reviewed same-object boundaries and statement-integrity checks.
- `dashi_agda` PR **#1437** (alongside #1415–#1417): hierarchical spectral Pareto, world-eigen stratification, sublinear conductor and max-cut ownership. Lean PR **#102** mirrors the formal contract. These are **existing mathematics**, not conjectural new machinery.
- Lean PR **#71** already has scoped verifier same-object evaluation.
- The original Hecke recurrence, prime-power assembly and related Agda owners are existing; no reproof of squarefree multiplicativity.

### New full-corpus input now committed

`dashi_lean4` PR **#105** committed two independent GitHub corpora at retrieval time 2026-11-09: **8,764 JMD public stars**, of which **1,996** are primary-language Lean, and **21,481 GitHub-wide `language:Lean` repositories** across **34 disjoint creation-date partitions**, with **231 pages** and **298 raw count/page receipts** (reported from completed collector validation). These are moving GitHub-index observations, not all formally checked Lean declarations.

New **`scripts/audit_jmd_formal_corpus.py`** joins the two sources only by numeric GitHub repository ID, validates exported counts, subset identity, checkpoint ID/name agreement, disjoint contiguous date windows and expected page counts, and writes `docs/roadmap/jmd_formal_ingress/audit.json` plus `starred_global_overlap.tsv`. `scripts/test_audit_jmd_formal_corpus.py` contains positive and fail-closed negative controls. The integration **does not classify mathematical theorems** and must never promote metadata to proof. Run locally from the Lean repo root:

```sh
python -m unittest discover -s scripts -p 'test_audit_jmd_formal_corpus.py' -v
python scripts/audit_jmd_formal_corpus.py
```

The script's synthetic fixtures were tested during development. **The full 21,481-row live ingress audit has not yet been run in the repository environment.** Its outputs should not be described as present before execution.

### Corrected exact remaining max-cut

| Gate | Decisive result (avoid duplicate tools) | Status |
|---|---|---|
| **P0.01** | Run the new full-corpus audit against both committed CSVs and actual checkpoint; inspect any coverage mismatch rather than suppressing it | OPEN for production execution |
| **P0.02** | Apply existing `dashi-repo symbol / related_symbols / discover` against **each distinct** JMD image claim and record exact declaration, full type, imports and source commit; distinguish non-mathematical images | OPEN: module candidates already indexed |
| **P1.01** | Extend **existing** OpenAI-math source candidate-router/statement-audit pattern to selected corpus **declarations**, not repository names; preserve branch/version and no-claim defaults | OPEN: generic integration, source implementations present |
| **P1.02** | Obtain authoritative selected Lean elaborated theorem types and axiom/opaque dependency closure, using pinned Lean environments, and compare with Agda original owners | OPEN for selected external formal proofs |
| **P2.01** | One *source-inspected* and *kernel-checked* same-object equality or hypothesis-preserving implication, with a deliberately non-equivalent negative control and original author credit | OPEN; source comparison precedent exists |
| **P2.02** | Join that certified relation into existing proof-debt and dependency-scheduler owners; show actual paid gap and unchanged unrelated cones | OPEN for this corpus instance |
| **P3.01** | Repeat the verified route for Hecke, selected Monster/Y443, Popov VOA, CFSG, Stacks or Karp only if a **precise** consumer and actual source declaration warrant it | OPEN by consumer |
| **P3.02** | Preserve private/unpublished DASHI material: **no external PR, issue, comment, message, or upstream source upload** unless separately authorised | Mandatory invariant |

These gate labels are **integration milestones**, not newly defined Agda/Lean theorem names. The mathematics should be placed with its existing closest owner in the Agda/Lean formal dependency graph, not in a competing world-index package. SLR/PNF is optional for human navigation and never proof authority.


## 2026-11-09 implemented LLM-free formal-world spine

Canonical script/Agda proof owners were added to the companion
[dashi_agda #1477](https://github.com/chboishabba/dashi_agda/pull/1477):

- \`scripts/jmd_formal_world_reconcile.py\`: single existing \`.dashi/repository.sqlite3\`
  database; image-to-owner search on original Agda symbols; native
  \`repo_requirements\` discovery; selected external Lean source admission
  using the 21,481-repository CSV; candidate-only formal links; opt-in
  \`lake env lean\` exact proof probes; changed-goal dependency closure.
- \`scripts/jmd_attach_wikidata_oeis.py\`: detects QID/OEIS coordinates
  only within AST-indexed Agda declaration source spans and records them
  as evidence, **not** theorem equivalences.
- \`DASHI/Interop/JMDFormalWorldReconciliationExact.agda\`: typed
  candidate-vs-proof firewall; proof-term-bearing implications and
  equivalences; composition; world-pair provenance preservation; imported
  through the canonical Interop aggregate.
- \`Docs/roadmap/JMDFormalWorldAutomaticExecution.md\`: executable command
  contract, safety boundary, verification instructions and remaining
  exact mathematical bridges.

This Lean branch now includes \`scripts/extract_jmd_lean_declarations.py\`
for pinned Lean \`#check\`/\`#print axioms\` inspection and
\`scripts/test_extract_jmd_lean_declarations.py\` for source-revision,
identifier and checker-failure regression fixtures. This extends existing
PR #78's source-aware OpenAI-math owner routing; no second index or LLM
orchestration is introduced.

**Statuses:** Code and Agda definitions are source-written and committed.
The assistant environment lacks installed Lean and Agda compilers and
cannot execute the user's local \`.dashi/repository.sqlite3\`, so neither
kernel acceptance nor full-corpus live world matching is claimed here.
\`dashi_lean4\` source selection is on-demand, not a claim that 21,481
repositories have been cloned or their declarations elaborated.

**Actual remaining hard frontier:** (1) local checker/test execution,
(2) automatic source-faithful selection and elaboration at scale, (3)
a fully checked shared-object translation between chosen Lean and Agda
types, (4) a real proof reuse that discharges the original Agda
obligation, (5) incremental invalidation replay on real updated source.
The deterministic pipeline can leave those open without false promotion.
