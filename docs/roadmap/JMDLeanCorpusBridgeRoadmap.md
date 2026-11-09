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
