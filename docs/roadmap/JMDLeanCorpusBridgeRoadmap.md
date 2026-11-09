# JMD / SOLFUNMEME Lean-corpus and DASHI interoperability companion

**Date:** 2026-11-09. **Source of truth for proof ownership:** [dashi_agda / JMDImageOwnerRoadmap](https://github.com/chboishabba/dashi_agda/blob/chatgpt/jmd-image-owner-roadmap-20261109/Docs/roadmap/JMDImageOwnerRoadmap.md). This Lean document is an *interop discovery* roadmap, not evidence that declarations have been transported or kernel-checked.

## External corpus: actual source supplied by JMD

- GitHub-wide Lean repository search, sorted by update: https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc
- JMD reported **17.9k** matches on 2026-11-09; this is a changing GitHub search estimate, not 17.9k downloaded repositories.
- JMD's **~1,242 starred Lean repositories**: https://github.com/jmikedupont2?language=lean&tab=stars (personal curated subset).
- **Implemented exporter (this PR):** [`scripts/export_jmd_stars.py`](../../scripts/export_jmd_stars.py). Run `python scripts/export_jmd_stars.py` (optionally set `GITHUB_TOKEN`). Outputs `scripts/jmd_starred_all.csv`, `scripts/jmd_starred_primary_lean.csv` and `scripts/jmd_starred_summary.json`. This exports public starred repositories only, not the GitHub-wide 17.9k search. No live harvest is claimed.
- JMD's earlier **~21k** was an independent approximate global estimate. Do not merge the three counts.
- JMD's canonical references: https://github.com/meta-introspector/solfunmeme-metameme/issues/1 (not the global Lean manifest).

**P0C confirmed:** the source query is found. **P0C still open:** a versioned repository-ID roster, revision SHAs, licences, completeness and freshness receipts. GitHub Search API typically limits a single query to its first 1,000 results; enumerate by disjoint `created:` partitions, split overfull intervals recursively, persist raw queries/results, dedup by numeric repository IDs, and revalidate moving HEADs. Never describe `language:Lean` as a Lean4-kernel-checked corpus.

## P0 / P1 / P2 schedule

| Stage | Deliverables | Status |
|---|---|---|
| P0 image source IDs | Consume Agda-side image manifest; use SHA-256 as image attribution/reference, not proof authority | corresponding Agda branch contains manifest |
| P0 declaration ownership | Check existing `dashi_lean4` owners and prior mappings before new port | OPEN |
| P0 global corpus harvest | partitioned GitHub source enumeration with timestamp, repo ID, clone URL, commit, licence, language, fork/archived state | OPEN |
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
