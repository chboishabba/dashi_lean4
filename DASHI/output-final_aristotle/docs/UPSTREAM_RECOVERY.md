# Recovering the upstream branches

This pass re-fetched the whole upstream DASHI Agda repository — every branch,
not just the pull request the port started from — and worked out mechanically
what it carries that this project had not seen.  `tools/upstream_fetch.py`
does the survey and the vendoring; the corpus it maintains lives in
`upstream/dashi_agda/` with a row per file in `MANIFEST.tsv`.

## What upstream has

| | |
| --- | --- |
| branches (`refs/heads/*`) | 614 |
| branches whose Agda tree differs from `master` | 612 |
| `.agda` modules on `master` | 11 032 |
| paths a branch *adds* to `master` | 579 |
| paths a branch *changes* from `master` | 1 249 |

## What was recovered in this pass

The corpus went from 3 565 paths / 3 583 files to 3 839 paths / 3 857 files across 49 refs.
Three selections were vendored:

* **every module a branch adds to `master` that was not already here** — 182
  files.  These are the genuinely branch-local modules: work that exists on one
  agent branch and nowhere else.  By branch:

  | files | branch |
  | --- | --- |
  | 61 | `agent/decision-controlled-dynamics-convergence` |
  | 32 | `agent/zeta-reflection-orbit-defect-2026` |
  | 27 | `agent/pnf-wave-access-trauma-learning` |
  | 14 | `agent/contested-ambient-authority-pnf` |
  | 12 | `agent/itir-producer-complete-token-heads` |
  | 9 | `agent/wave-quaternion-orbit-conscious-access-round10` |
  | 7 | `agent/ym-round61-dlr-transfer-audit` |
  | 6 | `agent/ns-clay-ancient-defect-round65` |
  | 5 | `agent/ns-clay-ancient-increments-round66` |
  | 4 | `agent/introspective-epistemic-authority` |
  | 3 | `formalise-aristotle-2510-01346` |
  | 1 | `agent/decision-interoception-contested-convergence` |
  | 1 | `agent/introspective-visual-proof-loop` |

* **the ontology-, reasoning- and evidence-named modules a branch *changes*
  from `master`** that the corpus did not carry at all — 46 files, including
  `DASHI/Core/TypedEvidenceDependencyExact.agda` and
  `DASHI/Dynamics/EvidenceGatedRechartBoundary.agda`;

* **the `Ontology/`, `Knowledge` and classification modules of `master`** that
  the corpus was missing — 46 files, including `DASHI/Ontology/Everything.agda`,
  `DASHI/Philosophy/ProcessOntology.agda`, the `DASHI/Interop/SensibLawOntology*`
  modules, `Ontology/DNA/SemanticChecksumAlgebra.agda` and the two
  classification-lattice modules.

Everything upstream that names Wikidata was already vendored; the survey
confirms there is no remaining `Wikidata`-matching path, on `master` or on any
branch, outside the corpus.

## What was ported to Lean

Most of the recovered material is physics, analysis and number theory that has
nothing to do with this project's subject.  Four ideas in it are about
knowledge representation, and each is now a proved Lean module rather than a
recorded claim.

| Recovered upstream idea | Lean rendering here |
| --- | --- |
| non-factorability survives further coarsening (`DASHI/Core/NonFactorabilityCompositionExact`) | `Epistemic.not_factorsThrough_postcomp`, with the converse shown to fail |
| hidden update order does not descend through a fixed surface (`DASHI/Core/FibreOrderNonfactorabilityExact`) | `Epistemic.UpdateOrder`, `orderedSurface_eq_of_invariant`, `not_factorsThrough_orderedEndpoint` |
| — instantiated on the ontology | `Wikidata.classSurface_cannot_decode_editOrder`: two redundant `P279` edits leave the derived class relation fixed, so it cannot say which curator edited last |
| bounded accumulation versus a commitment threshold (`DASHI/Cognition/PNF/BoundedEvidenceCommitmentExact`) | `Epistemic.Tally`, `Epistemic.commit`, and the boundary: `committed_does_not_entail_holds`, `holds_does_not_entail_committed`, `commitment_does_not_determine_state` |
| capture without secrecy: a public rule surface with held interpretation (`DASHI/Reasoning/FolkLawEpistemicAuthority*`, `DASHI/Governance/EpistemicCaptureProfessionalClosureExact`) | `Wikidata.isSubclassOf_submit_shadowed` (open submission is inert where ranking has spoken) and `Wikidata.answer_not_factorsThrough_unranked` (a fully public submission record still does not determine the answers, while the ranked record does) |
| correlated evidence is not independent confirmation, and a change at a source reopens what depends on it (`DASHI/Core/TypedEvidenceDependencyExact`) | `Epistemic.independentSupport`, `naive_counting_commits_independent_does_not`, `reopens_iff_transGen` |
| access/retrieval bias is not a formal defect (`DASHI/Reasoning/AccessBiasFallacySeparationExact`) | `Wikidata.retrieveTop_sound` / `retrieveTop_not_complete`, and the two-way non-determination `defect_not_factorsThrough_retrieval`, `retrieval_not_factorsThrough_defect` |

The upstream modules state these as finite enumerations checked by `refl`.  The
Lean versions are theorems about the executable Wikidata engine: the surfaces
are the real derived subclass and instance relations, the checkers are the
exact ones, and the counterexamples are decided rather than declared.

## Carrying the recovered corpus mechanically

The two Agda front-end routes were re-run over the enlarged corpus, so the
recovered modules are also carried as Lean:

| route | before | after |
| --- | --- | --- |
| `AgdaVendor` (offline transliteration, kernel-checked) | 220 modules | 239 |
| `AgdaCheck` (Lean reads the upstream `.agda` directly) | 150 modules | 253 |

Modules the front end still cannot elaborate are recorded, with the route they
failed on, in `tools/agda2lean_blocked.txt` and `tools/agdacheck_skipped.txt`,
so the gap is documented rather than hidden; `docs/AGDA_FRONTEND_COVERAGE.txt`
and `docs/AGDA_DIRECT_CHECK.txt` are the refreshed coverage reports.

## Reproducing the survey

```sh
python3 tools/upstream_fetch.py --report               # what upstream has
python3 tools/upstream_fetch.py --emit --new           # vendor branch-local modules
python3 tools/upstream_fetch.py --emit --master --match 'Ontology/|Knowledge'
python3 tools/upstream_fetch.py --emit --changed --match 'Ontology|Evidence'
```
