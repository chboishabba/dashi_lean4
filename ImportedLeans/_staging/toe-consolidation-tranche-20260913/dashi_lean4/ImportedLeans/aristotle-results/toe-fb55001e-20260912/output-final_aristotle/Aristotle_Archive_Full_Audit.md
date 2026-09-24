# Aristotle Archive — Full Formal/Operational Audit

**Audited source:** `ae06ae06-2580-422a-8fc3-92aeaaca8762-aristotle (2).tar.gz`  
**Audit scope:** every `RequestProject/**/*.lean` file recursively.  
**Purpose:** identify theorem-bearing contracts reusable by SensibLaw/ITIR/Nat, and separate them from corpus facts, examples, generated outputs, and operational CLI code.

## Executive result

- **189 Lean files** under `RequestProject/` recursively: 134 root theory, 19 CLI, 28 generated corpus, 8 wiki-generation modules.
- **109,571 lines**; **3,715 theorem/lemma declarations**; **1,975 def/abbrev declarations**.
- Exact scan: **0 custom `axiom` declarations, 0 `sorry`, 0 `unsafe` declarations**.
- **374 `native_decide` uses**. These are proof-producing executable facts, but many concern the pinned generated corpus; they are not universal Wikidata laws.
- **3 `partial def` declarations**, all in CLI/parser/network routines: `Cli/Enrich.lean:69`; `Cli/Enrich.lean:164`; `Cli/Fetch.lean:71`.
- No theorem hole was found by the exact `sorry`/`admit` code-token scan. Earlier apparent `admit` was the English word “admits” in commentary, not a Lean proof hole.

## Authority tiers

| Tier | Meaning | Nat/ITIR use |
|---|---|---|
| **T1 Generic formal law** | Theorem parameterised over abstract KB/claims/specs, not tied to one generated corpus | Safe as a design/theorem donor, subject to its explicit hypotheses |
| **T2 Pinned artifact theorem** | `native_decide` or theorem about the archive’s concrete generated/repaired corpus | Safe as a receipt/regression fact for that exact artifact only |
| **T3 Example/showcase** | Concrete examples demonstrating generic APIs | Useful test fixtures; no policy/authority inheritance |
| **T4 Operational code** | CLI/fetch/parser/render tooling, including the three `partial def`s | Implementation clue only; not a semantic theorem |

The core firewall is therefore: **T2/T3/T4 never silently upgrade into T1, and no tier creates SensibLaw migration/promotion authority merely by existing.**

## Root-theory subsystem inventory

### Core statement/value semantics
10 modules · 3,466 lines · 264 theorem/lemma declarations.

`Core`, `Ranks`, `Snaks`, `Terms`, `Lexemes`, `Sitelinks`, `ExternalIds`, `Quantities`, `TimeValues`, `GeoValues`.

### Constraints and validation
10 modules · 3,610 lines · 266 theorem/lemma declarations.

`Qualifiers`, `PropertyConstraints`, `StatementConstraints`, `RangeConstraints`, `CardinalityConstraints`, `AllowedUnits`, `FormatConstraints`, `ConstraintExceptions`, `ConstraintSuite`, `ContemporaryConstraint`.

### Property reasoning/query semantics
13 modules · 5,020 lines · 355 theorem/lemma declarations.

`Properties`, `PropertyEngine`, `Queries`, `CompiledFacts`, `RelationWords`, `Reachability`, `Subsumption`, `Grounding`, `Grounded`, `Semantics`, `Rdf`, `Engine`, `Paths`.

### Compiler/modules/provenance/publication
10 modules · 2,169 lines · 173 theorem/lemma declarations.

`Modules`, `ModulesCorpus`, `ModulesExamples`, `CompilerPipeline`, `Provenance`, `Publish`, `PublishExamples`, `Archive`, `Sync`, `Schemas`.

### Repair/diagnostics/review/reporting
15 modules · 5,071 lines · 346 theorem/lemma declarations.

`Defects`, `Diagnostics`, `DefectReport`, `Fixes`, `RepairWorkflow`, `RepairReview`, `RepairExamples`, `Worklist`, `WorklistExamples`, `Reports`, `ReportFormat`, `ReportExamples`, `OnePage`, `OnePageExamples`, `SpectrumReport`.

### Merge/alignment/identity/reflection
10 modules · 2,498 lines · 193 theorem/lemma declarations.

`Merge`, `ItemMerge`, `Alignment`, `BabyStepsAlignment`, `Matching`, `SoftIdentity`, `Renaming`, `Normalize`, `Redundancy`, `Reflection`.

### Taxonomy/type/ontology
19 modules · 5,080 lines · 350 theorem/lemma declarations.

`Taxonomy`, `Taxa`, `TaxaLineage`, `TaxaDiagnostics`, `TaxaExamples`, `TypeProperties`, `UpperOntology`, `FieldsOfStudy`, `Concepts`, `RelatedNotions`, `CategoryOfOntologies`, `OntologyTopology`, `OntologySheaves`, `OntologyLimits`, `OntologyColimits`, `GrothendieckSite`, `PullbackComparison`, `PullbackRetraction`, `RetractTopology`.

### Domain relation systems
13 modules · 5,548 lines · 443 theorem/lemma declarations.

`Mereology`, `Kinship`, `KinshipDiagnostics`, `Parenting`, `ParentingDiagnostics`, `ParentingExamples`, `Series`, `SeriesChain`, `SeriesDiagnostics`, `SeriesExamples`, `SeriesRepair`, `SeriesRepairExamples`, `Temporal`.

### Algebra/advanced structure
14 modules · 3,977 lines · 270 theorem/lemma declarations.

`ClassAlgebra`, `DisjointUnion`, `CubicalTypes`, `HomotopyTypes`, `OntologyGroups`, `MetaFrobenius`, `MathResonance`, `Periodicity`, `PeriodicityReport`, `ProgramAlgebra`, `SignedWords`, `Stratification`, `CyclicAlgebra`, `OntologyFields`.

### Corpus/examples/showcase
20 modules · 5,526 lines · 314 theorem/lemma declarations.

`CorpusEntailment`, `CorpusFrontier`, `CorpusRounds`, `MathCorpus`, `TheoryCorpus`, `EnrichmentCorpus`, `RelatedCorpus`, `Enrichment`, `Examples`, `Showcase`, `SelfDescription`, `BabySteps`, `BabyStepsProperties`, `FastEval`, `FeedbackSets`, `Gaps`, `KbTerms`, `Vocabulary`, `Main`, `DefTest`.

## Strongest reusable contracts for Nat / SensibLaw

| Module | Contract surface | Reuse boundary |
|---|---|---|
| **Ranks** | `not_isTruthy_deprecated`; `mem_truthyValues_iff`; `isTruthy_iff_preferred`; `isTruthy_iff_normal_of_no_preferred`; `mem_truthyItemStmts_iff`; `not_mem_truthy_of_deprecated` | Truthiness is computed over the subject–property statement family. Rank and truthy visibility are distinct; complete Q/P family coverage is needed before a normal statement can be classified truthy. |
| **Snaks** | `satisfiable_iff_clashFree`; `entails_noValue_iff`; `entails_someValue_iff`; `valuesOf_eq_nil_of_noValue` | Native `novalue` is a statement-level semantic assertion, not “a query returned no row”. This justifies `noStatementObserved ≠ nativeNovalue`. |
| **Qualifiers** | `allowedOk_iff`; `mandatoryOk_iff`; `claimOk_iff`; `specOf_eq_none_iff`; `qualSetOk_iff`; `qualSetOk_of_not_mem_table`; `scopeOk_iff` | Qualifier/scope validity is executable and separate. A missing profile can mean unconstrained only relative to a known/covered table; otherwise SensibLaw must retain `uninspected`. |
| **PropertyEngine** | `holds_of_relatedB`; restricted `relatedB_of_holds` / `relatedB_iff_holds` | Executable property relation gives sound derivability; completeness needs explicit well-formedness/symmetry/inverse/transitivity hypotheses. Derived relation ≠ direct assertion. |
| **Modules** | `moduleOf_isSubclassOf_le`; `moduleOf_isInstanceOf_le`; `moduleOf_isSubclassOf`; `moduleOf_isInstanceOf`; `moduleOf_valid`; `entails_moduleOf` | A bounded P31/P279 dependency module is a principled subject-type carrier. It is not the whole item graph and does not reconstruct native statement bundles. |
| **CompilerPipeline** | `compiled_sub_subset`; `wordStep_compiled_mono`; corpus-specific `compiled_answers_subclass` / `compiled_answers_instance` | Generic safe direction is compiled/pruned answer ⇒ source answer. Reverse completeness is corpus/stage-specific and must not be assumed for arbitrary Zelph pruned artifacts. |
| **Publish / Archive** | `parseJsonl?_jsonlOfKB`; `eq_of_renderKB_eq`; `cid_eq_of_renderKB_eq`; `importKB?_bundleOf`; `bundle_copies_agree`; `checkManifest_bundleOf` | Lossless publication and stable content identity justify content-addressed replay receipts, but a content ID is not truth, revision alignment, or authority. |
| **Sync** | `sync_entails_left`; `sync_entails_right`; `sync_least`; commutative/associative/idempotent laws up to equivalence | Future multi-source graph/evidence merge can be least-upper-bound-like while retaining provenance. Synchronisation must not invent authority. |
| **Schemas** | `conformsB_iff`; `specOkB_iff`; `completeFor_iff_conformsB_minShape` | Strong donor for replacing ad-hoc required-property lists with executable coverage/shape profiles later. |
| **Worklist / Reports** | `Task.automatic_rows_provenFix`; grouping completeness; `rows_eq_nil_iff_clean`; `provenFix_prunable` | Supports auditable automation/review queues and exact report completeness. Automatic work remains subordinate to proven preconditions. |

## Conditional / non-transferable surfaces

- **Generated corpus theorems:** excellent pinned regression/receipt facts, but not global Wikidata facts and not policy authority.
- **`CompilerPipeline` bidirectional answer equality:** stronger than the generic monotonicity theorem because it is tied to the archive’s concrete repaired/pruned corpus/stages. Do not use it as universal pruned-HF completeness.
- **PropertyEngine completeness:** requires its stated model restrictions. The sound direction is the safer default for external graph-derived facts.
- **Examples/Showcase/OnePageExamples/etc.:** examples prove APIs behave on selected fixtures; they do not establish cohort-wide migration safety.
- **CLI `partial def`s:** operational totality is intentionally not proved. They must not sit on a proof-authority path.
- **Noncomputable modules** (`Concepts`, `HomotopyTypes`, `CyclicAlgebra`, `MathResonance`, `Alignment`, `OntologyFields`) may provide mathematical specification but are not executable decision procedures merely because the theorem is formal.

## Nat mapping after the audit

```text
native revision-pinned Wikibase entity
  ├─ GUID / mainsnak / rank / qualifiers / references        [Ranks, Snaks, Qualifiers]
  └─ Q/P statement-family coverage receipts                 [Schemas-style coverage contract]

actual routed Zelph graph observations
  └─ P31/P279 bounded module                                 [Modules]
       └─ positive type closure only under preservation       [CompilerPipeline monotonicity]

native plane ⨝ graph plane
  ├─ explicit revision alignment
  ├─ content-addressed evidence surface                      [Publish/Archive identity principle]
  └─ no authority transfer

ItemPropertyEvidenceSurface
  └─ governed DomainInvariantSnapshot comparison
       └─ peer_cohort residual
            └─ least-privilege NatPeerWeld
```

This remains deliberately weaker than `migrationSafe`: **exact peer agreement, valid qualifiers, conservative type closure and stable content identity are evidence coordinates, not a P5991=P14143 theorem or edit authority.**

## Highest-alpha follow-ons revealed by the full audit

1. **Executable coverage profiles from `Schemas`:** define Nat’s Q/P and qualifier/scope coverage requirements as a named profile whose completeness can be checked, rather than only a Python list of required properties.
2. **Multi-source evidence sync from `Sync`:** if native entity exports, Zelph, source documents, and reviewer receipts are combined, model the combination as a provenance-preserving join/least upper bound; never erase source identity.
3. **Repair/worklist separation:** use `Worklist`/`Reports` contracts to keep “candidate automatically analysable” distinct from “candidate automatically editable”.
4. **Generated corpus as regression oracle only:** use the 28 generated modules to test parsers/compilers and detect drift, never to train policy by default.
5. **Preservation receipts per query family:** keep current `sound_only` vs `sound_and_complete` distinction for pruned Zelph artifacts and make it an explicit input to every negative/absence consumer.

## Complete 189-file inventory

| File | Lines | Theorems | Defs | native_decide | partial | Tier |
|---|---:|---:|---:|---:|---:|---|
| `Alignment.lean` | 226 | 13 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `AllowedUnits.lean` | 202 | 15 | 8 | 0 | 0 | T1/T3 root theory/examples |
| `Archive.lean` | 202 | 8 | 13 | 0 | 0 | T1/T3 root theory/examples |
| `BabySteps.lean` | 214 | 18 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `BabyStepsAlignment.lean` | 292 | 21 | 8 | 0 | 0 | T1/T3 root theory/examples |
| `BabyStepsProperties.lean` | 304 | 19 | 12 | 0 | 0 | T1/T3 root theory/examples |
| `CardinalityConstraints.lean` | 284 | 20 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `CategoryOfOntologies.lean` | 199 | 10 | 4 | 0 | 0 | T1/T3 root theory/examples |
| `ClassAlgebra.lean` | 303 | 23 | 6 | 0 | 0 | T1/T3 root theory/examples |
| `Cli/Codegen.lean` | 309 | 6 | 17 | 1 | 0 | T4 CLI |
| `Cli/Derive.lean` | 361 | 24 | 6 | 0 | 0 | T4 CLI |
| `Cli/Enrich.lean` | 455 | 0 | 34 | 6 | 2 | T4 CLI |
| `Cli/EnrichCmd.lean` | 280 | 0 | 10 | 0 | 0 | T4 CLI |
| `Cli/Examples.lean` | 155 | 0 | 4 | 0 | 0 | T4 CLI |
| `Cli/Fetch.lean` | 181 | 0 | 16 | 0 | 1 | T4 CLI |
| `Cli/Format.lean` | 484 | 20 | 22 | 0 | 0 | T4 CLI |
| `Cli/Import.lean` | 268 | 7 | 17 | 0 | 0 | T4 CLI |
| `Cli/OnePage.lean` | 333 | 1 | 22 | 0 | 0 | T4 CLI |
| `Cli/Publish.lean` | 507 | 0 | 26 | 0 | 0 | T4 CLI |
| `Cli/Query.lean` | 215 | 6 | 10 | 0 | 0 | T4 CLI |
| `Cli/RepairCmd.lean` | 81 | 0 | 2 | 0 | 0 | T4 CLI |
| `Cli/ReportCmd.lean` | 158 | 5 | 9 | 0 | 0 | T4 CLI |
| `Cli/ScanFormat.lean` | 240 | 8 | 13 | 0 | 0 | T4 CLI |
| `Cli/SeriesFormat.lean` | 228 | 6 | 8 | 0 | 0 | T4 CLI |
| `Cli/TaxaFormat.lean` | 250 | 8 | 10 | 0 | 0 | T4 CLI |
| `Cli/Tool.lean` | 1043 | 0 | 41 | 2 | 0 | T4 CLI |
| `Cli/WikiCmd.lean` | 89 | 0 | 5 | 0 | 0 | T4 CLI |
| `Cli/WorklistCmd.lean` | 162 | 0 | 8 | 0 | 0 | T4 CLI |
| `CompiledFacts.lean` | 273 | 29 | 2 | 8 | 0 | T1/T3 root theory/examples |
| `CompilerPipeline.lean` | 99 | 10 | 2 | 0 | 0 | T1/T3 root theory/examples |
| `Concepts.lean` | 259 | 28 | 12 | 0 | 0 | T1/T3 root theory/examples |
| `ConstraintExceptions.lean` | 393 | 31 | 17 | 0 | 0 | T1/T3 root theory/examples |
| `ConstraintSuite.lean` | 235 | 13 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `ContemporaryConstraint.lean` | 323 | 18 | 14 | 0 | 0 | T1/T3 root theory/examples |
| `Core.lean` | 228 | 21 | 7 | 0 | 0 | T1/T3 root theory/examples |
| `CorpusEntailment.lean` | 68 | 3 | 1 | 1 | 0 | T1/T3 root theory/examples |
| `CorpusFrontier.lean` | 267 | 23 | 4 | 11 | 0 | T1/T3 root theory/examples |
| `CorpusRounds.lean` | 212 | 22 | 2 | 8 | 0 | T1/T3 root theory/examples |
| `CubicalTypes.lean` | 222 | 13 | 17 | 0 | 0 | T1/T3 root theory/examples |
| `CyclicAlgebra.lean` | 116 | 10 | 3 | 2 | 0 | T1/T3 root theory/examples |
| `DefTest.lean` | 34 | 2 | 1 | 2 | 0 | T1/T3 root theory/examples |
| `DefectReport.lean` | 203 | 23 | 3 | 18 | 0 | T1/T3 root theory/examples |
| `Defects.lean` | 258 | 13 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `Diagnostics.lean` | 339 | 24 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `DisjointUnion.lean` | 291 | 18 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `Engine.lean` | 382 | 32 | 25 | 0 | 0 | T1/T3 root theory/examples |
| `Enrichment.lean` | 643 | 38 | 21 | 0 | 0 | T1/T3 root theory/examples |
| `EnrichmentCorpus.lean` | 224 | 30 | 3 | 24 | 0 | T1/T3 root theory/examples |
| `Examples.lean` | 206 | 24 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `ExternalIds.lean` | 294 | 28 | 18 | 0 | 0 | T1/T3 root theory/examples |
| `FastEval.lean` | 302 | 4 | 21 | 0 | 0 | T1/T3 root theory/examples |
| `FeedbackSets.lean` | 322 | 23 | 14 | 2 | 0 | T1/T3 root theory/examples |
| `FieldsOfStudy.lean` | 317 | 24 | 16 | 0 | 0 | T1/T3 root theory/examples |
| `Fixes.lean` | 416 | 23 | 17 | 0 | 0 | T1/T3 root theory/examples |
| `FormatConstraints.lean` | 559 | 34 | 21 | 0 | 0 | T1/T3 root theory/examples |
| `Gaps.lean` | 217 | 11 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `Generated/Chemistry.lean` | 662 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Core.lean` | 10513 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/CreativeWorks.lean` | 1049 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/DouglasAdams.lean` | 265 | 23 | 4 | 0 | 0 | T2 generated corpus |
| `Generated/Enriched.lean` | 5795 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Events.lean` | 819 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Frontier.lean` | 5535 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Frontier2.lean` | 3196 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Frontier3.lean` | 1607 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Frontier4.lean` | 698 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Geography.lean` | 3220 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Glossary.lean` | 1637 | 0 | 1 | 0 | 0 | T2 generated corpus |
| `Generated/KbTerms.lean` | 1687 | 0 | 17 | 0 | 0 | T2 generated corpus |
| `Generated/KnowledgeRepresentation.lean` | 1614 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/LifeSciences.lean` | 990 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Mathematics.lean` | 831 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/RelatedStructures.lean` | 1269 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/RelatedStructures2.lean` | 696 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Science.lean` | 1037 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Society.lean` | 1289 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Structures.lean` | 1609 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Technology.lean` | 1547 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/Theories.lean` | 2200 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `Generated/TheoryAuthority.lean` | 510 | 7 | 2 | 4 | 0 | T2 generated corpus |
| `Generated/TheorySitelinks.lean` | 337 | 0 | 1 | 0 | 0 | T2 generated corpus |
| `Generated/TheorySources.lean` | 336 | 0 | 3 | 0 | 0 | T2 generated corpus |
| `Generated/UpperOntology.lean` | 727 | 23 | 3 | 0 | 0 | T2 generated corpus |
| `Generated/VocabularyCorpus.lean` | 7877 | 23 | 3 | 7 | 0 | T2 generated corpus |
| `GeoValues.lean` | 528 | 42 | 33 | 3 | 0 | T1/T3 root theory/examples |
| `GrothendieckSite.lean` | 123 | 7 | 3 | 0 | 0 | T1/T3 root theory/examples |
| `Grounded.lean` | 185 | 18 | 2 | 14 | 0 | T1/T3 root theory/examples |
| `Grounding.lean` | 310 | 16 | 22 | 0 | 0 | T1/T3 root theory/examples |
| `HomotopyTypes.lean` | 186 | 4 | 8 | 0 | 0 | T1/T3 root theory/examples |
| `ItemMerge.lean` | 211 | 21 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `KbTerms.lean` | 168 | 16 | 1 | 11 | 0 | T1/T3 root theory/examples |
| `Kinship.lean` | 681 | 47 | 31 | 0 | 0 | T1/T3 root theory/examples |
| `KinshipDiagnostics.lean` | 232 | 12 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `Lexemes.lean` | 351 | 22 | 15 | 0 | 0 | T1/T3 root theory/examples |
| `Main.lean` | 849 | 0 | 0 | 0 | 0 | T1/T3 root theory/examples |
| `Matching.lean` | 239 | 11 | 7 | 0 | 0 | T1/T3 root theory/examples |
| `MathCorpus.lean` | 152 | 12 | 1 | 11 | 0 | T1/T3 root theory/examples |
| `MathResonance.lean` | 337 | 23 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `Mereology.lean` | 619 | 60 | 29 | 0 | 0 | T1/T3 root theory/examples |
| `Merge.lean` | 176 | 18 | 2 | 0 | 0 | T1/T3 root theory/examples |
| `MetaFrobenius.lean` | 482 | 44 | 15 | 0 | 0 | T1/T3 root theory/examples |
| `Modules.lean` | 398 | 33 | 4 | 0 | 0 | T1/T3 root theory/examples |
| `ModulesCorpus.lean` | 84 | 8 | 3 | 5 | 0 | T1/T3 root theory/examples |
| `ModulesExamples.lean` | 58 | 7 | 1 | 0 | 0 | T1/T3 root theory/examples |
| `Normalize.lean` | 125 | 12 | 1 | 0 | 0 | T1/T3 root theory/examples |
| `OnePage.lean` | 344 | 23 | 15 | 0 | 0 | T1/T3 root theory/examples |
| `OnePageExamples.lean` | 135 | 10 | 2 | 6 | 0 | T1/T3 root theory/examples |
| `OntologyColimits.lean` | 216 | 4 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `OntologyFields.lean` | 205 | 12 | 7 | 0 | 0 | T1/T3 root theory/examples |
| `OntologyGroups.lean` | 185 | 7 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `OntologyLimits.lean` | 168 | 9 | 8 | 0 | 0 | T1/T3 root theory/examples |
| `OntologySheaves.lean` | 119 | 2 | 4 | 0 | 0 | T1/T3 root theory/examples |
| `OntologyTopology.lean` | 199 | 11 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `Parenting.lean` | 936 | 73 | 54 | 0 | 0 | T1/T3 root theory/examples |
| `ParentingDiagnostics.lean` | 227 | 12 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `ParentingExamples.lean` | 218 | 14 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `Paths.lean` | 567 | 41 | 7 | 0 | 0 | T1/T3 root theory/examples |
| `Periodicity.lean` | 555 | 32 | 18 | 0 | 0 | T1/T3 root theory/examples |
| `PeriodicityReport.lean` | 229 | 28 | 5 | 9 | 0 | T1/T3 root theory/examples |
| `ProgramAlgebra.lean` | 329 | 15 | 8 | 0 | 0 | T1/T3 root theory/examples |
| `Properties.lean` | 248 | 18 | 3 | 0 | 0 | T1/T3 root theory/examples |
| `PropertyConstraints.lean` | 174 | 12 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `PropertyEngine.lean` | 555 | 39 | 23 | 0 | 0 | T1/T3 root theory/examples |
| `Provenance.lean` | 403 | 34 | 21 | 0 | 0 | T1/T3 root theory/examples |
| `Publish.lean` | 273 | 19 | 18 | 0 | 0 | T1/T3 root theory/examples |
| `PublishExamples.lean` | 110 | 14 | 3 | 10 | 0 | T1/T3 root theory/examples |
| `PullbackComparison.lean` | 261 | 10 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `PullbackRetraction.lean` | 655 | 26 | 34 | 0 | 0 | T1/T3 root theory/examples |
| `Qualifiers.lean` | 395 | 32 | 14 | 0 | 0 | T1/T3 root theory/examples |
| `Quantities.lean` | 291 | 29 | 18 | 0 | 0 | T1/T3 root theory/examples |
| `Queries.lean` | 715 | 46 | 32 | 0 | 0 | T1/T3 root theory/examples |
| `RangeConstraints.lean` | 560 | 44 | 23 | 0 | 0 | T1/T3 root theory/examples |
| `Ranks.lean` | 472 | 29 | 12 | 0 | 0 | T1/T3 root theory/examples |
| `Rdf.lean` | 595 | 41 | 19 | 0 | 0 | T1/T3 root theory/examples |
| `Reachability.lean` | 216 | 17 | 4 | 0 | 0 | T1/T3 root theory/examples |
| `Redundancy.lean` | 264 | 23 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `Reflection.lean` | 407 | 25 | 15 | 0 | 0 | T1/T3 root theory/examples |
| `RelatedCorpus.lean` | 185 | 23 | 2 | 18 | 0 | T1/T3 root theory/examples |
| `RelatedNotions.lean` | 128 | 5 | 5 | 4 | 0 | T1/T3 root theory/examples |
| `RelationWords.lean` | 387 | 14 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `Renaming.lean` | 269 | 24 | 0 | 0 | 0 | T1/T3 root theory/examples |
| `RepairExamples.lean` | 266 | 39 | 10 | 0 | 0 | T1/T3 root theory/examples |
| `RepairReview.lean` | 282 | 15 | 16 | 0 | 0 | T1/T3 root theory/examples |
| `RepairWorkflow.lean` | 715 | 51 | 30 | 0 | 0 | T1/T3 root theory/examples |
| `ReportExamples.lean` | 140 | 17 | 0 | 0 | 0 | T1/T3 root theory/examples |
| `ReportFormat.lean` | 390 | 13 | 23 | 0 | 0 | T1/T3 root theory/examples |
| `Reports.lean` | 712 | 25 | 26 | 0 | 0 | T1/T3 root theory/examples |
| `RetractTopology.lean` | 173 | 13 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `Schemas.lean` | 303 | 17 | 14 | 0 | 0 | T1/T3 root theory/examples |
| `SelfDescription.lean` | 260 | 26 | 3 | 0 | 0 | T1/T3 root theory/examples |
| `Semantics.lean` | 328 | 17 | 9 | 0 | 0 | T1/T3 root theory/examples |
| `Series.lean` | 610 | 49 | 28 | 0 | 0 | T1/T3 root theory/examples |
| `SeriesChain.lean` | 198 | 16 | 3 | 0 | 0 | T1/T3 root theory/examples |
| `SeriesDiagnostics.lean` | 269 | 18 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `SeriesExamples.lean` | 129 | 16 | 3 | 0 | 0 | T1/T3 root theory/examples |
| `SeriesRepair.lean` | 706 | 60 | 33 | 0 | 0 | T1/T3 root theory/examples |
| `SeriesRepairExamples.lean` | 219 | 36 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `Showcase.lean` | 466 | 0 | 0 | 0 | 0 | T1/T3 root theory/examples |
| `SignedWords.lean` | 256 | 10 | 6 | 0 | 0 | T1/T3 root theory/examples |
| `Sitelinks.lean` | 283 | 25 | 17 | 0 | 0 | T1/T3 root theory/examples |
| `Snaks.lean` | 398 | 25 | 20 | 0 | 0 | T1/T3 root theory/examples |
| `SoftIdentity.lean` | 289 | 25 | 23 | 0 | 0 | T1/T3 root theory/examples |
| `SpectrumReport.lean` | 341 | 35 | 8 | 20 | 0 | T1/T3 root theory/examples |
| `StatementConstraints.lean` | 485 | 47 | 19 | 0 | 0 | T1/T3 root theory/examples |
| `Stratification.lean` | 281 | 31 | 6 | 0 | 0 | T1/T3 root theory/examples |
| `Subsumption.lean` | 259 | 27 | 12 | 0 | 0 | T1/T3 root theory/examples |
| `Sync.lean` | 239 | 23 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `Taxa.lean` | 557 | 45 | 27 | 0 | 0 | T1/T3 root theory/examples |
| `TaxaDiagnostics.lean` | 287 | 20 | 12 | 0 | 0 | T1/T3 root theory/examples |
| `TaxaExamples.lean` | 154 | 18 | 2 | 0 | 0 | T1/T3 root theory/examples |
| `TaxaLineage.lean` | 339 | 25 | 5 | 0 | 0 | T1/T3 root theory/examples |
| `Taxonomy.lean` | 160 | 18 | 6 | 0 | 0 | T1/T3 root theory/examples |
| `Temporal.lean` | 504 | 30 | 22 | 0 | 0 | T1/T3 root theory/examples |
| `Terms.lean` | 289 | 16 | 18 | 0 | 0 | T1/T3 root theory/examples |
| `TheoryCorpus.lean` | 182 | 20 | 1 | 19 | 0 | T1/T3 root theory/examples |
| `TimeValues.lean` | 332 | 27 | 14 | 0 | 0 | T1/T3 root theory/examples |
| `TypeProperties.lean` | 344 | 27 | 16 | 0 | 0 | T1/T3 root theory/examples |
| `UpperOntology.lean` | 422 | 48 | 11 | 0 | 0 | T1/T3 root theory/examples |
| `Vocabulary.lean` | 251 | 0 | 1 | 0 | 0 | T1/T3 root theory/examples |
| `Wiki/Clean.lean` | 579 | 35 | 13 | 0 | 0 | T4 wiki generation |
| `Wiki/Generate.lean` | 111 | 10 | 4 | 0 | 0 | T4 wiki generation |
| `Wiki/Pages.lean` | 119 | 7 | 7 | 6 | 0 | T4 wiki generation |
| `Wiki/Registry.lean` | 140 | 2 | 7 | 0 | 0 | T4 wiki generation |
| `Wiki/Subst.lean` | 430 | 26 | 6 | 0 | 0 | T4 wiki generation |
| `Wiki/Syntax.lean` | 90 | 0 | 1 | 2 | 0 | T4 wiki generation |
| `Wiki/Template.lean` | 256 | 16 | 10 | 0 | 0 | T4 wiki generation |
| `Wiki/Text.lean` | 530 | 18 | 18 | 0 | 0 | T4 wiki generation |
| `Worklist.lean` | 421 | 24 | 31 | 0 | 0 | T1/T3 root theory/examples |
| `WorklistExamples.lean` | 109 | 11 | 1 | 0 | 0 | T1/T3 root theory/examples |

## Key declaration index

### `Core.lean`
`subclassOf_of_P279`, `subclassOf_trans`, `subclassOf_antisymm`, `level_subclassOf`, `instanceOf_of_P31`, `instanceOf_trans_subclassOf`, `level_instanceOf`, `not_instanceOf_self`, `instanceOf_asymm`, `not_subclassOf_of_instanceOf`, `level_lt_of_transGen_instanceOf`, `instanceOf_acyclic`, `isClass_of_hasInstance`, `isClass_of_subclassOf`, `two_le_level_of_isMetaclass`, `isClass_of_instanceOf_metaclass`, `not_hasInstance_of_isIndividual`, `not_P279_of_isIndividual`, `no_common_instance_of_subclasses`, `not_subclassOf_of_disjointWith`, `not_hasInstance_of_selfDisjoint`

### `Ranks.lean`
`Rank.toNat_injective`, `Rank.eq_of_toNat_eq`, `Rank.toNat_le_two`, `Rank.toNat_le_one`, `Rank.toNat_pos`, `le_foldr_max`, `foldr_max_append`, `foldr_max_eq_zero_or_mem`, `rank_le_bestRankNat`, `exists_rank_eq_bestRankNat`, `truthy_sublist`, `not_isTruthy_deprecated`, `mem_truthyValues_iff`, `exists_isTruthy`, `isTruthy_congr`, `isTruthy_iff_preferred`, `isTruthy_iff_normal_of_no_preferred`, `bestRankNat_append_deprecated`, `truthyValues_append_deprecated`, `truthyValues_append_preferred`, `mem_truthyItemStmts_iff`, `not_mem_truthy_of_deprecated`, `holds_of_mem_truthyItemStmts`, `berlin_population_truthy`, `berlin_country_truthy`, `berlin_truthyItemStmts`, `berlinNoPreferred_population_truthy`, `berlin_drop_deprecated`, `berlin_no_statements`

### `Snaks.lean`
`satisfies_someValue_of_value`, `not_satisfiable_of_value_and_noValue`, `not_satisfiable_of_someValue_and_noValue`, `clashFreeB_iff`, `models_canonical`, `satisfiable_iff_clashFree`, `satisfiable_iff_clashFreeB`, `entails_of_mem`, `entails_mono`, `entails_someValue_of_value`, `models_canonicalPlus`, `entails_noValue_iff`, `entails_someValue_iff`, `mem_valuesOf_iff`, `valuesOf_eq_nil_of_noValue`, `frag_clashFree`, `frag_satisfiable`, `frag_entails_father`, `frag_entails_spouse`, `frag_not_entails_child`, `frag_entails_no_child`, `frag_no_children`, `fragBad_not_clashFree`, `fragBad_unsatisfiable`, `fragBad2_unsatisfiable`

### `Qualifiers.lean`
`List.lookup_eq_some_of_nodup_keys`, `List.lookup_isSome_of_mem`, `qualValue_eq_some_mem`, `qualValue_eq_some_iff_of_nodup`, `qualValue_isSome_of_mem`, `allowedOk_iff`, `mandatoryOk_iff`, `claimOk_iff`, `quals_eq_nil_of_allowed_nil`, `mandatory_subset_allowed`, `not_claimOk_of_mandatory_not_allowed`, `qualValue_isSome_of_mandatory`, `allowedOk_mono`, `mandatoryOk_mono`, `specOf_eq_some_pid`, `specOf_eq_none_iff`, `qualSetOk_iff`, `qualSetOk_of_not_mem_table`, `qualSetOk_sublist`, `qualSetOk_truthy`, `scopeOk_iff`, `no_main_of_scope`, `not_qual_of_scope`, `scopeOk_sublist`, `scopeOk_truthy`, `no_claim_of_qualifier_only`, `berlin_qualSetOk_false`, `berlin_truthy_qualSetOk`, `berlin_scopeOk`, `berlin_bad_scope`, `country_unconstrained`, `berlin_repaired`

### `PropertyEngine.lean`
`mem_superProps`, `succ_eq_subProp`, `pwf_subProp`, `pwf_stmt`, `superProps_subset_allP`, `superProps_eq_empty_of_not_mem`, `isSubPropertyOf_iff`, `isSubPropertyOf_refl`, `supportsB_iff`, `mem_basePairsL_iff`, `mem_stepPairs_iff`, `mem_items_of_supportsB`, `mem_items_of_mem_basePairsL`, `stepPairs_subset_items`, `stepPairs_eq_empty_of_not_mem`, `mem_reach_stepPairs_iff`, `holds_of_supportsB`, `holds_of_mem_basePairsL`, `holds_of_mem_stepPairs`, `holds_of_oneStepB`, `holds_of_chainB`, `holds_of_relatedB`, `supportsB_of_mem_basePairsL`, `basePairsL_mono`, `relatedB_of_mem_basePairsL`, `mem_basePairsL_of_relatedB_of_not_trans`, `chainB_trans`, `relatedB_of_holds`, `relatedB_iff_holds`, `pvalid_base`, `pvalid_pWellFormed`, `pvalid_typeConstraintsOk`, `pvalid_valueTypeConstraintsOk`, `instanceOf_of_typeC`, `instanceOf_of_valueTypeC`, `exists_supportsB_subject`, `exists_supportsB_value`, `subjectTypeOk_of_pvalid`, `valueTypeOk_of_pvalid`

### `Modules.lean`
`mem_depSucc`, `depSucc_eq_dep`, `dep_mem_items`, `depSucc_subset_all`, `depSucc_eq_empty_of_not_mem`, `mem_moduleItemsF_iff`, `seed_mem_moduleItemsF`, `moduleItemsF_closed`, `moduleItemsF_closed_sub`, `moduleItemsF_closed_path`, `moduleItemsF_mono`, `moduleItemsF_subset_items`, `mem_moduleOf_items`, `moduleOf_Sub_iff`, `moduleOf_Inst_iff`, `moduleOf_Sub_le`, `moduleOf_Inst_le`, `moduleOf_disj_le`, `moduleOf_wellFormed`, `moduleOf_isSubclassOf_le`, `moduleOf_isInstanceOf_le`, `moduleOf_reflTransGen_sub`, `moduleOf_isSubclassOf`, `moduleOf_isInstanceOf`, `moduleOf_superclassesOfL`, `moduleOf_classesOf`, `moduleOf_levelsOk`, `moduleOf_acyclic`, `moduleOf_disjointOk`, `moduleOf_valid`, `entails_moduleOf`, `moduleOf_items_self`, `moduleOf_moduleItemsF`

### `CompilerPipeline.lean`
`repaired_corpus`, `compiled_corpus`, `foldl_dropSub_sub_subset`, `pruneRedundant_sub_subset`, `compiled_sub_subset`, `compiled_inst`, `wordStep_compiled_mono`, `compiled_answers_subclass`, `compiled_answers_instance`, `compiled_size`

### `Publish.lean`
`cleanFieldB_of_jsonSafeB`, `quote_notMem_of_jsonSafeB`, `comma_notMem_of_jsonSafeB`, `unquote`, `quote_toList`, `notMem_quote`, `mapM_unquote`, `mapM_unquote`, `parseJsonArray`, `jsonSafe_fields`, `nl_notMem_jsonRow`, `mapM_rows`, `parseJsonl`, `length_kbRecs`, `length_jsonRows`, `eq_of_renderKB_eq`, `cid_congr`, `cid_eq_of_renderKB_eq`, `eq_of_cid_and_render`

### `Archive.lean`
`checkManifest_manifestRows`, `lookup_payload`, `lookup_rows`, `importKB`, `importKB`, `bundle_copies_agree`, `bundleFiles_names_nodup`, `checkManifest_bundleOf`

### `Sync.lean`
`empty_wellFormed`, `equiv_iff`, `equiv_refl`, `equiv_symm`, `equiv_trans`, `wellFormed_sync`, `sync_entails_left`, `sync_entails_right`, `sync_least`, `sync_comm_equiv`, `sync_assoc_equiv`, `sync_idem_equiv`, `entails_empty`, `sync_empty_equiv`, `wellFormed_foldl_merge`, `wellFormed_pool`, `entails_foldl_acc`, `entails_foldl_mem`, `pool_entails_mem`, `gossip_equiv_pool`, `gossip_pairwise_equiv`, `gossip_entails_all`, `gossip_wellFormed`

### `Schemas.lean`
`mem_stmtsOf`, `conformsB_iff`, `specOkB_iff`, `mem_specs_of_conformsB_closed`, `conformsB_meet`, `stmtsOf_addStmts`, `countOf_le_addStmts`, `conformsB_addStmts`, `hasPropertyB_iff_countOf_pos`, `completeFor_iff_conformsB_minShape`, `base_valid`, `adams_conforms`, `other_fails`, `adams_conforms_open`, `adams_still_conforms_open`, `adams_breaks_closed`, `adams_breaks_max`

### `Reflection.lean`
`subclassOf`, `instanceOf`, `reflTransGen_comap`, `comap_subclassOf`, `comap_instanceOf`, `reflTransGen_fst`, `reflTransGen_snd`, `comm`, `lift_unique`, `sec_injective`, `subclassOf_iff`, `instanceOf_iff`, `hasInstance_iff`, `isMetaclass_iff`, `idem_idempotent`, `idem_fixed_iff`, `push_subset_iff`, `subset_pull_push`, `push_pull_subset`, `projection_formula`, `push_mono`, `pull_mono`, `push_extension_subset`, `extension_subset_pull_extension`, `Retract.preimage_extension`

### `Worklist.lean`
`taskKeys_nodup`, `mem_taskKeys_iff`, `tasks_keys`, `tasks_rows_key`, `tasks_rows_ne_nil`, `flatMap_rowsWithKey_perm`, `tasks_flatMap_perm`, `tasks_size_sum`, `tasks_eq_nil_iff`, `Task.errors_add_warnings`, `Task.status_counts`, `Task.automatic_rows_provenFix`, `worklist_perm`, `worklist_sorted`, `worklist_flatMap_perm`, `worklist_size_sum`, `worklist_eq_nil_iff`, `worklistRows_perm`, `htmlSections_eq_htmlText`, `Task.fields_length`, `Task.fields_ne_nil`, `parseCsvText_worklistCsv`, `taskBars_count_sum`, `worklistHtml_rows_length`

### `Reports.lean`
`Row.fields_length`, `preds_eq_empty_of_no_follows`, `isAfterB_of_no_follows`, `sErrors_eq_nil_of_no_series`, `SKB.rows_eq_of_no_series`, `errorRows_eq_nil_iff_valid`, `rows_eq_nil_iff_clean`, `rows_length`, `severity_of_mem_errors`, `severity_of_mem_warnings`, `severity_error_count`, `status_provenFix_iff`, `provenFix_prunable`, `allCodes_nodup`, `rowOfIssue_code_mem`, `rowOfSeriesIssue_code_mem`, `rowOfTaxonIssue_code_mem`, `rowOfKinIssue_code_mem`, `rowOfParentIssue_code_mem`, `count_sum_of_nodup`, `countOf_sum`, `KB.rows_code_mem`, `bars_count_sum`, `Row.fields_ne_nil`, `parseCsvText_csvOfRows`
