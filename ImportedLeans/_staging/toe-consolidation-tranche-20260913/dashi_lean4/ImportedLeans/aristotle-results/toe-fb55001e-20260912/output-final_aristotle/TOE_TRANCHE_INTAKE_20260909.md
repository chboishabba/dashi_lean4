# Intake report — combined NS / YM / RH / TOE Agda source handoff, 2026-09-09

This report records the review and selective import of the source-only Agda
handoff delivered with this round, and the exact provenance of everything
adopted. It is a **source-intake and dependency report, not a proof receipt**:
no Agda toolchain exists in this environment, so nothing in the tranche is
claimed to have been typechecked here, and no physical Clay, Yang–Mills or
Riemann result is asserted anywhere below.

Companion machine-readable artefacts:

* `TOE_TRANCHE_INTAKE_20260909_LEDGER.csv` — one row per adopted path, with
  `sha256` before (for reconciled files) and after.
* `Agda/DASHI/EverythingTrancheIntake20260909.agda` — additive Agda rollup
  naming exactly the 129 newly adopted modules.

---

## 1. Delivery: presence, commit, manifest count, checksum result

| item | value |
|---|---|
| archive present at project root | **yes** — `toe-ns-ym-rh-agda-handoff-20260909.tar.gz` (9 386 463 bytes) |
| archive `sha256` | `860423a0df24e2d5b8e9cf36fa0b8c965638c26c676366bba2484701692eeb78` |
| source commit declared in `HANDOFF.md` | `7f08c070a726a653e9da9419571cafe1b8cbd267` (`chboishabba/dashi_agda`, master, 2026-09-09) |
| `SOURCE_MANIFEST.txt` entries | **6 758** |
| `SHA256SUMS` entries | 6 758 |
| checksum result | **`sha256sum -c SHA256SUMS` → exit 0; 6 758 / 6 758 `OK`, 0 failures, 0 missing** |
| payload actually present | 6 758 `.agda` files under `dashi_agda/`, matching the manifest one-for-one |
| unpack location | beside the project, **not** over it |

### Discrepancy found in the delivery

`HANDOFF.md` states that `ns_worker_result/` "holds the slim, source/documentation
outcome returned by the NS worker: `RateBlockGramBound.lean` and its NS
intake/frontier notes", and instructs the reader to consult
`ns_worker_result/docs/ns-clay-contract/ns-agda-tranche-intake-20260909.md`
before making claims about the NS material.

**That directory is empty in this archive.** `ns_worker_result/` unpacks as a
zero-entry directory; neither `RateBlockGramBound.lean` nor the intake note is
present, and no path under `ns_worker_result/` appears in `SOURCE_MANIFEST.txt`
or in `SHA256SUMS` (`grep -c ns_worker_result` = 0 in both). The checksum pass
is therefore complete with respect to what was shipped, but the NS worker
document the handoff points at **was not shipped**.

Consequently the NS figures quoted in the task — R395–R530 reconciled, 159 new
modules, 36 donor reconciliations, two retained RingSolver repairs, R423
dependency-complete, no Agda toolchain receipt, Package A unclosed — are
recorded here **as reported upstream, unverified from this archive**. I could
not read the cited provenance note because it is absent. Nothing in this round
depends on those figures.

---

## 2. Scope constraint applied

This cutset excludes Yang–Mills and Navier–Stokes material, and that standing
constraint was kept. Concretely, nothing was adopted from
`DASHI/Physics/YangMills/**` or `DASHI/Physics/Closure/**` (the NS closure
family), and every adoption candidate was additionally scanned for `import`
lines *into* those namespaces; three further candidates were rejected on that
ground alone even though their own paths are outside the excluded directories:

| rejected candidate | reason |
|---|---|
| `DASHI/Core/ClayCrossDomainLiteralFrontierExact.agda` (new) | imports `DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact` and `DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact` |
| `DASHI/Wikimedia/ScientificReferenceQidValidation.agda` (new) | 3 imports into the excluded namespaces |
| `DASHI/Physics/NSYMLiteralFrontierSchedulerExact.agda` (new) | NS/YM scheduler |
| `DASHI/Analysis/PreProjectionCancellationBidiCrossPollinationExact.agda`, `DASHI/Analysis/StrictContractionUniqueness.agda`, `DASHI/Interop/PNFTernaryCycleSpectralExact.agda` (donor updates) | donor version adds an import into the excluded namespaces; **local version retained unchanged** |

---

## 3. Disposition of all 6 758 delivered modules

| class | count | action |
|---|---|---|
| byte-identical to a file already in this tree | 5 639 | no action (confirms the shared base) |
| already present, donor differs | 307 | see below |
| absent from this tree | 812 | see below |

Refining the 1 119 non-identical modules:

| class | count | action |
|---|---|---|
| **new, in excluded YM/NS paths** | 607 | not adopted (cutset exclusion) |
| **new, outside YM/NS, but importing YM/NS** | 3 | not adopted |
| **new, outside YM/NS, dependency-incomplete here** | 73 | reviewed, **not adopted** — see table B |
| **new, outside YM/NS, dependency-complete** | **129** | **adopted** (added) |
| **differing, in excluded YM/NS paths** | 201 | not adopted |
| **differing, donor adds a YM/NS import** | 3 | not adopted; local retained |
| **differing, donor drops local declarations** | 10 | reviewed, **local retained** — see table D |
| **differing, donor dependency-incomplete here** | 2 | reviewed, local retained |
| **differing, aggregate whose donor version drops local import lines** | 1 | reviewed, local retained — `DASHI/EverythingAristotleWikidataReciprocalGarden.agda`, see §6 |
| **differing, donor is a safe reconciliation** | **90** | **adopted** (reconciled to donor) |

Totals: **219 modules adopted** (129 added + 90 reconciled), 900 reviewed and
deliberately not adopted, 5 639 already identical.

### Adoption criteria actually used

A donor file was adopted only if **all** of the following held, each checked
mechanically:

1. its path is outside `DASHI/Physics/YangMills/**` and `DASHI/Physics/Closure/**`;
2. it contains no `import` into those namespaces;
3. every `DASHI.*` import it makes resolves, after intake, against a file
   present in this tree (computed as a greatest fixpoint over the whole
   candidate set, so transitive completeness is included);
4. for a file that already existed here, the donor version declares **every**
   top-level name the local version declares and makes **every** `DASHI.*`
   import the local version makes — i.e. the donor cannot silently drop local
   content. This is the same discipline the upstream NS worker reports using
   when it retained its two local RingSolver repairs.

---

## 4. Mechanical receipts

| check | before intake | after intake |
|---|---|---|
| `.agda` files under `Agda/` | 15 569 | 15 698 |
| files scanned by `scripts/agda_import_check.py` under `Agda/DASHI` | 14 028 | 14 157 |
| import lines parsed | 105 718 | 106 727 |
| **unresolved `DASHI.*` imports** | **241 in 67 files** | **241 in 67 files — unchanged** |

The Lean side was untouched by this round, and remains green:
`lake build Synthesis Cuisine Spine Integration Promoted` completes with
**8 458 jobs and no errors** after the intake (the pre-existing, documented
`AgdaMirror` root-aggregate failure, caused by the excluded Yang–Mills module,
is unchanged and outside these targets).

The intake adds 129 modules and 1 009 import lines and introduces **zero** new
unresolved import edges. That is the whole of the mechanical claim: it is
import-graph resolution against shipped files, not elaboration, not
typechecking, and not a kernel receipt.

Content classification of the 219 adopted modules (36 269 lines), by
mechanical scan:

| construct | count |
|---|---|
| `data` declarations | 500 |
| `record` declarations (interfaces) | 606 |
| `postulate` blocks | **0** |
| `{-# TERMINATING #-}` pragmas | **0** |
| `primTrustMe` uses | **0** |
| open goals / holes (`{! !}`, trailing `?`) | **0** |
| Boolean ledger obligations of the form `… ≡ true` | 754 |
| empty-type boundary statements of the form `… → ⊥` | 311 |

So the adopted surface introduces no axioms and no unfinished holes *in source
form*, but 754 of its obligations are Boolean-ledger statements. Per the
handoff's own instruction, and consistently with this corpus's standing
classification, **every one of those route/compiler Boolean interfaces is
conditional bookkeeping**: `f x ≡ true` records that a stipulated finite table
answers positively, and carries no mathematical content about the physical or
analytic premise it is named after.

---

## 5. What the adopted material is, by lane

* **`DASHI/Analysis` — 80 new + 87 reconciled (RH direct cluster).** The
  current direct cluster-response line: `RiemannG2*` pole-quotient /
  finite-near evaluation / quarter-period route material, the
  `RiemannAristotle*` schedulers and frontier records, the
  `NonArchimedean*` spectral obligation family, and the evaluator-independent
  final-near kernel updates the handoff describes. These are finite label
  types, scheduler tables and route ledgers. **No adopted module states, and
  none is read here as stating, a zero-free region, a spectral realisation, or
  any step of a proof of the Riemann hypothesis.**
* **`DASHI/Interop` — 22 new.** ITIR ↔ SensibLaw adapters, the
  Gods-Eye-View world-ontology/acquisition adapters, the source-diligence and
  directional-evidence proof-search bridges, and five Aristotle/Wikidata
  boundary modules (`AristotleRankQualifierPropertyEngineBoundary`,
  `AristotleSnakStatementPresenceBoundaryExact`,
  `AristotleConservativeTypeModuleBoundaryExact`,
  `AristotleConstraintTableCoverageExact`,
  `AristotleEvidenceSurfaceIdentityBoundaryExact`).
* **`DASHI/Wikimedia` — 27 new.** SensibLaw statement-bundle,
  prerequisite-DAG, review-handoff and rate-limited-getter contracts, plus the
  scientific-reference entity atlas and citation-QID bindings.
* **`DASHI/Core` — 2 reconciled**, including `Core/Prelude.agda`, whose donor
  version is strictly additive (re-exports `String`, `cong₂`, `subst`) and is
  required by several adopted modules.
* **`DASHI/Physics` — nothing adopted.**

The full path list with checksums is `TOE_TRANCHE_INTAKE_20260909_LEDGER.csv`;
the non-`Analysis` additions are also listed in table E below.

---

## 6. The reciprocal-garden surface: what upstream has, and why it is not here yet

The most substantive comparison the tranche enables concerns the ten-owner
Aristotle/Wikidata reciprocal garden built on the Lean side in earlier rounds
(`Lean/Integration/Kernel/Aristotle/**`, built and axiom-audited) and returned
as Agda source in `Agda/DASHI/Core/Aristotle*BidiExact.agda`.

Upstream master **has its own Agda counterparts**, and they are not relocations
of the returned files: they live in `DASHI.Interop.Aristotle*BidiExact`, they
cover all ten owners (the five returned plus `RankVisibilityCommutingProvenance`,
`SchemaCoverageProfile`, `CoverageResidualSalience`, `WorklistDeliberativeMoves`,
`ContentIdentityRevisionSync`), and each is a thin instantiation of a *generic*
kernel in `DASHI.Core.*BidiExact` rather than a self-contained module.

**Those generic kernels are absent both from this cutset and from the tranche
itself.** Every one of the ten upstream Interop owners is therefore
dependency-incomplete here and was not adopted:

| upstream Interop owner | generic kernel it needs (missing) |
|---|---|
| `AristotlePropertyFamilyQueryFibreBidiExact` | `DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact` |
| `AristotleSchemaCoverageProfileBidiExact` | `DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact` |
| `AristotleSnakAbsenceInformationLossBidiExact` | `DASHI.Core.PairIndexedInformationLossLocusBidiExact` |
| `AristotleReliableSourceConsumerAdequacyBidiExact` | `DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact` |
| `AristotlePrunedGraphPromotionTransportBidiExact` | `DASHI.Core.PromotionTransportChainBidiExact` |
| `AristotleWikibaseZelphBraidedPromotionBidiExact` | `DASHI.Core.BraidedPromotionTransportBidiExact` |
| `AristotleRankVisibilityCommutingProvenanceBidiExact` | `DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact` |
| `AristotleContentIdentityRevisionSyncBidiExact` | `DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact`, `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` |
| `AristotleCoverageResidualSalienceBidiExact` | `DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact`, `DASHI.Core.ResidualSalienceSchedulerBidiExact` |
| `AristotleWorklistDeliberativeMovesBidiExact` | `DASHI.Core.AskListenObservationProducerBidiExact`, `DASHI.Core.DeliberativeCyberneticLoopBidiExact` |

Their five *boundary* dependencies **were** shippable and are adopted (the five
`Interop/Aristotle…Boundary…Exact` modules in §5), so the intake moves the
frontier from "ten owners with fifteen missing dependencies" to "ten owners with
ten missing generic kernels", each named exactly above.

Because upstream's owners were not adoptable, the two local files that would
have had to be reconciled to them were **retained unchanged**:

* `Agda/DASHI/Core/AristotleWikidataReciprocalGardenValidation.agda` — the
  donor version re-points every regression at the `Interop` owners and would
  have dropped all nine local regression lemmas.
* `Agda/DASHI/EverythingAristotleWikidataReciprocalGarden.agda` — the donor
  rollup drops the five `DASHI.Core.Aristotle*BidiExact` import lines. Both
  local files still resolve; no merge was attempted, because merging in import
  lines to modules that are not present would have manufactured unresolved
  edges.

---

## 7. Frontier — exact remaining obligations

Open, and honestly open:

1. **No Agda kernel receipt exists for any of this**, adopted or pre-existing.
   The environment has no Agda toolchain (`agda` is not installed). Every Agda
   statement in this corpus, including all 219 modules adopted this round, is
   *unvalidated source*. Closing this needs an Agda build off the exact head.
2. **Ten generic `DASHI.Core.*BidiExact` kernels are missing** (§6). Until they
   are shipped or rebuilt, upstream's ten Interop reciprocal-garden owners
   cannot be imported here, and the Agda side of the garden remains the five
   self-contained returned owners.
3. **68 distinct `DASHI.*` modules are absent from both this cutset and the
   tranche**, blocking 75 reviewed modules (tables B and C). These are exactly
   the edges a rebase against upstream master would have to settle.
4. **241 pre-existing unresolved `DASHI.*` import edges in 67 files** remain,
   unchanged by this round (113 Moonshine, 91 Physics of which 65 YM/NS-named
   and out of scope, 14 Cognition, 11 Foundations, 8 Algebra).
5. **Ten files carry an unreconciled divergence** (table D): the donor version
   drops declarations the local version has. Deciding each needs either the
   upstream round history or a kernel, neither available here.
6. **The NS worker document cited by the handoff is missing from the archive**
   (§1). `RateBlockGramBound.lean` was not delivered and has not been reviewed
   here. Package A and the literal periodic Clay regularity target are recorded
   as **unclosed**, on the handoff's own statement; the physical outer-cell
   cancellation obligation is open and nothing in this round touches it.
7. **754 adopted Boolean-ledger obligations are conditional.** None of them has
   an independently checked physical or analytic premise in this tree.

Not attempted, deliberately: adopting anything under the YM/NS paths; editing
any aggregate to make the unresolved-import count smaller; renaming donor
modules so they would fit; and any transport of a Lean receipt onto an Agda
statement.

---

## 8. Provenance summary

Everything adopted this round comes from exactly one source:

```
chboishabba/dashi_agda @ 7f08c070a726a653e9da9419571cafe1b8cbd267
  delivered as toe-ns-ym-rh-agda-handoff-20260909.tar.gz
  sha256 860423a0df24e2d5b8e9cf36fa0b8c965638c26c676366bba2484701692eeb78
  manifest 6758 entries; SHA256SUMS 6758/6758 OK
```

Per-path provenance, including the pre-intake checksum of each of the 90
reconciled files, is in `TOE_TRANCHE_INTAKE_20260909_LEDGER.csv`. The Lean
side of the project was not modified by this round.

---

## Appendix

Tables B, C, D and E follow.
### D. Reviewed, local version retained — donor drops local declarations (10 files)

| path | local declarations absent from the donor version |
|---|---|
| `Agda/DASHI/Analysis/NonArchimedeanSigmaAnchorSameObjectBidiExact.agda` | `sourceAnchorWeldStillLive` |
| `Agda/DASHI/Analysis/NonArchimedeanSpectralBidiObligationExact.agda` | `fullTransferSqrtTwoRejected`, `gibbsUniquenessExactCutset`, `sigmaAnchorSingleWeldCutset`, `stoppingMomentSingleConsumerLeaf`, `unitOneStepContractionRejected`, `universalStoppingSurvivalRejected` |
| `Agda/DASHI/Analysis/NonArchimedeanSpectralOriginalGoalCapstoneExact.agda` | `MixingRepairBoundary`, `SigmaClosureBoundary`, `canonicalMixingRepairBoundary`, `canonicalSigmaClosureBoundary`, `constructiveStoppingTailClosedPositive`, `localAndProlateHalvesDoNotAutoWeld`, `polynomialMomentsRemainConsumerLeaf`, `prefactoredMixingRouteClosedPositive`, `sizeExponentHalfReadingRejected`, `totalVariationRouteClosedPositive`, `unitPrefactorMixingRouteClosedNegative`, `universalHalfLogTwoMGFDomainRejected`, `universalStoppingTailClosedNegative` |
| `Agda/DASHI/Analysis/RiemannAristotlePoleQuotientDirectFiniteNearAttackExact.agda` | `DirectFiniteNearObservation` |
| `Agda/DASHI/Analysis/RiemannAristotleRHAnalyticLeafSchedulerExact.agda` | `evaluationLeafNotYetSchedulable` |
| `Agda/DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerExact.agda` | `clusterMarginRepeatNotSchedulable`, `finiteNearEvaluationSchedulable` |
| `Agda/DASHI/Analysis/RiemannG2HighestAlphaAfter369Exact.agda` | `donorIdentificationNeedsExactIdentity`, `exactProblemIdentityIsRequired`, `ordinaryHarmonicDonorAssumedAvailable`, `sourceRecoveryAloneDoesNotCloseSameObjectScalarAttachment` |
| `Agda/DASHI/Analysis/RiemannG2HighestAlphaAfter8894Exact.agda` | `gammaSourceRecoveryStageIsArtifactRequired`, `genericExplicitFormulaReconstructionNoLongerLive`, `modulationOperationSearchNoLongerLive`, `sameObjectNearFarAttachmentIsCompilerOutput`, `sameObjectWeldIsCompilerOutput`, `separateSelectedNearFarSearchNoLongerLive`, `separateSelectedSameTestSearchNoLongerLive`, `sourceShiftReproofNoLongerLive`, `wholeMellinCarrierEqualityNoLongerLive`, `wholeWeilCarrierEqualityNoLongerLive` |
| `Agda/DASHI/Analysis/RiemannG2QuarterPeriodAnalyticRouteReconciliationExact.agda` | `adaptiveInverseWidthRouteNotRefutedBy8894DensityCut` |
| `Agda/DASHI/Core/AristotleWikidataReciprocalGardenValidation.agda` | `braidedPromotionRegression`, `emptyResultIsNotNoValueRegression`, `lossLocusIsPairRelativeRegression`, `negativeAnswerDoesNotPromoteRegression`, `nonSingletonFibreClosesConsumerRegression`, `patternInFullAbsentInReliableRegression`, `receiptDoesNotDetermineProvenanceRegression`, `soundnessIsNotCompletenessRegression`, `visibleSupportIsNotIndependentSupportRegression` |

### E. Adopted new modules outside `DASHI/Analysis` (49 of 129)

- `Agda/DASHI/Interop/AristotleConservativeTypeModuleBoundaryExact.agda`
- `Agda/DASHI/Interop/AristotleConstraintTableCoverageExact.agda`
- `Agda/DASHI/Interop/AristotleEvidenceSurfaceIdentityBoundaryExact.agda`
- `Agda/DASHI/Interop/AristotleRankQualifierPropertyEngineBoundary.agda`
- `Agda/DASHI/Interop/AristotleSnakStatementPresenceBoundaryExact.agda`
- `Agda/DASHI/Interop/ITIRSuiteNormalizedCompilerParityExact.agda`
- `Agda/DASHI/Interop/ITIRSuiteNormalizedCompilerStageParityWitnessExact.agda`
- `Agda/DASHI/Interop/SensibLawNatDualIdentityConfirmationExact.agda`
- `Agda/DASHI/Interop/SensibLawNatPeerPressureWeldExact.agda`
- `Agda/DASHI/Interop/SensibLawNatSourceMediaMaterializationExact.agda`
- `Agda/DASHI/Interop/SensibLawNatSourcePropositionVerificationExact.agda`
- `Agda/DASHI/Interop/SensibLawNatSourceSupportAcquisitionExact.agda`
- `Agda/DASHI/Interop/SensibLawNatZelphPeerCohortExact.agda`
- `Agda/DASHI/Interop/SensibLawNatZelphPipelineExact.agda`
- `Agda/DASHI/Interop/SensibLawWikibaseZelphItemSurfaceExact.agda`
- `Agda/DASHI/Interop/SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact.agda`
- `Agda/DASHI/Interop/SensibLawWikidataItemPropertyEvidenceExact.agda`
- `Agda/DASHI/Interop/SensibLawWikidataReferenceRoleAuthorityExact.agda`
- `Agda/DASHI/Interop/SensibLawWikidataRequiredPropertyCoverageExact.agda`
- `Agda/DASHI/Interop/SourceAttributionShapePolicyExact.agda`
- `Agda/DASHI/Interop/ZelphBoundedGraphCoverageExact.agda`
- `Agda/DASHI/Interop/ZelphPrunedArtifactQueryPreservationExact.agda`
- `Agda/DASHI/Wikimedia/AristotleNativeModelSourceExact.agda`
- `Agda/DASHI/Wikimedia/ConceptEntityAlignmentExact.agda`
- `Agda/DASHI/Wikimedia/IdentifierExact.agda`
- `Agda/DASHI/Wikimedia/MaboConcreteQidGraphProjectionExact.agda`
- `Agda/DASHI/Wikimedia/MaboNativeWikimediaBridgeExact.agda`
- `Agda/DASHI/Wikimedia/MaboPropertyTripleProjectionExact.agda`
- `Agda/DASHI/Wikimedia/NativeConcreteQidGraphProjectionExact.agda`
- `Agda/DASHI/Wikimedia/NativeEpistemicProjectionExact.agda`
- `Agda/DASHI/Wikimedia/NativePropertyTripleProjectionExact.agda`
- `Agda/DASHI/Wikimedia/NativeReferenceAttributedSourceBridgeExact.agda`
- `Agda/DASHI/Wikimedia/NativeReferenceSemanticsExact.agda`
- `Agda/DASHI/Wikimedia/NativeSnakPNFLogicalForceExact.agda`
- `Agda/DASHI/Wikimedia/NativeStatementExact.agda`
- `Agda/DASHI/Wikimedia/SLRP854ExternalReferenceInspectionABIExact.agda`
- `Agda/DASHI/Wikimedia/SLRWikimediaHandoffABIExact.agda`
- `Agda/DASHI/Wikimedia/ScientificCitationQidBindingsExact.agda`
- `Agda/DASHI/Wikimedia/ScientificReferenceEntityAtlasExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawBoundaryArtifactMorphismExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawNatClimateReviewHandoffExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawNatClimateSLRFixtureExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawNatObservationClaimSLRExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawSourceUnitReviewHandoffExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawStatementBundleDiagnosisProofSearchExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawStatementBundleSparseReopenExact.agda`
- `Agda/DASHI/Wikimedia/SensibLawWikipediaIngestContractExact.agda`
- `Agda/DASHI/Wikimedia/SourceProvenanceExact.agda`
- `Agda/DASHI/Wikimedia/WikidataPNFPredicateBridgeExact.agda`

### B. Reviewed, not adopted — unresolved external dependency (75 modules)

| module | missing `DASHI.*` dependency (absent from this cutset *and* from the tranche) |
|---|---|
| `DASHI.Analysis.RiemannAristotleSharedCertificateREADME` | `DASHI.Core.TwoChannelAllowanceCompositionExact` |
| `DASHI.Analysis.RiemannG2AllowancePaymentsToAnalyticCoresExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` |
| `DASHI.Analysis.RiemannG2CertifiedFiniteNearDirectCombinedOffAnalyticCoreExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` |
| `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` | `DASHI.Core.ProofCarryingFiniteSumEnclosureExact` |
| `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` |
| `DASHI.Analysis.RiemannG2CertifiedNearUpperClusterResponseCompilerExact` | `DASHI.Core.ProofCarryingFiniteSumEnclosureExact` |
| `DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` |
| `DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresRegression` | `DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact` |
| `DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact` | `DASHI.Core.ProofCarryingFiniteSumEnclosureExact` |
| `DASHI.Analysis.RiemannG2FinalOffMinimalCutRegression` | `DASHI.Core.TwoChannelAllowanceCompositionExact` |
| `DASHI.Analysis.RiemannG2LeastPrivilegeClayCutsetExact` | `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact` |
| `DASHI.Analysis.RiemannG2PoleQuotientOffCoreAllowanceBridgeExact` | `DASHI.Core.TwoChannelAllowanceCompositionExact` |
| `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` |
| `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerRegression` | `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact` |
| `DASHI.Analysis.RiemannG2UniformCertifiedPrizeCompilerExact` | `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact` |
| `DASHI.Analysis.RiemannG2UniformTargetZeroCertifiedCaseGeneratorExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` |
| `DASHI.Analysis.RiemannZetaDirectTerminalCompilerExact` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` |
| `DASHI.Analysis.RiemannZetaDirectTerminalCompilerRegression` | `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` |
| `DASHI.Analysis.RiemannZetaLiteralFrontierSchedulerExact` | `DASHI.Core.LiteralFrontierSchedulerExact`, `DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact` |
| `DASHI.Core.AristotleFrontierWorklistTruthMaintenanceBridgeExact` | `DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact`, `DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact` |
| `DASHI.Interop.AristotleContentIdentityRevisionSyncBidiExact` | `DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact`, `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` |
| `DASHI.Interop.AristotleCoverageResidualSalienceBidiExact` | `DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact`, `DASHI.Core.ResidualSalienceSchedulerBidiExact` |
| `DASHI.Interop.AristotlePropertyFamilyQueryFibreBidiExact` | `DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact` |
| `DASHI.Interop.AristotlePrunedGraphPromotionTransportBidiExact` | `DASHI.Core.PromotionTransportChainBidiExact` |
| `DASHI.Interop.AristotleRankVisibilityCommutingProvenanceBidiExact` | `DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact` |
| `DASHI.Interop.AristotleReliableSourceConsumerAdequacyBidiExact` | `DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact` |
| `DASHI.Interop.AristotleSchemaCoverageProfileBidiExact` | `DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact` |
| `DASHI.Interop.AristotleSnakAbsenceInformationLossBidiExact` | `DASHI.Core.PairIndexedInformationLossLocusBidiExact` |
| `DASHI.Interop.AristotleWikibaseZelphBraidedPromotionBidiExact` | `DASHI.Core.BraidedPromotionTransportBidiExact` |
| `DASHI.Interop.AristotleWorklistDeliberativeMovesBidiExact` | `DASHI.Core.AskListenObservationProducerBidiExact`, `DASHI.Core.DeliberativeCyberneticLoopBidiExact` |
| `DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact` | `DASHI.Core.ConsumerFibreRefinementSchedulerExact`, `DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact` |
| `DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact` | `DASHI.Core.DialecticalMaterialFutureSafetyExact`, `DASHI.Core.DialecticalMaterialRevisionExact`, `DASHI.Law.SensibLawProofDirectedSearchIntentExact` |
| `DASHI.Interop.DirectionalEvidenceProofSearchBridgeExact` | `DASHI.Statistics.DirectionalEvidenceTritExact` |
| `DASHI.Interop.Everything` | `DASHI.Law.HerzogAmalekAttributedSourceAtlasExact` |
| `DASHI.Interop.FormalisationGovernanceAttributedSourceMigrationExact` | `DASHI.Interop.SourceDiligenceProofSearchBridgeExact` |
| `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` | `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact` |
| `DASHI.Interop.GodsEyeViewActivistThreatAtlasExact` | `DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact` |
| `DASHI.Interop.GodsEyeViewCommunitySourceWorldAdapterExact` | `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` |
| `DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact` | `DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact` |
| `DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact` | `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact` |
| `DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact` | `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact` |
| `DASHI.Interop.GodsEyeViewLESSensorWorldAdapterExact` | `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` |
| `DASHI.Interop.GodsEyeViewMarketAcquisitionWorldAdapterExact` | `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` |
| `DASHI.Interop.GodsEyeViewMarketAgroecologyInternationalAccountabilityExact` | `DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact` |
| `DASHI.Interop.GodsEyeViewP854InspectionWorldAdapterExact` | `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` |
| `DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact` | `DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact`, `DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact` |
| `DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact` | `DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact` |
| `DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact` | `DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact` |
| `DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExact` | `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact` |
| `DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExtendedExact` | `DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExact` |
| `DASHI.Interop.GodsEyeViewWorldOntologyCrossDomainExact` | `DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact`, `DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact` |
| `DASHI.Interop.GodsEyeViewWorldResearchFrontierActionExact` | `DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact` |
| `DASHI.Interop.GravitationalAttributionProofSearchBridgeExact` | `DASHI.Law.SensibLawProofDirectedSearchIntentExact`, `DASHI.Physics.GR.GravitationalEpistemicLineageExact` |
| `DASHI.Interop.GravitationalObservationProofSearchBridgeExact` | `DASHI.Law.SensibLawProofDirectedSearchIntentExact`, `DASHI.Physics.GR.GravitationalObservationBidiExact` |
| `DASHI.Interop.GravitationalObservationUnificationBidiCrossPollinationExact` | `DASHI.Law.SensibLawProofDirectedSearchIntentExact`, `DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact`, `DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact`, `DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact`, `DASHI.Physics.GR.GravitationalObservationBidiExact`, `DASHI.Physics.GR.GravitationalPredictionObservationBidiExact`, `DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact` |
| `DASHI.Interop.ITIRHealthRecordSensibLawAdapterExact` | `DASHI.Core.SourceConditionedObservationExact`, `DASHI.Law.SensibLawHealthRecordEvidenceExact`, `DASHI.Law.SensibLawLongitudinalHousingHealthExact` |
| `DASHI.Interop.ITIRHousingEpisodeSensibLawAdapterExact` | `DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact` |
| `DASHI.Interop.ITIRLaterMedicalParticularHarmSensibLawAdapterExact` | `DASHI.Law.SensibLawLaterMedicalParticularHarmSourceConditionedExact` |
| `DASHI.Interop.ITIRRecordingManifestSensibLawAdapterExact` | `DASHI.Law.SensibLawRecordingManifestLineageExact` |
| `DASHI.Interop.ITIRSubmittedEvidencePackageSensibLawAdapterExact` | `DASHI.Law.SensibLawSubmittedEvidencePackageWrongTypeExact`, `DASHI.Law.SensibLawWrongTypeCausationElementExact` |
| `DASHI.Interop.ITIRTemporalHealthSensibLawAdapterExact` | `DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact`, `DASHI.Law.SensibLawWrongTypeCausationElementExact` |
| `DASHI.Interop.IntrospectiveProofLoopExact` | `DASHI.Core.BoundAcquisitionDemandExact`, `DASHI.Core.ConsumerFibreRefinementSchedulerExact`, `DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact`, `DASHI.Law.SensibLawProofDirectedSearchIntentExact` |
| `DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact` | `DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact`, `DASHI.Core.NDimParetoHyperfabricExact`, `DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact` |
| `DASHI.Interop.SensibLawNatCoverageAcquisitionDemandExact` | `DASHI.Law.SensibLawProofDirectedSearchIntentExact` |
| `DASHI.Interop.SensibLawWikidataTernaryAdmissibilityValidation` | `DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact` |
| `DASHI.Interop.SourceDiligenceProofSearchBridgeExact` | `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact`, `DASHI.Law.SensibLawProofDirectedSearchIntentExact` |
| `DASHI.Wikimedia.Everything` | `DASHI.Wikimedia.SensibLawStatementBundleHistoricalResponsibilityExact`, `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` |
| `DASHI.Wikimedia.ScientificReferenceResidualAcquisitionExact` | `DASHI.Law.SensibLawProofDirectedSearchIntentExact` |
| `DASHI.Wikimedia.SensibLawNatBatchPrerequisiteRunnerContractExact` | `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` |
| `DASHI.Wikimedia.SensibLawRateLimitedParallelGetterExact` | `DASHI.Wikimedia.SensibLawSharedAcquisitionExecutionExact` |
| `DASHI.Wikimedia.SensibLawSharedAcquisitionExecutionExact` | `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` |
| `DASHI.Wikimedia.SensibLawStatementBundleHistoricalResponsibilityExact` | `DASHI.Core.HistoricalFirstFailureTraceBidiExact`, `DASHI.Core.HistoricalProducerResponsibilityTraceBidiExact`, `DASHI.Core.HistoricalResponsibilityLineageTraceBidiExact`, `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` |
| `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` | `DASHI.Core.QueryPromotionResidualBidiExact`, `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` |
| `DASHI.Wikimedia.SensibLawZelphHFPrerequisiteBridgeExact` | `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` |
| `DASHI.Wikimedia.SensibLawZelphHFSelectorResultPaymentExact` | `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` |

### C. The 68 distinct blocking dependencies, by demand

| missing module | modules blocked |
|---|---|
| `DASHI.Law.SensibLawProofDirectedSearchIntentExact` | 8 |
| `DASHI.Core.EmpiricalSourceDiligenceAdmissionExact` | 5 |
| `DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact` | 5 |
| `DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact` | 4 |
| `DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact` | 4 |
| `DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact` | 4 |
| `DASHI.Core.TwoChannelAllowanceCompositionExact` | 3 |
| `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` | 3 |
| `DASHI.Core.ProofCarryingFiniteSumEnclosureExact` | 3 |
| `DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact` | 3 |
| `DASHI.Core.ConsumerFibreRefinementSchedulerExact` | 2 |
| `DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact` | 2 |
| `DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact` | 2 |
| `DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact` | 2 |
| `DASHI.Physics.GR.GravitationalObservationBidiExact` | 2 |
| `DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact` | 2 |
| `DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact` | 2 |
| `DASHI.Law.SensibLawWrongTypeCausationElementExact` | 2 |
| `DASHI.Core.PairIndexedInformationLossLocusBidiExact` | 1 |
| `DASHI.Core.BraidedPromotionTransportBidiExact` | 1 |
| `DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact` | 1 |
| `DASHI.Core.ResidualSalienceSchedulerBidiExact` | 1 |
| `DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact` | 1 |
| `DASHI.Core.NDimParetoHyperfabricExact` | 1 |
| `DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact` | 1 |
| `DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact` | 1 |
| `DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact` | 1 |
| `DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact` | 1 |
| `DASHI.Core.QueryPromotionResidualBidiExact` | 1 |
| `DASHI.Core.HistoricalFirstFailureTraceBidiExact` | 1 |
| `DASHI.Core.HistoricalProducerResponsibilityTraceBidiExact` | 1 |
| `DASHI.Core.HistoricalResponsibilityLineageTraceBidiExact` | 1 |
| `DASHI.Core.SourceConditionedObservationExact` | 1 |
| `DASHI.Law.SensibLawHealthRecordEvidenceExact` | 1 |
| `DASHI.Law.SensibLawLongitudinalHousingHealthExact` | 1 |
| `DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact` | 1 |
| `DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact` | 1 |
| `DASHI.Core.AskListenObservationProducerBidiExact` | 1 |
| `DASHI.Core.DeliberativeCyberneticLoopBidiExact` | 1 |
| `DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact` | 1 |
| `DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact` | 1 |
| `DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact` | 1 |
| `DASHI.Physics.GR.GravitationalPredictionObservationBidiExact` | 1 |
| `DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact` | 1 |
| `DASHI.Law.HerzogAmalekAttributedSourceAtlasExact` | 1 |
| `DASHI.Statistics.DirectionalEvidenceTritExact` | 1 |
| `DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact` | 1 |
| `DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact` | 1 |
| `DASHI.Core.DialecticalMaterialFutureSafetyExact` | 1 |
| `DASHI.Core.DialecticalMaterialRevisionExact` | 1 |
| `DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact` | 1 |
| `DASHI.Core.LiteralFrontierSchedulerExact` | 1 |
| `DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact` | 1 |
| `DASHI.Law.SensibLawLaterMedicalParticularHarmSourceConditionedExact` | 1 |
| `DASHI.Law.SensibLawSubmittedEvidencePackageWrongTypeExact` | 1 |
| `DASHI.Core.PromotionTransportChainBidiExact` | 1 |
| `DASHI.Law.SensibLawRecordingManifestLineageExact` | 1 |
| `DASHI.Core.BoundAcquisitionDemandExact` | 1 |
| `DASHI.Physics.GR.GravitationalEpistemicLineageExact` | 1 |
| `DASHI.Wikimedia.SensibLawStatementBundleHistoricalResponsibilityExact` | 1 |
| `DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact` | 1 |
| `DASHI.Interop.GodsEyeViewWorldEpistemicSourceAtlasExact` | 1 |
| `DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact` | 1 |
| `DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact` | 1 |
| `DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact` | 1 |
| `DASHI.Interop.SourceDiligenceProofSearchBridgeExact` | 1 |
| `DASHI.Wikimedia.SensibLawSharedAcquisitionExecutionExact` | 1 |
| `DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact` | 1 |
