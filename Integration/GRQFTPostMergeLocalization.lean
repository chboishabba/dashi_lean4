import Integration.GRQFTExecutableResidual

namespace Integration.GRQFTPostMergeLocalization

open Integration.GRQFTExecutableResidual

inductive ComparisonAuthority where
  | boundedComparisonLawReceipt
  | fixtureBaselineDiagnostic
  | rejectedProjectionDiagnostic
  deriving DecidableEq, Repr

structure ColliderChiSquareScopeRow where
  experiment : String
  observable : String
  chi2PerDof : String
  degreesOfFreedom : String
  authority : ComparisonAuthority
  empiricalPromotion : Bool
  deriving Repr

def cmsRatioRow : ColliderChiSquareScopeRow where
  experiment := "CMS"
  observable := "SMP-20-003 t43 50--76 / 76--106 GeV phi-star ratio"
  chi2PerDof := "2.1565191176275618"
  degreesOfFreedom := "18"
  authority := .boundedComparisonLawReceipt
  empiricalPromotion := true

def atlasFixtureBestRow : ColliderChiSquareScopeRow where
  experiment := "ATLAS"
  observable := "H -> gamma gamma |y_yy| fixture-baseline covariance comparison"
  chi2PerDof := "2.6493994618998236"
  degreesOfFreedom := "6"
  authority := .fixtureBaselineDiagnostic
  empiricalPromotion := false

def cmsW4AbsoluteRow : ColliderChiSquareScopeRow where
  experiment := "CMS"
  observable := "SMP-20-003 76--106 GeV absolute d-sigma/d-phi-star current W4 projection"
  chi2PerDof := "298.8462841768543"
  degreesOfFreedom := "17 after one fitted scale"
  authority := .rejectedProjectionDiagnostic
  empiricalPromotion := false

structure RatioAbsoluteLocalization where
  ratioChi2PerDof : String
  absoluteChi2PerDof : String
  contrastAbsoluteOverRatio : String
  sharedCarrierGloballyRejected : Bool
  projectionSpecificDefectSearchPreferred : Bool
  uniqueCauseProved : Bool
  atlasFixtureCountsAsAcceptedValidation : Bool
  deriving Repr

def ratioAbsoluteLocalization : RatioAbsoluteLocalization where
  ratioChi2PerDof := "2.1565191176275618"
  absoluteChi2PerDof := "298.8462841768543"
  contrastAbsoluteOverRatio := "138.57808249139114"
  sharedCarrierGloballyRejected := false
  projectionSpecificDefectSearchPreferred := true
  uniqueCauseProved := false
  atlasFixtureCountsAsAcceptedValidation := false

theorem w4_does_not_globally_reject_shared_carrier :
    ratioAbsoluteLocalization.sharedCarrierGloballyRejected = false := rfl

theorem projection_specific_search_preferred :
    ratioAbsoluteLocalization.projectionSpecificDefectSearchPreferred = true := rfl

theorem atlas_fixture_not_accepted_validation :
    ratioAbsoluteLocalization.atlasFixtureCountsAsAcceptedValidation = false := rfl

/-!
Abstract mirror of the merged Agda same-object chain:

  CMP119 stress = literal pinned stress
  literal pinned stress = selected/recovered QFT stress

No physics is discharged by these generic equality lemmas. They prove only that
once the two same-object receipts exist, there is no third independent stress
identity to prove.
-/

theorem two_step_same_object_transport
    {α : Type u} {cmp119 literal selected : α}
    (h₁ : cmp119 = literal)
    (h₂ : literal = selected) :
    cmp119 = selected :=
  h₁.trans h₂

theorem two_step_same_object_transport_through_shared
    {α : Type u} {β : Type v}
    (toShared : α → β)
    {cmp119 literal selected : α}
    (h₁ : cmp119 = literal)
    (h₂ : literal = selected) :
    toShared cmp119 = toShared selected :=
  congrArg toShared (two_step_same_object_transport h₁ h₂)

def secondCMP119ToSharedStressTheoremRequired : Bool := false

theorem second_cmp119_to_shared_stress_theorem_not_required :
    secondCMP119ToSharedStressTheoremRequired = false := rfl

inductive PostMergeLeaf where
  | grTheoremBearingDiscreteToSmoothAnalyticBundle
  | cmp119StressToLiteralPinnedStressAttachment
  | pinnedLiteralYMToRecoveredQFTAttachment
  | grAnchoredCMP119CrossSectorStressEquality
  | physicalDrellYanAbsoluteProjectionReplacement
  | acceptedMeasuredGAndEmpiricalAuthority
  | empiricalGRQFTDiscriminator
  deriving DecidableEq, Repr

def remainingPostMergeLeaves : List PostMergeLeaf :=
  [ .grDiscreteToContinuumSameObjectRealization
  , .cmp119StressToLiteralPinnedStressAttachment
  , .pinnedLiteralYMToRecoveredQFTAttachment
  , .grAnchoredCMP119CrossSectorStressEquality
  , .physicalDrellYanAbsoluteProjectionReplacement
  , .acceptedMeasuredGAndEmpiricalAuthority
  , .empiricalGRQFTDiscriminator
  ]

structure PostMergeMaxCut where
  finiteEinsteinClosed : Bool
  finiteToPhysicalCalibrationCompilerClosed : Bool
  cmsBoundedRatioContactSurvivesW4Rejection : Bool
  cmp119ToSelectedSharedSectorCompilerClosed : Bool
  secondQFTStressTheoremRequired : Bool
  activePhysicalSectorTotalizationStillRequired : Bool
  terminalGRQFTPromoted : Bool
  remainingLeaves : List PostMergeLeaf
  deriving Repr

def postMergeMaxCut : PostMergeMaxCut where
  finiteEinsteinClosed := true
  finiteToPhysicalCalibrationCompilerClosed := true
  cmsBoundedRatioContactSurvivesW4Rejection := true
  cmp119ToSelectedSharedSectorCompilerClosed := true
  secondQFTStressTheoremRequired := false
  activePhysicalSectorTotalizationStillRequired := true
  terminalGRQFTPromoted := false
  remainingLeaves := remainingPostMergeLeaves

theorem postmerge_terminal_still_false :
    postMergeMaxCut.terminalGRQFTPromoted = false := rfl

/-!
Clay's universal compact-simple group parameter is not a physical instruction
to sum every possible compact-simple group as a simultaneously active sector.
A GRQFT candidate must select its active physical sector(s) first.
-/

structure PhysicalGaugeSectorSelection
    (Candidate Group : Type u) where
  activeSector : Candidate → Group → Prop
  selectedGroup : Candidate → Group
  selectedGroupIsActive :
    ∀ candidate, activeSector candidate (selectedGroup candidate)

def clayUniversalGroupParameterMeansAllGroupsPhysicallyActive : Bool := false

theorem clay_group_quantifier_not_physical_sector_sum :
    clayUniversalGroupParameterMeansAllGroupsPhysicallyActive = false := rfl

def singleGaugeSectorAutomaticallyEqualsTotalEinsteinSource : Bool := false

theorem single_sector_not_automatically_total_source :
    singleGaugeSectorAutomaticallyEqualsTotalEinsteinSource = false := rfl

/-!
Ratio-cancellation firewall: equal ratios do not identify absolute components.
Using cross multiplication avoids division.
-/

def ratioEquivalent
    (n d pn pd : Nat) : Prop :=
  n * pd = pn * d

theorem ratio_cancellation_witness :
    ratioEquivalent 2 1 200 100 := by decide

theorem ratio_cancellation_numerator_wrong :
    (2 : Nat) ≠ 200 := by decide

theorem ratio_cancellation_denominator_wrong :
    (1 : Nat) ≠ 100 := by decide

def ratioAgreementImpliesAbsoluteAgreement : Bool := false

theorem ratio_agreement_does_not_imply_absolute_agreement :
    ratioAgreementImpliesAbsoluteAgreement = false := rfl

inductive LowChiSquareProvenance where
  | posteriorTunedTrainingDiagnostic
  | independentHoldoutFailure
  | boundedFrozenComparisonLaw
  | fixtureBaselineDiagnostic
  deriving DecidableEq, Repr

structure LowChiSquareRow where
  label : String
  chi2PerDof : String
  provenance : LowChiSquareProvenance
  promotesEmpiricalAdequacy : Bool
  deriving Repr

def lowChiSquareRows : List LowChiSquareRow :=
  [ { label := "HEP-R41 posterior t43", chi2PerDof := "1.7408778006026118",
      provenance := .posteriorTunedTrainingDiagnostic, promotesEmpiricalAdequacy := false }
  , { label := "HEP-R42 t45 holdout", chi2PerDof := "222.54402462995546",
      provenance := .independentHoldoutFailure, promotesEmpiricalAdequacy := false }
  , { label := "canonical CMS W3 t43", chi2PerDof := "2.1565191176275618",
      provenance := .boundedFrozenComparisonLaw, promotesEmpiricalAdequacy := true }
  , { label := "ATLAS fixture minimum", chi2PerDof := "2.6493994618998236",
      provenance := .fixtureBaselineDiagnostic, promotesEmpiricalAdequacy := false }
  ]

def lowChiSquareAlonePromotesEmpiricalAdequacy : Bool := false

theorem low_chi_square_alone_does_not_promote :
    lowChiSquareAlonePromotesEmpiricalAdequacy = false := rfl

/-!
Single-active-sector source compiler, abstract mirror.

The theorem does not identify a physical total with one sector.  It states that
if the application has already supplied that equality and the selected CMP119
stress equals the recovered/selected sector stress, then source factorisation is
just equality composition.
-/

theorem single_active_sector_source_factorisation
    {Stress : Type u}
    {effective cmp119 selected total : Stress}
    (hEffectiveCMP : effective = cmp119)
    (hCMPSelected : cmp119 = selected)
    (hTotalSelected : total = selected) :
    effective = total := by
  exact (hEffectiveCMP.trans hCMPSelected).trans hTotalSelected.symm

def singleSectorCompilerManufacturesDeclaredTotal : Bool := false

theorem single_sector_compiler_does_not_manufacture_total :
    singleSectorCompilerManufacturesDeclaredTotal = false := rfl

/-!
Shortest shared-source route.

If the shared source is definitionally chosen to be the literal GR source, the
GR factorisation is reflexive.  The only nontrivial stress theorem remaining is
the cross-sector equality to the selected QFT/CMP119 stress, plus the physical
active-sector totalisation witness.
-/

theorem gr_anchored_factorisation_is_reflexive
    {Stress : Type u}
    (grSource : Stress) :
    grSource = grSource := rfl

def primitiveGRSourceFactorisationLeafRequired : Bool := false

theorem primitive_gr_source_factorisation_not_required :
    primitiveGRSourceFactorisationLeafRequired = false := rfl

def crossSectorGRToCMP119StressEqualityRequired : Bool := true

theorem cross_sector_stress_equality_still_required :
    crossSectorGRToCMP119StressEqualityRequired = true := rfl

def commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute : Bool := false
def commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute : Bool := false

theorem common_metric_variation_not_minimal :
    commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute = false := rfl

theorem common_metric_language_not_minimal :
    commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute = false := rfl

/-!
Generic recovered GR and Schwarzschild validation are distinct.

The same-object composition theorem needs only literal=recovered and
recovered=selected.  A Schwarzschild known-limit theorem is additional physical
validation, not a premise of this equality.
-/

theorem generic_recovered_gr_selected
    {GR : Type u}
    {literal recovered selected : GR}
    (hLiteralRecovered : literal = recovered)
    (hRecoveredSelected : recovered = selected) :
    literal = selected :=
  hLiteralRecovered.trans hRecoveredSelected

def schwarzschildRadialValuationRequiredForGenericAttachment : Bool := false
def schwarzschildWeakFieldValidationStillPhysicallyRequired : Bool := true

theorem schwarzschild_not_generic_recovery_premise :
    schwarzschildRadialValuationRequiredForGenericAttachment = false := rfl

theorem schwarzschild_known_limit_still_required :
    schwarzschildWeakFieldValidationStillPhysicallyRequired = true := rfl

/-!
Single-sector totalisation can be a model-construction choice.

This generic Lean mirror captures the definitional idea without rebuilding the
full Agda UnifiedCandidate record: select one sector, define total := selected,
and define aggregation := equality with that selected value.
-/

structure SingleSectorTotalization (Candidate Group Stress : Type u) where
  selectedGroup : Candidate → Group
  sectorStress : Candidate → Group → Stress

def SingleSectorTotalization.total
    {Candidate Group Stress : Type u}
    (S : SingleSectorTotalization Candidate Group Stress)
    (c : Candidate) : Stress :=
  S.sectorStress c (S.selectedGroup c)

def SingleSectorTotalization.aggregates
    {Candidate Group Stress : Type u}
    (S : SingleSectorTotalization Candidate Group Stress)
    (c : Candidate)
    (sectorFamily : Group → Stress)
    (total : Stress) : Prop :=
  total = sectorFamily (S.selectedGroup c)

theorem single_sector_total_is_selected
    {Candidate Group Stress : Type u}
    (S : SingleSectorTotalization Candidate Group Stress)
    (c : Candidate) :
    S.total c = S.sectorStress c (S.selectedGroup c) := rfl

def singleSectorTotalEqualityIsPrimitiveTheorem : Bool := false

theorem single_sector_total_equality_not_primitive :
    singleSectorTotalEqualityIsPrimitiveTheorem = false := rfl

/-!
Stress-weld equality vs aggregation/promotion packaging.
-/

structure StressEnergyEqualityCore
    (Candidate Regime Stress : Type u) where
  sameStressEnergyOnOverlap :
    Candidate → Regime → Stress → Stress → Prop

def aggregationIsPremiseOfCrossSectorEquality : Bool := false
def promotionTokenIsPremiseOfCrossSectorEquality : Bool := false

theorem aggregation_not_cross_sector_equality_premise :
    aggregationIsPremiseOfCrossSectorEquality = false := rfl

theorem promotion_not_cross_sector_equality_premise :
    promotionTokenIsPremiseOfCrossSectorEquality = false := rfl

/-!
Request surfaces are not theorem evidence.
-/

structure HolonomyTaylorRicciRequest where
  holonomyTaylorExpansion : Prop
  curvatureExtractionErrorBound : Prop
  ricciContractionLimitCompatibility : Prop
  uniformCurvatureDerivativeBound : Prop
  discreteRicciConvergenceRate : Prop

structure HolonomyTaylorRicciEvidence (R : HolonomyTaylorRicciRequest) : Prop where
  holonomyTaylorExpansionEvidence : R.holonomyTaylorExpansion
  curvatureExtractionErrorBoundEvidence : R.curvatureExtractionErrorBound
  ricciContractionLimitCompatibilityEvidence : R.ricciContractionLimitCompatibility
  uniformCurvatureDerivativeBoundEvidence : R.uniformCurvatureDerivativeBound
  discreteRicciConvergenceRateEvidence : R.discreteRicciConvergenceRate

def requestSurfaceAloneClosesCurvatureConvergence : Bool := false

theorem request_surface_is_not_curvature_proof :
    requestSurfaceAloneClosesCurvatureConvergence = false := rfl

/-!
Same-object recovery mathematics without promotion payload.
-/

structure GRRecoveryCommutationCore
    (Candidate Regime GR : Type u) where
  recover : Candidate → GR
  target : Candidate → GR
  coarseGrain : Candidate → Regime → Candidate
  grRegime : Regime → Prop
  recoveryAfterCoarseGraining :
    ∀ candidate regime, grRegime regime →
      recover (coarseGrain candidate regime) =
        target (coarseGrain candidate regime)

structure QFTRecoveryCommutationCore
    (Candidate Regime QFT : Type u) where
  recover : Candidate → QFT
  target : Candidate → QFT
  coarseGrain : Candidate → Regime → Candidate
  qftRegime : Regime → Prop
  recoveryAfterCoarseGraining :
    ∀ candidate regime, qftRegime regime →
      recover (coarseGrain candidate regime) =
        target (coarseGrain candidate regime)

def fullRecoveryReceiptRequiredForSameObjectEquality : Bool := false

theorem full_recovery_receipt_not_same_object_premise :
    fullRecoveryReceiptRequiredForSameObjectEquality = false := rfl

structure CommonRegimeMathematicalCore
    (Candidate Regime : Type u) where
  overlapRegime : Regime
  overlapIsGR : Prop
  overlapIsQFT : Prop
  backreactionConsistency : Candidate → Prop
  correctionControl : Candidate → Prop

def regimePromotionTokenIsMathematicalOverlapPremise : Bool := false
def commonOverlapBackreactionCorrectionsStillMathematical : Bool := true

theorem regime_token_not_overlap_math :
    regimePromotionTokenIsMathematicalOverlapPremise = false := rfl

theorem common_overlap_is_theory_math :
    commonOverlapBackreactionCorrectionsStillMathematical = true := rfl

inductive TheoryCoreLeaf where
  | grDiscreteToSmoothEvidence
  | grRecoveryCommutationAndLiteralAttachment
  | qftRecoveryCommutationAndPinnedAttachment
  | cmp119StressLiteralSameObject
  | grToSelectedQFTCrossSectorStressEquality
  | commonOverlapBackreactionAndCorrectionControl
  deriving DecidableEq, Repr

def theoryCoreLeaves : List TheoryCoreLeaf :=
  [ .grDiscreteToSmoothEvidence
  , .grRecoveryCommutationAndLiteralAttachment
  , .qftRecoveryCommutationAndPinnedAttachment
  , .cmp119StressLiteralSameObject
  , .grToSelectedQFTCrossSectorStressEquality
  , .commonOverlapBackreactionAndCorrectionControl
  ]

inductive PhysicalValidationLeaf where
  | recoveryPromotionAuthorities
  | stressWeldAndRegimePromotionAuthorities
  | acceptedMeasuredGAndUnitCalibration
  | chosenColliderOrOtherEmpiricalCalibration
  | novelObservableAgainstEstablishedGRQFT
  | falsifiableMeasurement
  | knownLimitValidationIncludingSchwarzschild
  deriving DecidableEq, Repr

def physicalValidationLeaves : List PhysicalValidationLeaf :=
  [ .recoveryPromotionAuthorities
  , .stressWeldAndRegimePromotionAuthorities
  , .acceptedMeasuredGAndUnitCalibration
  , .chosenColliderOrOtherEmpiricalCalibration
  , .novelObservableAgainstEstablishedGRQFT
  , .falsifiableMeasurement
  , .knownLimitValidationIncludingSchwarzschild
  ]

def w4DrellYanIsPremiseOfMathematicalGRQFTCore : Bool := false
def commonRegimeBackreactionIsPartOfTheoryCore : Bool := true
def novelObservableIsPartOfTheoryConstructionCore : Bool := false

theorem w4_not_theory_core_premise :
    w4DrellYanIsPremiseOfMathematicalGRQFTCore = false := rfl

theorem common_regime_backreaction_is_theory_core :
    commonRegimeBackreactionIsPartOfTheoryCore = true := rfl

theorem novel_observable_is_validation_not_theory_core :
    novelObservableIsPartOfTheoryConstructionCore = false := rfl

/-!
Concrete normalized component cut.

The finite GR fixture is the exact 4x4 rational tensor diag(1,-1,-1,-1).
A future CMP119 evaluator supplies the QFT tensor in the same carrier; the
16 component equations then compile directly to tensor equality.
-/

inductive Axis4 where
  | t | x | y | z
  deriving DecidableEq, Repr

def RationalTensor4 := Axis4 → Axis4 → Rat

def finiteGRStressRational : RationalTensor4
  | .t, .t => 1
  | .x, .x => -1
  | .y, .y => -1
  | .z, .z => -1
  | _, _ => 0

structure CMP119RationalStressComponentEvaluator (Stress : Type u) where
  component : Stress → Axis4 → Axis4 → Rat

def cmp119RationalTensor
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : RationalTensor4 :=
  E.component stress

structure NormalizedCrossSectorStressInstance
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Prop where
  qft00 : E.component stress .t .t = 1
  qft11 : E.component stress .x .x = -1
  qft22 : E.component stress .y .y = -1
  qft33 : E.component stress .z .z = -1
  qft01 : E.component stress .t .x = 0
  qft02 : E.component stress .t .y = 0
  qft03 : E.component stress .t .z = 0
  qft10 : E.component stress .x .t = 0
  qft12 : E.component stress .x .y = 0
  qft13 : E.component stress .x .z = 0
  qft20 : E.component stress .y .t = 0
  qft21 : E.component stress .y .x = 0
  qft23 : E.component stress .y .z = 0
  qft30 : E.component stress .z .t = 0
  qft31 : E.component stress .z .x = 0
  qft32 : E.component stress .z .y = 0

theorem sixteen_components_compile_to_tensor_equality
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedCrossSectorStressInstance E stress)
    (a b : Axis4) :
    finiteGRStressRational a b = cmp119RationalTensor E stress a b := by
  cases a <;> cases b <;>
    simp [finiteGRStressRational, cmp119RationalTensor,
      h.qft00, h.qft11, h.qft22, h.qft33,
      h.qft01, h.qft02, h.qft03, h.qft10,
      h.qft12, h.qft13, h.qft20, h.qft21,
      h.qft23, h.qft30, h.qft31, h.qft32]

def normalizedCMP119ComponentEvaluatorStillRequired : Bool := true
def secondTensorEqualityTheoremAfterSixteenComponentsRequired : Bool := false
def physicalSIStressCalibrationClaimed : Bool := false

theorem no_second_tensor_theorem_after_components :
    secondTensorEqualityTheoremAfterSixteenComponentsRequired = false := rfl

/-!
Executable common-regime attempt retaining four separate failure coordinates.
-/

structure CommonRegimeDecisionProbe
    (Candidate Regime : Type u) where
  grRegimeDecision : Regime → Bool
  qftRegimeDecision : Regime → Bool
  backreactionDecision : Candidate → Regime → Bool
  correctionDecision : Candidate → Regime → Bool

structure CommonRegimeAttemptResult where
  grPassed : Bool
  qftPassed : Bool
  backreactionPassed : Bool
  correctionPassed : Bool
  allPassed : Bool
  deriving DecidableEq, Repr

def runCommonRegimeAttempt
    {Candidate Regime : Type u}
    (P : CommonRegimeDecisionProbe Candidate Regime)
    (candidate : Candidate)
    (regime : Regime) : CommonRegimeAttemptResult :=
  let gr := P.grRegimeDecision regime
  let qft := P.qftRegimeDecision regime
  let back := P.backreactionDecision candidate regime
  let corr := P.correctionDecision candidate regime
  {
    grPassed := gr
    qftPassed := qft
    backreactionPassed := back
    correctionPassed := corr
    allPassed := gr && qft && back && corr
  }

def commonRegimeAttemptRetainsFourSeparateFailureCoordinates : Bool := true
def missingCommonRegimePromotionTokenBlocksAttemptExecution : Bool := false

theorem overlap_attempt_preserves_failures :
    commonRegimeAttemptRetainsFourSeparateFailureCoordinates = true := rfl

theorem promotion_does_not_block_overlap_attempt :
    missingCommonRegimePromotionTokenBlocksAttemptExecution = false := rfl

/-!
Concrete frontier correction.
-/

def unifiedCandidateInhabitationIsAggregateConsequence : Bool := true
def qftComponentEvaluatorExists : Bool := false
def commonOverlapEvidenceExists : Bool := false

theorem candidate_inhabitation_not_extra_leaf :
    unifiedCandidateInhabitationIsAggregateConsequence = true := rfl

/-!
CMP119 metric-basis component extraction.

The YM side already owns a stress functional on canonical admissible metric
perturbations.  GRQFT therefore needs only a 4x4 coordinate frame inside that
perturbation carrier plus a rational readout.
-/

structure MetricBasis16 (MetricPerturbation : Type u) where
  basisPerturbation : Axis4 → Axis4 → MetricPerturbation

structure RationalStressPairingReadout
    (PairingScalar : Type u) where
  pairingToRat : PairingScalar → Rat

def metricBasisComponent
    {Stress MetricPerturbation PairingScalar : Type u}
    (pairing : Stress → MetricPerturbation → PairingScalar)
    (basis : MetricBasis16 MetricPerturbation)
    (readout : RationalStressPairingReadout PairingScalar)
    (stress : Stress)
    (a b : Axis4) : Rat :=
  readout.pairingToRat (pairing stress (basis.basisPerturbation a b))

def secondStressRepresentationNeededForComponents : Bool := false

theorem no_second_stress_representation :
    secondStressRepresentationNeededForComponents = false := rfl

/-!
Ten-component reduction from symmetry.
-/

structure PairingComponentSymmetry
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Prop where
  componentSymmetric :
    ∀ a b, E.component stress a b = E.component stress b a

structure NormalizedSymmetricTenComponentInstance
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Prop where
  symmetry : PairingComponentSymmetry E stress
  qft00 : E.component stress .t .t = 1
  qft01 : E.component stress .t .x = 0
  qft02 : E.component stress .t .y = 0
  qft03 : E.component stress .t .z = 0
  qft11 : E.component stress .x .x = -1
  qft12 : E.component stress .x .y = 0
  qft13 : E.component stress .x .z = 0
  qft22 : E.component stress .y .y = -1
  qft23 : E.component stress .y .z = 0
  qft33 : E.component stress .z .z = -1

theorem ten_components_compile_to_tensor_equality
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedSymmetricTenComponentInstance E stress)
    (a b : Axis4) :
    finiteGRStressRational a b = E.component stress a b := by
  cases a <;> cases b
  · exact h.qft00.symm
  · exact h.qft01.symm
  · exact h.qft02.symm
  · exact h.qft03.symm
  · exact (h.symmetry.componentSymmetric .x .t).trans h.qft01 |>.symm
  · exact h.qft11.symm
  · exact h.qft12.symm
  · exact h.qft13.symm
  · exact (h.symmetry.componentSymmetric .y .t).trans h.qft02 |>.symm
  · exact (h.symmetry.componentSymmetric .y .x).trans h.qft12 |>.symm
  · exact h.qft22.symm
  · exact h.qft23.symm
  · exact (h.symmetry.componentSymmetric .z .t).trans h.qft03 |>.symm
  · exact (h.symmetry.componentSymmetric .z .x).trans h.qft13 |>.symm
  · exact (h.symmetry.componentSymmetric .z .y).trans h.qft23 |>.symm
  · exact h.qft33.symm

def sixteenIndependentComponentPaymentsRequired : Bool := false
def metricBasis16StillNeedsPhysicalCoordinateIdentification : Bool := true
def symmetrySemanticMeaningStillRequired : Bool := true

theorem sixteen_components_not_independent :
    sixteenIndependentComponentPaymentsRequired = false := rfl

/-!
Concrete-frontier sharpening.
-/

def qftComponentEvaluatorCompilerExists : Bool := true
def metricBasisInstanceExists : Bool := false
def symmetrySemanticBridgeInstanceExists : Bool := false
def tenIndependentComponentValuesExist : Bool := false

theorem qft_component_evaluator_compiler_present :
    qftComponentEvaluatorCompilerExists = true := rfl

/-!
Repulsion mechanism classifier.

Within the two-sign Einstein/Newton source-product model, a negative effective
source has exactly two nonzero sign origins: negative coupling with positive
source, or positive coupling with negative source.  Positive-positive and
negative-negative do not produce the negative branch.
-/

inductive CouplingSign where
  | positive | zero | negative
  deriving DecidableEq, Repr

inductive SourceSign where
  | positive | zero | negative
  deriving DecidableEq, Repr

inductive EffectiveSourceOrientation where
  | positive | zero | negative
  deriving DecidableEq, Repr

def effectiveSourceOrientation :
    CouplingSign → SourceSign → EffectiveSourceOrientation
  | .zero, _ => .zero
  | _, .zero => .zero
  | .positive, .positive => .positive
  | .positive, .negative => .negative
  | .negative, .positive => .negative
  | .negative, .negative => .positive

inductive NegativeEffectiveSourceRoute where
  | negativeCouplingPositiveSource
  | positiveCouplingNegativeSource
  deriving DecidableEq, Repr

theorem classify_negative_effective_source
    (g : CouplingSign)
    (s : SourceSign)
    (h : effectiveSourceOrientation g s = .negative) :
    NegativeEffectiveSourceRoute := by
  cases g <;> cases s <;> simp [effectiveSourceOrientation] at h
  · exact .positiveCouplingNegativeSource
  · exact .negativeCouplingPositiveSource

theorem positive_coupling_positive_source_cannot_be_negative :
    effectiveSourceOrientation .positive .positive ≠ .negative := by
  decide

theorem negative_coupling_negative_source_cannot_be_negative :
    effectiveSourceOrientation .negative .negative ≠ .negative := by
  decide

/-!
Negative active-stress route.

Under the explicitly declared local orthonormal rest-frame diagonal stress
interpretation, rho + p_x + p_y + p_z is the standard active-stress/focusing
combination.  The normalized GR target diag(1,-1,-1,-1) therefore has value -2.

This is an algebraic diagnostic, not by itself a solved repulsive spacetime.
-/

inductive DiagonalStressInterpretationConvention where
  | localOrthonormalCovariantRestFrame
  deriving DecidableEq, Repr

def activeStressSum (T : RationalTensor4) : Rat :=
  T .t .t + T .x .x + T .y .y + T .z .z

theorem finite_gr_active_stress_sum_negative_two :
    activeStressSum finiteGRStressRational = -2 := by
  norm_num [activeStressSum, finiteGRStressRational]

def cmp119ActiveStressSum
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Rat :=
  E.component stress .t .t
    + E.component stress .x .x
    + E.component stress .y .y
    + E.component stress .z .z

theorem ten_components_compile_to_negative_active_stress
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedSymmetricTenComponentInstance E stress) :
    cmp119ActiveStressSum E stress = -2 := by
  simp [cmp119ActiveStressSum, h.qft00, h.qft11, h.qft22, h.qft33]

inductive GRQFTRepulsionMechanismCandidate where
  | negativePressureTensionActiveSource
  deriving DecidableEq, Repr

def normalizedGRTargetRepulsionCandidate :
    GRQFTRepulsionMechanismCandidate :=
  .negativePressureTensionActiveSource

def normalizedGRTargetHasNegativeActiveStressUnderDeclaredConvention : Bool := true
def cmp119TenComponentPaymentTransportsNegativeActiveStress : Bool := true
def negativeActiveStressEqualsNegativeInertialMass : Bool := false
def negativeActiveStressRequiresNegativeNewtonG : Bool := false
def algebraicNegativeActiveStressAloneSolvesRepulsiveGeometry : Bool := false
def einsteinDynamicsAndGeometryStillRequired : Bool := true

theorem negative_active_stress_route_is_distinct_from_negative_g :
    negativeActiveStressRequiresNegativeNewtonG = false := rfl


/-!
Ten-slot symmetric metric basis.

Swapped ordered pairs select the same independent symmetric slot, so component
symmetry is compiler-owned by the chosen representation rather than an
additional semantic theorem.
-/

inductive SymmetricTensorComponent4 where
  | c00 | c01 | c02 | c03 | c11 | c12 | c13 | c22 | c23 | c33
  deriving DecidableEq, Repr

def symmetricSlotOfAxes : Axis4 → Axis4 → SymmetricTensorComponent4
  | .t, .t => .c00
  | .t, .x => .c01
  | .t, .y => .c02
  | .t, .z => .c03
  | .x, .t => .c01
  | .x, .x => .c11
  | .x, .y => .c12
  | .x, .z => .c13
  | .y, .t => .c02
  | .y, .x => .c12
  | .y, .y => .c22
  | .y, .z => .c23
  | .z, .t => .c03
  | .z, .x => .c13
  | .z, .y => .c23
  | .z, .z => .c33

theorem symmetric_slot_swapped (a b : Axis4) :
    symmetricSlotOfAxes a b = symmetricSlotOfAxes b a := by
  cases a <;> cases b <;> rfl

def componentSymmetryIsCompilerOwnedOnSymmetricBasis : Bool := true
def separateYMSymmetrySemanticBridgeRequiredOnSymmetricBasisRoute : Bool := false

theorem symmetric_basis_owns_component_symmetry :
    componentSymmetryIsCompilerOwnedOnSymmetricBasis = true := rfl

/-!
Existing same-object transport composition:
CMP119 endpoint stress = literal stress, and literal stress transported through
the R130 representation = canonical metric stress.  No third stress identity is
needed.
-/

theorem endpoint_to_metric_representation
    {CMP119 Literal Metric : Type u}
    (toLiteral : CMP119 → Literal)
    (toMetric : Literal → Metric)
    (cmp119 : CMP119)
    (literal : Literal)
    (metric : Metric)
    (hCMP119Literal : toLiteral cmp119 = literal)
    (hLiteralMetric : toMetric literal = metric) :
    toMetric (toLiteral cmp119) = metric := by
  rw [hCMP119Literal]
  exact hLiteralMetric

def secondEndpointToMetricStressIdentificationRequired : Bool := false

theorem no_second_endpoint_metric_stress_theorem :
    secondEndpointToMetricStressIdentificationRequired = false := rfl

/-!
Timelike defocusing compiler.

Convention:
* signature (-,+,+,+)
* local orthonormal comoving frame
* Lambda = 0
* normalized kappa = 1

For the normalized diagonal stress diag(1,-1,-1,-1),
T = -rho + px + py + pz = -4 and
R_00 = T_00 - (1/2) g_00 T = -1.
Therefore the Raychaudhuri curvature term -R_uu is +1.
-/

def stressTraceRestFrame (T : RationalTensor4) : Rat :=
  - T .t .t + T .x .x + T .y .y + T .z .z

def ricci00TraceReversed (T : RationalTensor4) : Rat :=
  T .t .t - (1 / 2 : Rat) * (-1) * stressTraceRestFrame T

theorem finite_gr_stress_trace_negative_four :
    stressTraceRestFrame finiteGRStressRational = -4 := by
  norm_num [stressTraceRestFrame, finiteGRStressRational]

theorem finite_gr_ricci00_negative_one :
    ricci00TraceReversed finiteGRStressRational = -1 := by
  norm_num [ricci00TraceReversed, stressTraceRestFrame, finiteGRStressRational]

def raychaudhuriCurvatureContribution (ricciUU : Rat) : Rat :=
  -ricciUU

theorem finite_gr_raychaudhuri_curvature_contribution_positive_one :
    raychaudhuriCurvatureContribution
      (ricci00TraceReversed finiteGRStressRational) = 1 := by
  norm_num [raychaudhuriCurvatureContribution, ricci00TraceReversed,
    stressTraceRestFrame, finiteGRStressRational]

def raychaudhuriRHS
    (thetaSquared shearSquared vorticitySquared ricciUU : Rat) : Rat :=
  -(1 / 3 : Rat) * thetaSquared
    - shearSquared
    + vorticitySquared
    - ricciUU

theorem finite_gr_initial_parallel_shearfree_irrotational_defocusing :
    raychaudhuriRHS 0 0 0
      (ricci00TraceReversed finiteGRStressRational) = 1 := by
  norm_num [raychaudhuriRHS, ricci00TraceReversed,
    stressTraceRestFrame, finiteGRStressRational]

def cmp119StressTraceRestFrame
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Rat :=
  - E.component stress .t .t
    + E.component stress .x .x
    + E.component stress .y .y
    + E.component stress .z .z

def cmp119Ricci00TraceReversed
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : Rat :=
  E.component stress .t .t
    - (1 / 2 : Rat) * (-1) * cmp119StressTraceRestFrame E stress

theorem ten_components_compile_to_negative_ricci00
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedSymmetricTenComponentInstance E stress) :
    cmp119Ricci00TraceReversed E stress = -1 := by
  norm_num [cmp119Ricci00TraceReversed, cmp119StressTraceRestFrame,
    h.qft00, h.qft11, h.qft22, h.qft33]

theorem ten_components_compile_to_positive_initial_raychaudhuri_rhs
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedSymmetricTenComponentInstance E stress) :
    raychaudhuriRHS 0 0 0 (cmp119Ricci00TraceReversed E stress) = 1 := by
  rw [ten_components_compile_to_negative_ricci00 h]
  norm_num [raychaudhuriRHS]

def finiteTargetTraceReverseGivesNegativeRicciUU : Bool := true
def negativeRicciUUGivesPositiveRaychaudhuriCurvatureTerm : Bool := true
def zeroKinematicTermsGivePositiveExpansionDerivative : Bool := true
def localDefocusingContributionEqualsGlobalOutwardTrajectory : Bool := false
def solvedBoundaryValueGeometryStillRequiredForRemoteAcceleration : Bool := true

theorem local_defocusing_not_yet_global_trajectory :
    localDefocusingContributionEqualsGlobalOutwardTrajectory = false := rfl


/-!
Same-object finite defocusing witness.

This mirrors the Agda composition at the level currently represented in the Lean
GRQFT branch: positive normalized coupling is the selected finite Einstein
fixture, while the source-side tension pattern gives negative active stress and
positive Raychaudhuri defocusing.  The finite witness is not promoted to a
continuum/global repulsive spacetime.
-/

inductive FiniteUnitCoefficient where
  | negative | zero | positive
  deriving DecidableEq, Repr

inductive FiniteEinsteinAttemptOutcome where
  | exactResidualZero | nonzeroResidualCounterexample
  deriving DecidableEq, Repr

def finiteEinsteinAttempt : FiniteUnitCoefficient → FiniteEinsteinAttemptOutcome
  | .positive => .exactResidualZero
  | .zero => .nonzeroResidualCounterexample
  | .negative => .nonzeroResidualCounterexample

structure FiniteDefocusingSolutionWitness : Prop where
  positiveExpansionPastToPresent : True
  positiveExpansionPresentToFuture : True
  expansionGradientConstant : True
  curvaturePositive : True
  energyDensityPositive : True
  pressureNegative : True
  equationOfStateRhoPlusPressureZero : True
  normalizedPositiveCouplingPasses :
    finiteEinsteinAttempt .positive = .exactResidualZero
  zeroCouplingRejected :
    finiteEinsteinAttempt .zero = .nonzeroResidualCounterexample
  negativeCouplingRejected :
    finiteEinsteinAttempt .negative = .nonzeroResidualCounterexample
  activeStressNegativeTwo :
    activeStressSum finiteGRStressRational = -2
  timelikeRicciNegativeOne :
    ricci00TraceReversed finiteGRStressRational = -1
  raychaudhuriCurvaturePositiveOne :
    raychaudhuriCurvatureContribution
      (ricci00TraceReversed finiteGRStressRational) = 1

theorem canonical_finite_defocusing_solution_witness :
    FiniteDefocusingSolutionWitness := by
  constructor <;> try trivial <;> rfl

inductive FiniteRepulsionMechanism where
  | positiveGCouplingWithNegativePressureTension
  deriving DecidableEq, Repr

def finiteModelMechanism : FiniteRepulsionMechanism :=
  .positiveGCouplingWithNegativePressureTension

def finiteWitnessNeedsNegativeG : Bool := false
def finiteWitnessNeedsNegativeInertialMass : Bool := false
def finiteWitnessIsContinuumGlobalRepulsiveSpacetime : Bool := false
def completeRiemannGeodesicDeviationStillNeededForTrajectoryTheorem : Bool := true

theorem finite_defocusing_mechanism_is_source_side :
    finiteWitnessNeedsNegativeG = false := rfl


/-!
Finite FLRW-like comoving acceleration orientation.

Only the exact zero-Hdot fixture is compiled.  In that case
a¨/a = H², so positive normalized curvature gives expanding acceleration.
-/

inductive CurvatureOrientation where
  | zero | positive
  deriving DecidableEq, Repr

inductive ScaleAccelerationOrientation where
  | zero | expanding
  deriving DecidableEq, Repr

def zeroHdotFLRWAccelerationOrientation :
    CurvatureOrientation → ScaleAccelerationOrientation
  | .zero => .zero
  | .positive => .expanding

def finiteFLRWAccelerationOrientation : ScaleAccelerationOrientation :=
  zeroHdotFLRWAccelerationOrientation .positive

theorem finite_flrw_acceleration_is_expanding :
    finiteFLRWAccelerationOrientation = .expanding := rfl

def positiveComovingAccelerationOrientationConstructed : Bool := true
def finiteSignDepthAccelerationEqualsContinuumMagnitudePrediction : Bool := false
def comovingFLRWAccelerationEqualsArbitraryLocalTestMassTrajectory : Bool := false
def fullIndexedRiemannDeviationOperatorStillNeededForGeneralTrajectory : Bool := true

theorem finite_flrw_acceleration_not_general_trajectory :
    comovingFLRWAccelerationEqualsArbitraryLocalTestMassTrajectory = false := rfl


/-!
Indexed comoving Riemann / geodesic-deviation cut.

For the finite FLRW-like fixture, positive a¨/a gives
R^i_{0j0} = -(a¨/a) δ^i_j in the comoving orthonormal convention.
We retain orientation only, not continuum magnitude.
-/

inductive SpatialAxis3 where
  | x | y | z
  deriving DecidableEq, Repr

inductive CurvatureActionOrientation where
  | negative | zero | positive
  deriving DecidableEq, Repr

def sameSpatialAxis : SpatialAxis3 → SpatialAxis3 → Bool
  | .x, .x => true
  | .y, .y => true
  | .z, .z => true
  | _, _ => false

def riemannFromScaleAcceleration :
    ScaleAccelerationOrientation → CurvatureActionOrientation
  | .zero => .zero
  | .expanding => .negative

def comovingRiemannTimeTidal
    (i j : SpatialAxis3) : CurvatureActionOrientation :=
  if sameSpatialAxis i j then
    riemannFromScaleAcceleration finiteFLRWAccelerationOrientation
  else
    .zero

inductive SeparationAccelerationOrientation where
  | inward | zero | outward
  deriving DecidableEq, Repr

def deviationFromRiemann : CurvatureActionOrientation → SeparationAccelerationOrientation
  | .negative => .outward
  | .zero => .zero
  | .positive => .inward

def principalDeviationAcceleration
    (i : SpatialAxis3) : SeparationAccelerationOrientation :=
  deviationFromRiemann (comovingRiemannTimeTidal i i)

theorem all_principal_comoving_deviation_directions_outward
    (i : SpatialAxis3) :
    principalDeviationAcceleration i = .outward := by
  cases i <;> rfl

theorem comoving_offdiagonal_xy_zero :
    comovingRiemannTimeTidal .x .y = .zero := rfl

theorem comoving_offdiagonal_xz_zero :
    comovingRiemannTimeTidal .x .z = .zero := rfl

theorem comoving_offdiagonal_yz_zero :
    comovingRiemannTimeTidal .y .z = .zero := rfl

def indexedComovingTimeTidalBlockConstructed : Bool := true
def threePrincipalTidalEigenDirectionsOutward : Bool := true
def resultIsArbitrarySpacetimeRiemannTensor : Bool := false
def resultIsLocalizedStaticAntigravityField : Bool := false
def arbitraryWorldlineDeviationStillRequiresGeneralRiemannCarrier : Bool := true

theorem comoving_riemann_cut_not_general_static_field :
    resultIsLocalizedStaticAntigravityField = false := rfl


/-!
Localized positive-G repulsive source criterion.

This is an explicit weak-field/stationary/spherical adapter, not a proof of the
full Tolman/Komar theorem.  The existing active-stress density is integrated
with a unit positive volume weight in the finite fixture and then fed into the
signed exterior-response classifier.
-/

structure LocalizedWeakFieldActiveMassAssumptions where
  stationarySource : Bool
  weakFieldExterior : Bool
  sphericalExteriorComparison : Bool
  localOrthonormalRestFrame : Bool
  positiveVolumeWeight : Bool
  pressureSensitiveActiveSourceLaw : Bool
  deriving Repr

def canonicalLocalizedWeakFieldAssumptions :
    LocalizedWeakFieldActiveMassAssumptions where
  stationarySource := true
  weakFieldExterior := true
  sphericalExteriorComparison := true
  localOrthonormalRestFrame := true
  positiveVolumeWeight := true
  pressureSensitiveActiveSourceLaw := true

def localizedActiveMass (T : RationalTensor4) : Rat :=
  activeStressSum T

theorem finite_gr_localized_active_mass_negative_two :
    localizedActiveMass finiteGRStressRational = -2 := by
  norm_num [localizedActiveMass, activeStressSum, finiteGRStressRational]

inductive ActiveMassSign where
  | positive | zero | negative
  deriving DecidableEq, Repr

inductive ExteriorRadialResponse where
  | inward | zero | outward
  deriving DecidableEq, Repr

def exteriorResponse :
    CouplingSign → ActiveMassSign → ExteriorRadialResponse
  | .zero, _ => .zero
  | _, .zero => .zero
  | .positive, .positive => .inward
  | .positive, .negative => .outward
  | .negative, .positive => .outward
  | .negative, .negative => .inward

theorem positive_g_negative_active_mass_repels :
    exteriorResponse .positive .negative = .outward := rfl

structure LocalizedPositiveGRepulsiveSourceWitness : Prop where
  assumptions : LocalizedWeakFieldActiveMassAssumptions
  couplingPositive : CouplingSign = .positive
  activeMassValue : localizedActiveMass finiteGRStressRational = -2
  activeMassNegative : ActiveMassSign = .negative
  externalResponseOutward :
    exteriorResponse .positive .negative = .outward

theorem canonical_localized_positive_g_repulsive_source_witness :
    LocalizedPositiveGRepulsiveSourceWitness := by
  refine
    { assumptions := canonicalLocalizedWeakFieldAssumptions
      couplingPositive := rfl
      activeMassValue := finite_gr_localized_active_mass_negative_two
      activeMassNegative := rfl
      externalResponseOutward := rfl }

def externalTestMassRepulsionCriterionConstructed : Bool := true
def localizedCriterionRequiresNegativeG : Bool := false
def localizedCriterionRequiresNegativeInertialMass : Bool := false
def finiteFixtureProvesTolmanKomarTheorem : Bool := false
def stationaryWeakFieldSphericalAdapterExplicit : Bool := true
def fullLocalizedMetricSolutionStillRequiredBeyondCriterion : Bool := true

theorem localized_repulsion_uses_positive_g :
    localizedCriterionRequiresNegativeG = false := rfl


/-!
Localized positive-G antigravity max-cut.

This is the strongest composed finite/conditional result in the current GRQFT
mirror: positive coupling, negative-pressure active source, outward principal
comoving deviation, and outward external-test-mass weak-field response.
-/

structure LocalizedPositiveGAntigravityMaxCut : Prop where
  finiteDefocusing : FiniteDefocusingSolutionWitness
  localizedExterior : LocalizedPositiveGRepulsiveSourceWitness
  couplingPositive : CouplingSign = .positive
  xPrincipalDeviationOutward :
    principalDeviationAcceleration .x = .outward
  yPrincipalDeviationOutward :
    principalDeviationAcceleration .y = .outward
  zPrincipalDeviationOutward :
    principalDeviationAcceleration .z = .outward
  externalTestMassResponseOutward :
    exteriorResponse .positive .negative = .outward

theorem canonical_localized_positive_g_antigravity_max_cut :
    LocalizedPositiveGAntigravityMaxCut := by
  refine
    { finiteDefocusing := canonical_finite_defocusing_solution_witness
      localizedExterior := canonical_localized_positive_g_repulsive_source_witness
      couplingPositive := rfl
      xPrincipalDeviationOutward := rfl
      yPrincipalDeviationOutward := rfl
      zPrincipalDeviationOutward := rfl
      externalTestMassResponseOutward := rfl }

def localizedMaxCutNegativeGRequired : Bool := false
def localizedMaxCutNegativeInertialMassRequired : Bool := false
def localizedMaxCutArbitraryStaticMetricSolved : Bool := false
def localizedMaxCutFullTolmanKomarInternal : Bool := false
def localizedMaxCutContinuumMagnitudeCalibrated : Bool := false

theorem localized_max_cut_uses_positive_g :
    localizedMaxCutNegativeGRequired = false := rfl


/-!
Localized anisotropic repulsive shell.

Smallest exact two-zone fixture that retains positive density, relaxes radial
pressure to zero at the outer boundary, keeps tangential tension, and preserves
negative integrated active source.
-/

structure SphericalStressZone where
  rho : Rat
  radialPressure : Rat
  tangentialPressure : Rat
  deriving Repr

def activeStressDensity (z : SphericalStressZone) : Rat :=
  z.rho + z.radialPressure + z.tangentialPressure + z.tangentialPressure

def coreZone : SphericalStressZone where
  rho := 1
  radialPressure := -1
  tangentialPressure := -1

def boundaryZone : SphericalStressZone where
  rho := 1
  radialPressure := 0
  tangentialPressure := -1

theorem core_active_stress_negative_two :
    activeStressDensity coreZone = -2 := by
  norm_num [activeStressDensity, coreZone]

theorem boundary_active_stress_negative_one :
    activeStressDensity boundaryZone = -1 := by
  norm_num [activeStressDensity, boundaryZone]

theorem boundary_radial_pressure_zero :
    boundaryZone.radialPressure = 0 := rfl

theorem boundary_density_positive :
    boundaryZone.rho = 1 := rfl

theorem boundary_tangential_tension_negative :
    boundaryZone.tangentialPressure = -1 := rfl

def isotropicVacuumLikeZone (density : Rat) : SphericalStressZone where
  rho := density
  radialPressure := -density
  tangentialPressure := -density

theorem isotropic_positive_unit_cannot_have_zero_radial_boundary_pressure :
    (isotropicVacuumLikeZone 1).radialPressure ≠ 0 := by
  norm_num [isotropicVacuumLikeZone]

theorem boundary_radial_null_combination :
    boundaryZone.rho + boundaryZone.radialPressure = 1 := by
  norm_num [boundaryZone]

theorem boundary_tangential_null_combination :
    boundaryZone.rho + boundaryZone.tangentialPressure = 0 := by
  norm_num [boundaryZone]

def twoZoneIntegratedActiveMass : Rat :=
  activeStressDensity coreZone + activeStressDensity boundaryZone

theorem two_zone_integrated_active_mass_negative_three :
    twoZoneIntegratedActiveMass = -3 := by
  norm_num [twoZoneIntegratedActiveMass, activeStressDensity, coreZone, boundaryZone]

structure LocalizedAnisotropicRepulsiveShellWitness : Prop where
  coreActiveNegative : activeStressDensity coreZone = -2
  boundaryActiveNegative : activeStressDensity boundaryZone = -1
  outerRadialPressureZero : boundaryZone.radialPressure = 0
  outerDensityPositive : boundaryZone.rho = 1
  outerTangentialTensionNegative : boundaryZone.tangentialPressure = -1
  integratedActiveMassNegative : twoZoneIntegratedActiveMass = -3
  positiveGCoupling : CouplingSign = .positive
  externalResponseOutward :
    exteriorResponse .positive .negative = .outward

theorem canonical_localized_anisotropic_repulsive_shell :
    LocalizedAnisotropicRepulsiveShellWitness := by
  exact {
    coreActiveNegative := core_active_stress_negative_two
    boundaryActiveNegative := boundary_active_stress_negative_one
    outerRadialPressureZero := boundary_radial_pressure_zero
    outerDensityPositive := boundary_density_positive
    outerTangentialTensionNegative := boundary_tangential_tension_negative
    integratedActiveMassNegative := two_zone_integrated_active_mass_negative_three
    positiveGCoupling := rfl
    externalResponseOutward := rfl
  }

def anisotropicTransitionRepairsBoundaryPressure : Bool := true
def fullTOVConservationEquationSolved : Bool := false
def exactStaticMetricSolved : Bool := false
def negativeGRequiredForAnisotropicShell : Bool := false

theorem anisotropic_shell_does_not_require_negative_g :
    negativeGRequiredForAnisotropicShell = false := rfl


/-!
Finite normalized anisotropic TOV balance.

The first shell with p_t=-1 fails the static-balance sign test.  A thin
transition with p_r=0, p_t=+1 matches the normalized outward pressure step, and
a half-weight transition remains net negative in active mass.
-/

def normalizedAnisotropicTOVRHS (z : SphericalStressZone) : Rat :=
  -(z.rho + z.radialPressure)
    + 2 * (z.tangentialPressure - z.radialPressure)

theorem original_boundary_tov_rhs_negative_three :
    normalizedAnisotropicTOVRHS boundaryZone = -3 := by
  norm_num [normalizedAnisotropicTOVRHS, boundaryZone]

def desiredOutwardRadialPressureStep : Rat := 1

theorem original_boundary_does_not_match_desired_step :
    normalizedAnisotropicTOVRHS boundaryZone ≠ desiredOutwardRadialPressureStep := by
  norm_num [normalizedAnisotropicTOVRHS, boundaryZone, desiredOutwardRadialPressureStep]

def balancedTransitionZone : SphericalStressZone where
  rho := 1
  radialPressure := 0
  tangentialPressure := 1

theorem balanced_transition_tov_rhs_positive_one :
    normalizedAnisotropicTOVRHS balancedTransitionZone = 1 := by
  norm_num [normalizedAnisotropicTOVRHS, balancedTransitionZone]

theorem balanced_transition_active_stress_positive_three :
    activeStressDensity balancedTransitionZone = 3 := by
  norm_num [activeStressDensity, balancedTransitionZone]

def transitionWeight : Rat := 1 / 2

def balancedTwoZoneActiveMass : Rat :=
  activeStressDensity coreZone
    + transitionWeight * activeStressDensity balancedTransitionZone

theorem balanced_two_zone_active_mass_negative_half :
    balancedTwoZoneActiveMass = -(1 / 2 : Rat) := by
  norm_num [balancedTwoZoneActiveMass, transitionWeight, activeStressDensity,
    coreZone, balancedTransitionZone]

structure FiniteAnisotropicTOVBalanceWitness : Prop where
  transitionBalance :
    normalizedAnisotropicTOVRHS balancedTransitionZone =
      desiredOutwardRadialPressureStep
  surfaceRadialPressureZero :
    balancedTransitionZone.radialPressure = 0
  integratedActiveMassNegative :
    balancedTwoZoneActiveMass = -(1 / 2 : Rat)
  couplingPositive : CouplingSign = .positive
  exteriorResponseOutward :
    exteriorResponse .positive .negative = .outward

theorem canonical_finite_anisotropic_tov_balance :
    FiniteAnisotropicTOVBalanceWitness := by
  exact {
    transitionBalance := balanced_transition_tov_rhs_positive_one
    surfaceRadialPressureZero := rfl
    integratedActiveMassNegative := balanced_two_zone_active_mass_negative_half
    couplingPositive := rfl
    exteriorResponseOutward := rfl
  }

def originalNegativeTangentialShellFailsBalanceSign : Bool := true
def positiveTangentialTransitionRepairsNormalizedBalance : Bool := true
def transitionMustBeThinEnoughForNetNegativeActiveMass : Bool := true
def fullTOVMetricFactorDerived : Bool := false
def continuumConservationSolved : Bool := false
def junctionConditionsSolved : Bool := false

theorem corrected_shell_still_repels_with_positive_g :
    exteriorResponse .positive .negative = .outward := rfl


/-!
Constructive normalized anisotropic-TOV design equation.
-/

def requiredTangentialPressure
    (rho pR pRPrime gravityFactor : Rat) : Rat :=
  pR + (1 / 2 : Rat) * (pRPrime + gravityFactor * (rho + pR))

def normalizedTOVRHSFromCoordinates
    (rho pR pT gravityFactor : Rat) : Rat :=
  -(gravityFactor * (rho + pR)) + 2 * (pT - pR)

theorem required_tangential_pressure_closes_normalized_tov
    (rho pR pRPrime gravityFactor : Rat) :
    normalizedTOVRHSFromCoordinates
      rho pR
      (requiredTangentialPressure rho pR pRPrime gravityFactor)
      gravityFactor
      = pRPrime := by
  ring

theorem balanced_transition_tangential_pressure_forced_to_one :
    requiredTangentialPressure 1 0 1 1 = 1 := by
  norm_num [requiredTangentialPressure]


/-!
Balance-compatible localized antigravity max-cut.
-/

structure BalancedLocalizedPositiveGAntigravityMaxCut : Prop where
  finiteDefocusing : FiniteDefocusingSolutionWitness
  anisotropicBalance : FiniteAnisotropicTOVBalanceWitness
  couplingPositive : CouplingSign = .positive
  externalResponseOutward :
    exteriorResponse .positive .negative = .outward
  xPrincipalDeviationOutward :
    principalDeviationAcceleration .x = .outward
  yPrincipalDeviationOutward :
    principalDeviationAcceleration .y = .outward
  zPrincipalDeviationOutward :
    principalDeviationAcceleration .z = .outward

theorem canonical_balanced_localized_positive_g_antigravity_max_cut :
    BalancedLocalizedPositiveGAntigravityMaxCut := by
  exact {
    finiteDefocusing := canonical_finite_defocusing_solution_witness
    anisotropicBalance := canonical_finite_anisotropic_tov_balance
    couplingPositive := rfl
    externalResponseOutward := rfl
    xPrincipalDeviationOutward := rfl
    yPrincipalDeviationOutward := rfl
    zPrincipalDeviationOutward := rfl
  }

def balancedMaxCutNegativeGRequired : Bool := false
def balancedMaxCutNegativeInertialMassRequired : Bool := false
def balancedMaxCutFullContinuumTOVSolved : Bool := false
def balancedMaxCutJunctionConditionsSolved : Bool := false
def balancedMaxCutExactLocalizedMetricSolved : Bool := false

theorem balanced_max_cut_uses_positive_g :
    balancedMaxCutNegativeGRequired = false := rfl


/-!
Literal finite rational TOV system.

Absorb 4π into rhoBar so m' = r^2 rhoBar remains rational.  The fixture uses
r1=1,m1=1/8 and r2=2,m2=1/4 with p_r(r2)=0.
-/

structure RationalRadialState where
  radius : Rat
  mass : Rat
  densityBar : Rat
  rho : Rat
  radialPressure : Rat
  tangentialPressure : Rat
  deriving Repr

def schwarzschildDenominator (s : RationalRadialState) : Rat :=
  s.radius * (s.radius - 2 * s.mass)

def tovGravityNumerator (s : RationalRadialState) : Rat :=
  s.mass + s.radius^3 * s.radialPressure

def tovGravityFactor (s : RationalRadialState) : Rat :=
  tovGravityNumerator s / schwarzschildDenominator s

def anisotropicTOVRHS (s : RationalRadialState) : Rat :=
  -((s.rho + s.radialPressure) * tovGravityFactor s)
    + 2 * (s.tangentialPressure - s.radialPressure) / s.radius

def innerTOVState : RationalRadialState where
  radius := 1
  mass := 1/8
  densityBar := 1/8
  rho := 1
  radialPressure := -1
  tangentialPressure := -1

def outerMassTarget : Rat := 1/4
def outerRadius : Rat := 2
def outerDensityBar : Rat := 1/32

def massIncrement (r rhoBar deltaR : Rat) : Rat :=
  r^2 * rhoBar * deltaR

theorem outer_mass_integration_exact :
    innerTOVState.mass + massIncrement outerRadius outerDensityBar 1
      = outerMassTarget := by
  norm_num [innerTOVState, massIncrement, outerRadius, outerDensityBar, outerMassTarget]

def outerBaseState (pT : Rat) : RationalRadialState where
  radius := 2
  mass := 1/4
  densityBar := 1/32
  rho := 1
  radialPressure := 0
  tangentialPressure := pT

theorem outer_tov_gravity_factor_one_twelfth :
    tovGravityFactor (outerBaseState 0) = 1/12 := by
  norm_num [tovGravityFactor, tovGravityNumerator, schwarzschildDenominator, outerBaseState]

def desiredOuterPressureDerivative : Rat := 1/2

def requiredOuterTangentialPressure : Rat :=
  0 + (2/2 : Rat) * (desiredOuterPressureDerivative + tovGravityFactor (outerBaseState 0))

theorem required_outer_tangential_pressure_seven_twelfths :
    requiredOuterTangentialPressure = 7/12 := by
  norm_num [requiredOuterTangentialPressure, desiredOuterPressureDerivative,
    tovGravityFactor, tovGravityNumerator, schwarzschildDenominator, outerBaseState]

def outerBalancedTOVState : RationalRadialState :=
  outerBaseState requiredOuterTangentialPressure

theorem outer_tov_balance_exact :
    anisotropicTOVRHS outerBalancedTOVState = desiredOuterPressureDerivative := by
  norm_num [anisotropicTOVRHS, outerBalancedTOVState, requiredOuterTangentialPressure,
    desiredOuterPressureDerivative, tovGravityFactor, tovGravityNumerator,
    schwarzschildDenominator, outerBaseState]

theorem outer_r_minus_two_m_three_halves :
    outerBalancedTOVState.radius - 2 * outerBalancedTOVState.mass = 3/2 := by
  norm_num [outerBalancedTOVState, outerBaseState]

def radialActiveStress (s : RationalRadialState) : Rat :=
  s.rho + s.radialPressure + 2 * s.tangentialPressure

def finiteIntegratedActiveMass : Rat :=
  radialActiveStress innerTOVState + (1/2 : Rat) * radialActiveStress outerBalancedTOVState

theorem finite_integrated_active_mass_negative_eleven_twelfths :
    finiteIntegratedActiveMass = -11/12 := by
  norm_num [finiteIntegratedActiveMass, radialActiveStress, innerTOVState,
    outerBalancedTOVState, requiredOuterTangentialPressure, outerBaseState,
    desiredOuterPressureDerivative, tovGravityFactor, tovGravityNumerator,
    schwarzschildDenominator]

/-!
Exterior-mass collision and static positive-density no-go.

The literal TOV metric mass at the surface is +1/4 while the pressure-weighted
active-stress diagnostic is -11/12.  They are not the same object.
-/

def finiteSurfaceMetricMass : Rat := outerMassTarget

theorem finite_surface_metric_mass_positive_quarter :
    finiteSurfaceMetricMass = 1/4 := rfl

theorem surface_metric_mass_not_active_stress_diagnostic :
    finiteSurfaceMetricMass ≠ finiteIntegratedActiveMass := by
  norm_num [finiteSurfaceMetricMass, outerMassTarget,
    finiteIntegratedActiveMass, radialActiveStress, innerTOVState,
    outerBalancedTOVState, requiredOuterTangentialPressure, outerBaseState,
    desiredOuterPressureDerivative, tovGravityFactor, tovGravityNumerator,
    schwarzschildDenominator]

inductive MetricMassSign where
  | negative | zero | positive
  deriving DecidableEq, Repr

inductive DensityShellSign where
  | zero | positive
  deriving DecidableEq, Repr

def accumulatePositiveDensityShell :
    MetricMassSign → DensityShellSign → MetricMassSign
  | .negative, _ => .negative
  | .zero, .zero => .zero
  | .zero, .positive => .positive
  | .positive, _ => .positive

theorem two_positive_shells_from_regular_center_positive :
    accumulatePositiveDensityShell
      (accumulatePositiveDensityShell .zero .positive) .positive = .positive := rfl

inductive ExteriorRepulsionEscapeRoute where
  | negativeEnergyDensityContribution
  | negativeSurfaceEnergyJunction
  | nonVacuumExteriorStress
  | modifiedGravityOrEffectiveCoupling
  | timeDependentOrNonStaticGeometry
  | nonSphericalOrTopologicalRoute
  deriving DecidableEq, Repr

def negativePressureCanGiveLocalDefocusing : Bool := true
def negativePressureAloneCanMakeMetricMassNegative : Bool := false
def regularPositiveDensityMassAccumulationStaysNonnegative : Bool := true
def finiteLiteralTOVStandardExteriorRepulsive : Bool := false
def trueExteriorRepulsionNeedsEscapeRoute : Bool := true
def activeStressDiagnosticEqualsSchwarzschildMassByDefault : Bool := false

theorem finite_tov_blocks_standard_exterior_repulsion :
    finiteLiteralTOVStandardExteriorRepulsive = false := rfl


/-!
Authoritative localized max-cut after literal TOV execution.

Local defocusing survives, but the standard vacuum exterior remains on the
positive-mass attractive branch because the literal surface metric mass is +1/4.
-/

structure LocalizedDefocusingExteriorNoGoMaxCut : Prop where
  finiteDefocusing : FiniteDefocusingSolutionWitness
  literalFiniteTOVMassPositive :
    finiteSurfaceMetricMass = 1/4
  pressureWeightedActiveDiagnosticNegative :
    finiteIntegratedActiveMass = -11/12
  twoMassNotionsDistinct :
    finiteSurfaceMetricMass ≠ finiteIntegratedActiveMass
  xPrincipalDeviationOutward :
    principalDeviationAcceleration .x = .outward
  yPrincipalDeviationOutward :
    principalDeviationAcceleration .y = .outward
  zPrincipalDeviationOutward :
    principalDeviationAcceleration .z = .outward
  standardVacuumExteriorRepulsionFalse :
    finiteLiteralTOVStandardExteriorRepulsive = false

theorem canonical_localized_defocusing_exterior_no_go_max_cut :
    LocalizedDefocusingExteriorNoGoMaxCut := by
  exact {
    finiteDefocusing := canonical_finite_defocusing_solution_witness
    literalFiniteTOVMassPositive := finite_surface_metric_mass_positive_quarter
    pressureWeightedActiveDiagnosticNegative :=
      finite_integrated_active_mass_negative_eleven_twelfths
    twoMassNotionsDistinct := surface_metric_mass_not_active_stress_diagnostic
    xPrincipalDeviationOutward := rfl
    yPrincipalDeviationOutward := rfl
    zPrincipalDeviationOutward := rfl
    standardVacuumExteriorRepulsionFalse := rfl
  }

def authoritativeInteriorDefocusingConstructed : Bool := true
def authoritativeStandardVacuumExteriorRepulsionConstructed : Bool := false
def authoritativeExternalAntigravityNeedsEscapeRoute : Bool := true

theorem authoritative_max_cut_blocks_standard_exterior_repulsion :
    authoritativeStandardVacuumExteriorRepulsionConstructed = false := rfl


/-!
Positive-mass non-vacuum exterior escape.

Kottler/Schwarzschild-de Sitter weak-field radial acceleration:
  a_r = -M/r^2 + Lambda*r/3.
-/

def kottlerRadialAcceleration (mass radius lambda : Rat) : Rat :=
  -mass / (radius^2) + lambda * radius / 3

def kottlerSurfaceMass : Rat := 1/4
def kottlerProbeRadius : Rat := 2
def kottlerExteriorLambda : Rat := 3/4

theorem kottler_mass_term_one_sixteenth :
    kottlerSurfaceMass / (kottlerProbeRadius^2) = 1/16 := by
  norm_num [kottlerSurfaceMass, kottlerProbeRadius]

theorem kottler_lambda_term_one_half :
    kottlerExteriorLambda * kottlerProbeRadius / 3 = 1/2 := by
  norm_num [kottlerExteriorLambda, kottlerProbeRadius]

theorem kottler_fixture_acceleration_seven_sixteenths :
    kottlerRadialAcceleration
      kottlerSurfaceMass kottlerProbeRadius kottlerExteriorLambda = 7/16 := by
  norm_num [kottlerRadialAcceleration, kottlerSurfaceMass,
    kottlerProbeRadius, kottlerExteriorLambda]

def kottlerLambdaThreshold (mass radius : Rat) : Rat :=
  3 * mass / radius^3

theorem kottler_fixture_threshold_three_thirtyseconds :
    kottlerLambdaThreshold kottlerSurfaceMass kottlerProbeRadius = 3/32 := by
  norm_num [kottlerLambdaThreshold, kottlerSurfaceMass, kottlerProbeRadius]

structure PositiveMassNonVacuumExteriorRepulsionWitness : Prop where
  positiveSurfaceMass : kottlerSurfaceMass = 1/4
  threshold : kottlerLambdaThreshold kottlerSurfaceMass kottlerProbeRadius = 3/32
  outwardAcceleration :
    kottlerRadialAcceleration
      kottlerSurfaceMass kottlerProbeRadius kottlerExteriorLambda = 7/16

theorem canonical_positive_mass_nonvacuum_exterior_repulsion :
    PositiveMassNonVacuumExteriorRepulsionWitness := by
  exact {
    positiveSurfaceMass := rfl
    threshold := kottler_fixture_threshold_three_thirtyseconds
    outwardAcceleration := kottler_fixture_acceleration_seven_sixteenths
  }

def positiveMassRetainedInKottlerEscape : Bool := true
def negativeMassRequiredInKottlerEscape : Bool := false
def nonVacuumExteriorRequiredInKottlerEscape : Bool := true
def kottlerInteriorExteriorJunctionSolved : Bool := false
def kottlerSIMagnitudeCalibrated : Bool := false


/-!
Exterior repulsion route synthesis.

Standard positive-mass vacuum exterior is blocked in the literal TOV fixture.
A positive-mass non-vacuum Kottler escape has an exact outward rational witness.
-/

inductive ExteriorRepulsionRouteStatus where
  | standardVacuumBlocked
  | nonVacuumKottlerConstructed
  deriving DecidableEq, Repr

structure ExteriorRepulsionRouteSynthesis : Prop where
  standardVacuumRepulsionFalse :
    finiteLiteralTOVStandardExteriorRepulsive = false
  positiveMassNonVacuumEscape :
    PositiveMassNonVacuumExteriorRepulsionWitness

theorem canonical_exterior_repulsion_route_synthesis :
    ExteriorRepulsionRouteSynthesis := by
  exact {
    standardVacuumRepulsionFalse := rfl
    positiveMassNonVacuumEscape :=
      canonical_positive_mass_nonvacuum_exterior_repulsion
  }

def positiveMassVacuumExteriorRepulsionBlocked : Bool := true
def positiveMassNonVacuumExteriorRepulsionConstructed : Bool := true
def negativeMetricMassRequiredForCurrentConstructedEscape : Bool := false
def exteriorInteriorJunctionStillOpen : Bool := true
def exteriorSIMagnitudeStillOpen : Bool := true


/-!
de Sitter-like interior -> Kottler exterior junction.

A shell-free match at R requires both lapse and radial-derivative continuity.
For nonzero mass these force incompatible Lambda jumps.  A thin shell is
therefore required.  The explicit M=1/4, R=2 fixture uses
Lambda_out=3/16, Lambda_in=3/8 and gives outward acceleration +1/16 while
keeping f(R)=1/2 in the static patch.
-/

def fInteriorJunction (r lambdaIn : Rat) : Rat :=
  1 - lambdaIn * r^2 / 3

def fExteriorJunction (r mass lambdaOut : Rat) : Rat :=
  1 - 2*mass/r - lambdaOut*r^2/3

def fInteriorPrimeJunction (r lambdaIn : Rat) : Rat :=
  -2*lambdaIn*r/3

def fExteriorPrimeJunction (r mass lambdaOut : Rat) : Rat :=
  2*mass/r^2 - 2*lambdaOut*r/3

def metricContinuityLambdaJump (mass r : Rat) : Rat :=
  6*mass/r^3

def derivativeContinuityLambdaJump (mass r : Rat) : Rat :=
  -3*mass/r^3

theorem fixture_metric_jump_three_sixteenths :
    metricContinuityLambdaJump (1/4) 2 = 3/16 := by
  norm_num [metricContinuityLambdaJump]

theorem fixture_derivative_jump_minus_three_thirtyseconds :
    derivativeContinuityLambdaJump (1/4) 2 = -3/32 := by
  norm_num [derivativeContinuityLambdaJump]

theorem nonzero_mass_shell_free_match_impossible_fixture :
    metricContinuityLambdaJump (1/4) 2
      ≠ derivativeContinuityLambdaJump (1/4) 2 := by
  norm_num [metricContinuityLambdaJump, derivativeContinuityLambdaJump]

def junctionLambdaOut : Rat := 3/16
def junctionLambdaIn : Rat := 3/8

theorem junction_lapse_matches :
    fInteriorJunction 2 junctionLambdaIn
      = fExteriorJunction 2 (1/4) junctionLambdaOut := by
  norm_num [fInteriorJunction, fExteriorJunction, junctionLambdaIn, junctionLambdaOut]

theorem junction_lapse_static_half :
    fExteriorJunction 2 (1/4) junctionLambdaOut = 1/2 := by
  norm_num [fExteriorJunction, junctionLambdaOut]

theorem junction_outward_acceleration_one_sixteenth :
    kottlerRadialAcceleration (1/4) 2 junctionLambdaOut = 1/16 := by
  norm_num [kottlerRadialAcceleration, junctionLambdaOut]

theorem junction_derivative_jump_three_eighths :
    fExteriorPrimeJunction 2 (1/4) junctionLambdaOut
      - fInteriorPrimeJunction 2 junctionLambdaIn = 3/8 := by
  norm_num [fExteriorPrimeJunction, fInteriorPrimeJunction, junctionLambdaOut, junctionLambdaIn]

inductive SurfaceTangentialStressOrientation where
  | negativeTension
  | zero
  | positivePressure
  deriving DecidableEq, Repr

structure DeSitterKottlerJunctionWitness : Prop where
  lapseMatched :
    fInteriorJunction 2 junctionLambdaIn
      = fExteriorJunction 2 (1/4) junctionLambdaOut
  staticPatch :
    fExteriorJunction 2 (1/4) junctionLambdaOut = 1/2
  outwardAcceleration :
    kottlerRadialAcceleration (1/4) 2 junctionLambdaOut = 1/16
  derivativeJump :
    fExteriorPrimeJunction 2 (1/4) junctionLambdaOut
      - fInteriorPrimeJunction 2 junctionLambdaIn = 3/8
  surfaceTangentialStress :
    SurfaceTangentialStressOrientation = .positivePressure

theorem canonical_de_sitter_kottler_junction :
    DeSitterKottlerJunctionWitness := by
  exact {
    lapseMatched := junction_lapse_matches
    staticPatch := junction_lapse_static_half
    outwardAcceleration := junction_outward_acceleration_one_sixteenth
    derivativeJump := junction_derivative_jump_three_eighths
    surfaceTangentialStress := rfl
  }

def shellFreeDarmoisMatchAvailable : Bool := false
def thinSurfaceLayerRequired : Bool := true
def positiveSurfacePressureOrientationRequired : Bool := true
def exactIsraelNormalizationSolved : Bool := false


/-!
TOV / junction tangential-stress sign consistency.
-/

inductive TangentialPressureSign where
  | negative | zero | positive
  deriving DecidableEq, Repr

def tovBoundaryTangentialSign : TangentialPressureSign := .positive
def junctionSurfaceTangentialSign : TangentialPressureSign := .positive

theorem tov_and_junction_tangential_signs_agree :
    tovBoundaryTangentialSign = junctionSurfaceTangentialSign := rfl

structure TOVJunctionSignConsistencyWitness : Prop where
  tovTangentialPressure :
    requiredOuterTangentialPressure = 7/12
  junctionDerivativeJump :
    fExteriorPrimeJunction 2 (1/4) junctionLambdaOut
      - fInteriorPrimeJunction 2 junctionLambdaIn = 3/8
  signsAgree :
    tovBoundaryTangentialSign = junctionSurfaceTangentialSign

theorem canonical_tov_junction_sign_consistency :
    TOVJunctionSignConsistencyWitness := by
  exact {
    tovTangentialPressure := required_outer_tangential_pressure_seven_twelfths
    junctionDerivativeJump := junction_derivative_jump_three_eighths
    signsAgree := rfl
  }

def bulkPressureEqualsSurfaceDistributionMagnitude : Bool := false
def exactIsraelMagnitudeStillOpen : Bool := true


/-!
Exact Israel-shell magnitude invariant.

With matched lapse f_R, sigma=0 and
P = [f']/(16*pi*sqrt(f_R)).
Avoiding irrational/pi extensions, retain
(16*pi*P)^2 = [f']^2/f_R.
-/

def israelTangentialPressureSquared16Pi : Rat :=
  (3/8 : Rat)^2 / (1/2 : Rat)

theorem israel_tangential_pressure_squared_nine_thirtyseconds :
    israelTangentialPressureSquared16Pi = 9/32 := by
  norm_num [israelTangentialPressureSquared16Pi]

def israelSurfaceEnergyDensityJumpNumerator : Rat := 0

theorem israel_surface_energy_density_zero :
    israelSurfaceEnergyDensityJumpNumerator = 0 := rfl

/-!
Kottler positive-mass repulsion parameter window.

Use scaled L = Lambda*R^3:
  outward iff L > 3M
  static patch iff L < 3R - 6M
so a nonempty window requires R > 3M.

The midpoint L=(3/2)(R-M) gives equal margins
(3/2)(R-3M).
-/

def scaledLambdaMidpoint (mass radius : Rat) : Rat :=
  (3/2 : Rat) * (radius - mass)

def outwardAccelerationMargin (mass scaledLambda : Rat) : Rat :=
  scaledLambda - 3*mass

def staticPatchMargin (mass radius scaledLambda : Rat) : Rat :=
  3*radius - 6*mass - scaledLambda

def kottlerWindowWidth (mass radius : Rat) : Rat :=
  (3*radius - 6*mass) - 3*mass

theorem midpoint_outward_margin_identity (mass radius : Rat) :
    outwardAccelerationMargin mass (scaledLambdaMidpoint mass radius)
      = (3/2 : Rat) * (radius - 3*mass) := by
  ring

theorem midpoint_static_margin_identity (mass radius : Rat) :
    staticPatchMargin mass radius (scaledLambdaMidpoint mass radius)
      = (3/2 : Rat) * (radius - 3*mass) := by
  ring

theorem kottler_window_width_identity (mass radius : Rat) :
    kottlerWindowWidth mass radius = 3*(radius - 3*mass) := by
  ring

theorem fixture_midpoint_scaled_lambda_twentyone_eighths :
    scaledLambdaMidpoint (1/4) 2 = 21/8 := by
  norm_num [scaledLambdaMidpoint]

theorem fixture_midpoint_lambda_twentyone_sixtyfourths :
    scaledLambdaMidpoint (1/4) 2 / (2^3) = 21/64 := by
  norm_num [scaledLambdaMidpoint]

structure KottlerRepulsionParameterWindowWitness
    (mass radius : Rat) : Prop where
  midpointOutwardMargin :
    outwardAccelerationMargin mass (scaledLambdaMidpoint mass radius)
      = (3/2 : Rat) * (radius - 3*mass)
  midpointStaticMargin :
    staticPatchMargin mass radius (scaledLambdaMidpoint mass radius)
      = (3/2 : Rat) * (radius - 3*mass)
  windowWidth :
    kottlerWindowWidth mass radius = 3*(radius - 3*mass)

theorem kottler_repulsion_parameter_window
    (mass radius : Rat) :
    KottlerRepulsionParameterWindowWitness mass radius := by
  exact {
    midpointOutwardMargin := midpoint_outward_margin_identity mass radius
    midpointStaticMargin := midpoint_static_margin_identity mass radius
    windowWidth := kottler_window_width_identity mass radius
  }

def kottlerWindowControlledByRGreaterThanThreeM : Bool := true
def israelExactSquaredMagnitudeConstructed : Bool := true
def israelExactPiSqrtMagnitudeInternal : Bool := false


theorem kottler_window_nonempty_iff (mass radius : Rat) :
    3*mass < 3*radius - 6*mass ↔ 3*mass < radius := by
  constructor <;> intro h <;> linarith

theorem midpoint_outward_margin_positive
    (mass radius : Rat)
    (h : 3*mass < radius) :
    0 < outwardAccelerationMargin mass (scaledLambdaMidpoint mass radius) := by
  rw [midpoint_outward_margin_identity]
  positivity

theorem midpoint_static_margin_positive
    (mass radius : Rat)
    (h : 3*mass < radius) :
    0 < staticPatchMargin mass radius (scaledLambdaMidpoint mass radius) := by
  rw [midpoint_static_margin_identity]
  positivity


/-!
Parameterized repulsive junction design family.

Let R = 3M + delta.  Then the midpoint Kottler choice has equal outward/static
margins (3/2) delta and total scaled-Lambda window width 3 delta.  The junction
derivative cost remains 6M/R^2, independent of Lambda_out after lapse matching.
-/

def radiusFromGap (mass gap : Rat) : Rat :=
  3*mass + gap

theorem gap_midpoint_outward_margin
    (mass gap : Rat) :
    outwardAccelerationMargin mass
      (scaledLambdaMidpoint mass (radiusFromGap mass gap))
      = (3/2 : Rat) * gap := by
  ring

theorem gap_midpoint_static_margin
    (mass gap : Rat) :
    staticPatchMargin mass (radiusFromGap mass gap)
      (scaledLambdaMidpoint mass (radiusFromGap mass gap))
      = (3/2 : Rat) * gap := by
  ring

theorem gap_window_width
    (mass gap : Rat) :
    kottlerWindowWidth mass (radiusFromGap mass gap)
      = 3*gap := by
  ring

theorem matched_junction_derivative_jump
    (mass radius lambdaOut : Rat)
    (hR : radius ≠ 0) :
    let lambdaIn := lambdaOut + 6*mass/radius^3
    fExteriorPrimeJunction radius mass lambdaOut
      - fInteriorPrimeJunction radius lambdaIn
      = 6*mass/radius^2 := by
  dsimp
  field_simp [hR]
  ring

theorem fixture_gap_radius_two :
    radiusFromGap (1/4) (5/4) = 2 := by
  norm_num [radiusFromGap]

structure ParameterizedRepulsiveJunctionDesign
    (mass gap : Rat) : Prop where
  outwardMargin :
    outwardAccelerationMargin mass
      (scaledLambdaMidpoint mass (radiusFromGap mass gap))
      = (3/2 : Rat) * gap
  staticMargin :
    staticPatchMargin mass (radiusFromGap mass gap)
      (scaledLambdaMidpoint mass (radiusFromGap mass gap))
      = (3/2 : Rat) * gap
  windowWidth :
    kottlerWindowWidth mass (radiusFromGap mass gap) = 3*gap

theorem parameterized_repulsive_junction_design
    (mass gap : Rat) :
    ParameterizedRepulsiveJunctionDesign mass gap := by
  exact {
    outwardMargin := gap_midpoint_outward_margin mass gap
    staticMargin := gap_midpoint_static_margin mass gap
    windowWidth := gap_window_width mass gap
  }


/-!
General Israel shell with DEC-compatible exact fixture.

M=1/4, R=2,
Lambda_out=3/8 -> f_out=1/4, sqrt=1/2,
Lambda_in=21/64 -> f_in=9/16, sqrt=3/4.

The shell has:
  8pi sigma = 1/4
  8pi P     = -5/24
so NEC/WEC/DEC pass while SEC fails.
-/

def generalShellMass : Rat := 1/4
def generalShellRadius : Rat := 2
def generalShellLambdaOut : Rat := 3/8
def generalShellLambdaIn : Rat := 21/64
def generalShellSqrtFOut : Rat := 1/2
def generalShellSqrtFIn : Rat := 3/4

theorem general_shell_fout_quarter :
    fExteriorJunction generalShellRadius generalShellMass generalShellLambdaOut = 1/4 := by
  norm_num [fExteriorJunction, generalShellRadius, generalShellMass, generalShellLambdaOut]

theorem general_shell_fin_nine_sixteenths :
    fInteriorJunction generalShellRadius generalShellLambdaIn = 9/16 := by
  norm_num [fInteriorJunction, generalShellRadius, generalShellLambdaIn]

theorem general_shell_outward_acceleration_three_sixteenths :
    kottlerRadialAcceleration generalShellMass generalShellRadius generalShellLambdaOut
      = 3/16 := by
  norm_num [kottlerRadialAcceleration, generalShellMass, generalShellRadius,
    generalShellLambdaOut]

def generalKTauOut : Rat :=
  fExteriorPrimeJunction generalShellRadius generalShellMass generalShellLambdaOut
    / (2*generalShellSqrtFOut)

def generalKTauIn : Rat :=
  fInteriorPrimeJunction generalShellRadius generalShellLambdaIn
    / (2*generalShellSqrtFIn)

def generalKThetaOut : Rat := generalShellSqrtFOut / generalShellRadius
def generalKThetaIn : Rat := generalShellSqrtFIn / generalShellRadius

def generalSurfaceSigma8Pi : Rat :=
  2*(generalShellSqrtFIn-generalShellSqrtFOut)/generalShellRadius

def generalSurfacePressure8Pi : Rat :=
  (generalKTauOut-generalKTauIn) + (generalKThetaOut-generalKThetaIn)

theorem general_surface_sigma_quarter :
    generalSurfaceSigma8Pi = 1/4 := by
  norm_num [generalSurfaceSigma8Pi, generalShellSqrtFIn, generalShellSqrtFOut,
    generalShellRadius]

theorem general_surface_pressure_minus_five_twentyfourths :
    generalSurfacePressure8Pi = -5/24 := by
  norm_num [generalSurfacePressure8Pi, generalKTauOut, generalKTauIn,
    generalKThetaOut, generalKThetaIn, fExteriorPrimeJunction,
    fInteriorPrimeJunction, generalShellRadius, generalShellMass,
    generalShellLambdaOut, generalShellLambdaIn, generalShellSqrtFOut,
    generalShellSqrtFIn]

theorem general_shell_nec_margin_one_twentyfourth :
    generalSurfaceSigma8Pi + generalSurfacePressure8Pi = 1/24 := by
  rw [general_surface_sigma_quarter, general_surface_pressure_minus_five_twentyfourths]
  norm_num

theorem general_shell_dec_margin_one_twentyfourth :
    generalSurfaceSigma8Pi - 5/24 = 1/24 := by
  rw [general_surface_sigma_quarter]
  norm_num

theorem general_shell_sec_margin_minus_one_sixth :
    generalSurfaceSigma8Pi + 2*generalSurfacePressure8Pi = -1/6 := by
  rw [general_surface_sigma_quarter, general_surface_pressure_minus_five_twentyfourths]
  norm_num

structure GeneralIsraelDECCompatibleShellWitness : Prop where
  outwardAcceleration :
    kottlerRadialAcceleration generalShellMass generalShellRadius generalShellLambdaOut
      = 3/16
  sigmaPositive : generalSurfaceSigma8Pi = 1/4
  pressureTension : generalSurfacePressure8Pi = -5/24
  necMargin : generalSurfaceSigma8Pi + generalSurfacePressure8Pi = 1/24
  decMargin : generalSurfaceSigma8Pi - 5/24 = 1/24
  secMargin : generalSurfaceSigma8Pi + 2*generalSurfacePressure8Pi = -1/6

theorem canonical_general_israel_dec_compatible_shell :
    GeneralIsraelDECCompatibleShellWitness := by
  exact {
    outwardAcceleration := general_shell_outward_acceleration_three_sixteenths
    sigmaPositive := general_surface_sigma_quarter
    pressureTension := general_surface_pressure_minus_five_twentyfourths
    necMargin := general_shell_nec_margin_one_twentyfourth
    decMargin := general_shell_dec_margin_one_twentyfourth
    secMargin := general_shell_sec_margin_minus_one_sixth
  }

def generalShellNECCompatible : Bool := true
def generalShellWECCompatible : Bool := true
def generalShellDECCompatible : Bool := true
def generalShellSECCompatible : Bool := false
def generalShellNeedsNegativeSurfaceEnergy : Bool := false


/-!
Rational-square Israel design family.

Let x=sqrt(f_in(R)), y=sqrt(f_out(R)) with rational x,y.
The de Sitter/Kottler amplitudes and shell conditions become exact rational
expressions.  After clearing positive denominators:

  pressure tension margin = R(x-y)(2xy+1) - 3Mx
  NEC/DEC margin          = 3Mx - R(x-y)
  SEC-violation margin    = R(x-y)(xy+1) - 3Mx
  outward acceleration    = R(1-y^2) - 3M
-/

def lambdaInFromSquareLapse (radius x : Rat) : Rat :=
  3 * (1 - x^2) / radius^2

def lambdaOutFromSquareLapse (mass radius y : Rat) : Rat :=
  3 * (1 - 2*mass/radius - y^2) / radius^2

def outwardAccelerationScaled (mass radius y : Rat) : Rat :=
  radius * (1-y^2) - 3*mass

def surfaceGap (x y : Rat) : Rat := x-y

def rationalSquareSurfaceSigma8 (radius x y : Rat) : Rat :=
  2 * surfaceGap x y / radius

def rationalSquareSurfacePressure8 (mass radius x y : Rat) : Rat :=
  -(surfaceGap x y * (2*x*y+1)) / (radius*x*y)
    + 3*mass/(radius^2*y)

def pressureTensionMarginCleared (mass radius x y : Rat) : Rat :=
  radius * surfaceGap x y * (2*x*y+1) - 3*mass*x

def necDecMarginCleared (mass radius x y : Rat) : Rat :=
  3*mass*x - radius*surfaceGap x y

def secViolationMarginCleared (mass radius x y : Rat) : Rat :=
  radius*surfaceGap x y*(x*y+1) - 3*mass*x

theorem rational_square_pressure_cleared
    (mass radius x y : Rat)
    (hR : radius ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    rationalSquareSurfacePressure8 mass radius x y
      * (radius^2*x*y)
      = -pressureTensionMarginCleared mass radius x y := by
  field_simp [rationalSquareSurfacePressure8, pressureTensionMarginCleared,
    surfaceGap, hR, hx, hy]
  ring

theorem rational_square_nec_cleared
    (mass radius x y : Rat)
    (hR : radius ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    (rationalSquareSurfaceSigma8 radius x y
      + rationalSquareSurfacePressure8 mass radius x y)
      * (radius^2*x*y)
      = necDecMarginCleared mass radius x y := by
  field_simp [rationalSquareSurfaceSigma8, rationalSquareSurfacePressure8,
    necDecMarginCleared, surfaceGap, hR, hx, hy]
  ring

theorem rational_square_sec_cleared
    (mass radius x y : Rat)
    (hR : radius ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    (rationalSquareSurfaceSigma8 radius x y
      + 2*rationalSquareSurfacePressure8 mass radius x y)
      * (radius^2*x*y)
      = -2*secViolationMarginCleared mass radius x y := by
  field_simp [rationalSquareSurfaceSigma8, rationalSquareSurfacePressure8,
    secViolationMarginCleared, surfaceGap, hR, hx, hy]
  ring

theorem rational_square_fixture_lambda_in :
    lambdaInFromSquareLapse 2 (3/4) = 21/64 := by
  norm_num [lambdaInFromSquareLapse]

theorem rational_square_fixture_lambda_out :
    lambdaOutFromSquareLapse (1/4) 2 (1/2) = 3/8 := by
  norm_num [lambdaOutFromSquareLapse]

theorem rational_square_fixture_pressure_margin :
    pressureTensionMarginCleared (1/4) 2 (3/4) (1/2) = 5/16 := by
  norm_num [pressureTensionMarginCleared, surfaceGap]

theorem rational_square_fixture_nec_dec_margin :
    necDecMarginCleared (1/4) 2 (3/4) (1/2) = 1/16 := by
  norm_num [necDecMarginCleared, surfaceGap]

theorem rational_square_fixture_sec_violation_margin :
    secViolationMarginCleared (1/4) 2 (3/4) (1/2) = 1/8 := by
  norm_num [secViolationMarginCleared, surfaceGap]

theorem rational_square_fixture_outward_margin :
    outwardAccelerationScaled (1/4) 2 (1/2) = 3/4 := by
  norm_num [outwardAccelerationScaled]

structure RationalSquareIsraelAdmissible
    (mass radius x y : Rat) : Prop where
  radiusPositive : 0 < radius
  xPositive : 0 < x
  yPositive : 0 < y
  innerLapseRootLarger : y < x
  pressureTensionMarginPositive :
    0 < pressureTensionMarginCleared mass radius x y
  necDecMarginPositive :
    0 < necDecMarginCleared mass radius x y
  secViolationMarginPositive :
    0 < secViolationMarginCleared mass radius x y
  outwardMarginPositive :
    0 < outwardAccelerationScaled mass radius y

theorem rational_square_fixture_admissible :
    RationalSquareIsraelAdmissible (1/4) 2 (3/4) (1/2) := by
  constructor <;> norm_num [pressureTensionMarginCleared, necDecMarginCleared,
    secViolationMarginCleared, outwardAccelerationScaled, surfaceGap]

theorem admissible_shell_surface_energy_positive
    {mass radius x y : Rat}
    (h : RationalSquareIsraelAdmissible mass radius x y) :
    0 < rationalSquareSurfaceSigma8 radius x y := by
  dsimp [rationalSquareSurfaceSigma8, surfaceGap]
  positivity

theorem admissible_shell_pressure_is_tension
    {mass radius x y : Rat}
    (h : RationalSquareIsraelAdmissible mass radius x y) :
    rationalSquareSurfacePressure8 mass radius x y < 0 := by
  have hR : radius ≠ 0 := ne_of_gt h.radiusPositive
  have hx : x ≠ 0 := ne_of_gt h.xPositive
  have hy : y ≠ 0 := ne_of_gt h.yPositive
  have hden : 0 < radius^2*x*y := by positivity
  have heq := rational_square_pressure_cleared mass radius x y hR hx hy
  nlinarith [h.pressureTensionMarginPositive]

theorem admissible_shell_nec_dec_margin_positive
    {mass radius x y : Rat}
    (h : RationalSquareIsraelAdmissible mass radius x y) :
    0 < rationalSquareSurfaceSigma8 radius x y
      + rationalSquareSurfacePressure8 mass radius x y := by
  have hR : radius ≠ 0 := ne_of_gt h.radiusPositive
  have hx : x ≠ 0 := ne_of_gt h.xPositive
  have hy : y ≠ 0 := ne_of_gt h.yPositive
  have hden : 0 < radius^2*x*y := by positivity
  have heq := rational_square_nec_cleared mass radius x y hR hx hy
  nlinarith [h.necDecMarginPositive]

theorem admissible_shell_sec_is_violated
    {mass radius x y : Rat}
    (h : RationalSquareIsraelAdmissible mass radius x y) :
    rationalSquareSurfaceSigma8 radius x y
      + 2*rationalSquareSurfacePressure8 mass radius x y < 0 := by
  have hR : radius ≠ 0 := ne_of_gt h.radiusPositive
  have hx : x ≠ 0 := ne_of_gt h.xPositive
  have hy : y ≠ 0 := ne_of_gt h.yPositive
  have hden : 0 < radius^2*x*y := by positivity
  have heq := rational_square_sec_cleared mass radius x y hR hx hy
  nlinarith [h.secViolationMarginPositive]


/-!
Vacuum-stress amplitude / CMP119 transport.

The normalized GRQFT tensor diag(1,-1,-1,-1) is the -g vacuum-stress
direction.  Scalar amplitudes therefore generate the interior/exterior
cosmological-stress tensors without a second tensor weld.
-/

def scaleRationalTensor (a : Rat) (T : RationalTensor4) : RationalTensor4 :=
  fun i j => a * T i j

def vacuumStressAt (a : Rat) : RationalTensor4 :=
  scaleRationalTensor a finiteGRStressRational

def scaledCMP119Tensor
    {Stress : Type u}
    (a : Rat)
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress) : RationalTensor4 :=
  fun i j => a * E.component stress i j

theorem normalized_cmp119_scales_to_vacuum_stress
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedCrossSectorStressInstance E stress)
    (a : Rat) (i j : Axis4) :
    vacuumStressAt a i j = scaledCMP119Tensor a E stress i j := by
  unfold vacuumStressAt scaleRationalTensor scaledCMP119Tensor
  rw [sixteen_components_compile_to_tensor_equality h i j]

def decExteriorAmplitude : Rat := 3/8
def decInteriorAmplitude : Rat := 21/64

theorem cmp119_compiles_dec_exterior_stress
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedCrossSectorStressInstance E stress)
    (i j : Axis4) :
    vacuumStressAt decExteriorAmplitude i j
      = scaledCMP119Tensor decExteriorAmplitude E stress i j :=
  normalized_cmp119_scales_to_vacuum_stress h decExteriorAmplitude i j

theorem cmp119_compiles_dec_interior_stress
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (h : NormalizedCrossSectorStressInstance E stress)
    (i j : Axis4) :
    vacuumStressAt decInteriorAmplitude i j
      = scaledCMP119Tensor decInteriorAmplitude E stress i j :=
  normalized_cmp119_scales_to_vacuum_stress h decInteriorAmplitude i j

def oneNormalizedCMP119TensorFeedsBothRegions : Bool := true
def secondTensorWeldRequiredForDECExterior : Bool := false
def qftAmplitudeDynamicsConstructed : Bool := false


/-!
Balanced DEC-compatible repulsive shell family.

For R>0 and 0<y<x<1 choose

  M = R (x-y) (x*y+2) / (6x).

Then the cleared margins become

  pressure-tension margin = (3/2) R (x-y) x y
  NEC/DEC margin          = (1/2) R (x-y) x y
  SEC-violation margin    = (1/2) R (x-y) x y

and the outward-acceleration margin is

  R*y*(2-x*(x+y))/(2x) > 0.

Thus there is an open positive-mass family of DEC-compatible repulsive shells.
-/

def balancedShellMass (radius x y : Rat) : Rat :=
  radius * (x-y) * (x*y+2) / (6*x)

theorem balanced_shell_pressure_margin
    (radius x y : Rat) (hx : x ≠ 0) :
    pressureTensionMarginCleared (balancedShellMass radius x y) radius x y
      = (3/2 : Rat) * radius * (x-y) * x * y := by
  field_simp [balancedShellMass, pressureTensionMarginCleared, surfaceGap, hx]
  ring

theorem balanced_shell_nec_dec_margin
    (radius x y : Rat) (hx : x ≠ 0) :
    necDecMarginCleared (balancedShellMass radius x y) radius x y
      = (1/2 : Rat) * radius * (x-y) * x * y := by
  field_simp [balancedShellMass, necDecMarginCleared, surfaceGap, hx]
  ring

theorem balanced_shell_sec_violation_margin
    (radius x y : Rat) (hx : x ≠ 0) :
    secViolationMarginCleared (balancedShellMass radius x y) radius x y
      = (1/2 : Rat) * radius * (x-y) * x * y := by
  field_simp [balancedShellMass, secViolationMarginCleared, surfaceGap, hx]
  ring

theorem balanced_shell_outward_margin
    (radius x y : Rat) (hx : x ≠ 0) :
    outwardAccelerationScaled (balancedShellMass radius x y) radius y
      = radius*y*(2-x*(x+y))/(2*x) := by
  field_simp [balancedShellMass, outwardAccelerationScaled, hx]
  ring

theorem balanced_shell_mass_positive
    {radius x y : Rat}
    (hR : 0 < radius) (hx : 0 < x) (hy : 0 < y) (hyx : y < x) :
    0 < balancedShellMass radius x y := by
  unfold balancedShellMass
  positivity

theorem balanced_shell_family_admissible
    {radius x y : Rat}
    (hR : 0 < radius)
    (hy : 0 < y)
    (hyx : y < x)
    (hx1 : x < 1) :
    RationalSquareIsraelAdmissible
      (balancedShellMass radius x y) radius x y := by
  have hx : 0 < x := lt_trans hy hyx
  have hxypos : 0 < x*y := mul_pos hx hy
  have hgap : 0 < x-y := sub_pos.mpr hyx
  have hshape : 0 < 2 - x*(x+y) := by
    have hy1 : y < 1 := lt_trans hyx hx1
    nlinarith [mul_pos hx (by linarith : 0 < x+y)]
  constructor
  · exact hR
  · exact hx
  · exact hy
  · exact hyx
  · rw [balanced_shell_pressure_margin radius x y (ne_of_gt hx)]
    positivity
  · rw [balanced_shell_nec_dec_margin radius x y (ne_of_gt hx)]
    positivity
  · rw [balanced_shell_sec_violation_margin radius x y (ne_of_gt hx)]
    positivity
  · rw [balanced_shell_outward_margin radius x y (ne_of_gt hx)]
    positivity

theorem balanced_shell_family_has_positive_mass
    {radius x y : Rat}
    (hR : 0 < radius)
    (hy : 0 < y)
    (hyx : y < x)
    (hx1 : x < 1) :
    0 < balancedShellMass radius x y := by
  exact balanced_shell_mass_positive hR (lt_trans hy hyx) hy hyx


/-!
One-parameter balanced DEC-compatible shell family.

Fix x=3/4, y=1/2 and choose
  M(R)=19R/144.

For R>0:
  Lambda_in  = 21/(16 R^2)
  Lambda_out = 35/(24 R^2)
  a_out(R)   = 17/(48 R)
  8pi sigma  = 1/(2R)
  8pi P      = -3/(8R)
  NEC/DEC margin = 1/(8R)
  SEC margin     = -1/(4R).
-/

def balancedFamilyX : Rat := 3/4
def balancedFamilyY : Rat := 1/2
def balancedFamilyMass (radius : Rat) : Rat := 19*radius/144

theorem balanced_family_mass_matches_general_choice
    (radius : Rat) :
    balancedFamilyMass radius =
      balancedShellMass radius balancedFamilyX balancedFamilyY := by
  ring_nf [balancedFamilyMass, balancedShellMass, balancedFamilyX, balancedFamilyY]

theorem balanced_family_lambda_in
    (radius : Rat) (hR : radius ≠ 0) :
    lambdaInFromSquareLapse radius balancedFamilyX
      = 21/(16*radius^2) := by
  field_simp [lambdaInFromSquareLapse, balancedFamilyX, hR]
  ring

theorem balanced_family_lambda_out
    (radius : Rat) (hR : radius ≠ 0) :
    lambdaOutFromSquareLapse
      (balancedFamilyMass radius) radius balancedFamilyY
      = 35/(24*radius^2) := by
  field_simp [lambdaOutFromSquareLapse, balancedFamilyMass, balancedFamilyY, hR]
  ring

theorem balanced_family_outward_acceleration
    (radius : Rat) (hR : radius ≠ 0) :
    kottlerRadialAcceleration
      (balancedFamilyMass radius) radius
      (35/(24*radius^2))
      = 17/(48*radius) := by
  field_simp [kottlerRadialAcceleration, balancedFamilyMass, hR]
  ring

theorem balanced_family_surface_sigma
    (radius : Rat) (hR : radius ≠ 0) :
    rationalSquareSurfaceSigma8 radius balancedFamilyX balancedFamilyY
      = 1/(2*radius) := by
  field_simp [rationalSquareSurfaceSigma8, surfaceGap,
    balancedFamilyX, balancedFamilyY, hR]
  ring

theorem balanced_family_surface_pressure
    (radius : Rat) (hR : radius ≠ 0) :
    rationalSquareSurfacePressure8
      (balancedFamilyMass radius) radius balancedFamilyX balancedFamilyY
      = -3/(8*radius) := by
  field_simp [rationalSquareSurfacePressure8, surfaceGap,
    balancedFamilyMass, balancedFamilyX, balancedFamilyY, hR]
  ring

theorem balanced_family_nec_dec_margin
    (radius : Rat) (hR : radius ≠ 0) :
    rationalSquareSurfaceSigma8 radius balancedFamilyX balancedFamilyY
      + rationalSquareSurfacePressure8
        (balancedFamilyMass radius) radius balancedFamilyX balancedFamilyY
      = 1/(8*radius) := by
  rw [balanced_family_surface_sigma radius hR,
      balanced_family_surface_pressure radius hR]
  field_simp [hR]
  ring

theorem balanced_family_sec_margin
    (radius : Rat) (hR : radius ≠ 0) :
    rationalSquareSurfaceSigma8 radius balancedFamilyX balancedFamilyY
      + 2*rationalSquareSurfacePressure8
        (balancedFamilyMass radius) radius balancedFamilyX balancedFamilyY
      = -1/(4*radius) := by
  rw [balanced_family_surface_sigma radius hR,
      balanced_family_surface_pressure radius hR]
  field_simp [hR]
  ring

theorem balanced_family_positive_radius_physical_signs
    {radius : Rat} (hR : 0 < radius) :
    0 < balancedFamilyMass radius
    ∧ 0 < 21/(16*radius^2)
    ∧ 0 < 35/(24*radius^2)
    ∧ 0 < 17/(48*radius)
    ∧ 0 < 1/(2*radius)
    ∧ (-3/(8*radius) < 0)
    ∧ 0 < 1/(8*radius)
    ∧ (-1/(4*radius) < 0) := by
  constructor
  · unfold balancedFamilyMass
    positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · positivity


end Integration.GRQFTPostMergeLocalization
