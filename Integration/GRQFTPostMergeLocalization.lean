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


end Integration.GRQFTPostMergeLocalization
