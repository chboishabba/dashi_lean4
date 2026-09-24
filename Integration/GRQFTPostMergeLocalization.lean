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
  | grDiscreteToContinuumRealization
  | cmp119StressToLiteralPinnedStressAttachment
  | pinnedLiteralYMToRecoveredQFTAttachment
  | allSectorQFTAggregationAndCommonVariation
  | einsteinCommonMetricVariation
  | commonMetricProducerLanguage
  | physicalDrellYanAbsoluteProjectionReplacement
  | acceptedMeasuredGAndEmpiricalAuthority
  | empiricalGRQFTDiscriminator
  deriving DecidableEq, Repr

def remainingPostMergeLeaves : List PostMergeLeaf :=
  [ .grDiscreteToContinuumRealization
  , .cmp119StressToLiteralPinnedStressAttachment
  , .pinnedLiteralYMToRecoveredQFTAttachment
  , .allSectorQFTAggregationAndCommonVariation
  , .einsteinCommonMetricVariation
  , .commonMetricProducerLanguage
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
  allSectorAggregationStillRequired : Bool
  terminalGRQFTPromoted : Bool
  remainingLeaves : List PostMergeLeaf
  deriving Repr

def postMergeMaxCut : PostMergeMaxCut where
  finiteEinsteinClosed := true
  finiteToPhysicalCalibrationCompilerClosed := true
  cmsBoundedRatioContactSurvivesW4Rejection := true
  cmp119ToSelectedSharedSectorCompilerClosed := true
  secondQFTStressTheoremRequired := false
  allSectorAggregationStillRequired := true
  terminalGRQFTPromoted := false
  remainingLeaves := remainingPostMergeLeaves

theorem postmerge_terminal_still_false :
    postMergeMaxCut.terminalGRQFTPromoted = false := rfl

end Integration.GRQFTPostMergeLocalization
