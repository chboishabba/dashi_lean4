import Integration.GRQFTPostMergeLocalization

namespace AgdaMirror.GRQFTPostMergeLocalization

open Integration.GRQFTPostMergeLocalization

def agdaRepository : String := "chboishabba/dashi_agda"

theorem cms_ratio_survives_w4_negative_parity :
    ratioAbsoluteLocalization.sharedCarrierGloballyRejected = false :=
  w4_does_not_globally_reject_shared_carrier

theorem projection_search_parity :
    ratioAbsoluteLocalization.projectionSpecificDefectSearchPreferred = true :=
  projection_specific_search_preferred

theorem cmp119_two_step_stress_transport_parity
    {α : Type u} {β : Type v}
    (toShared : α → β)
    {cmp119 literal selected : α}
    (h₁ : cmp119 = literal)
    (h₂ : literal = selected) :
    toShared cmp119 = toShared selected :=
  two_step_same_object_transport_through_shared toShared h₁ h₂

theorem second_cmp119_stress_theorem_parity :
    secondCMP119ToSharedStressTheoremRequired = false :=
  second_cmp119_to_shared_stress_theorem_not_required

theorem clay_group_quantifier_boundary_parity :
    clayUniversalGroupParameterMeansAllGroupsPhysicallyActive = false :=
  clay_group_quantifier_not_physical_sector_sum

theorem ratio_cancellation_boundary_parity :
    ratioAgreementImpliesAbsoluteAgreement = false :=
  ratio_agreement_does_not_imply_absolute_agreement

theorem low_chi_square_provenance_boundary_parity :
    lowChiSquareAlonePromotesEmpiricalAdequacy = false :=
  low_chi_square_alone_does_not_promote

theorem single_active_sector_source_factorisation_parity
    {Stress : Type u}
    {effective cmp119 selected total : Stress}
    (hEffectiveCMP : effective = cmp119)
    (hCMPSelected : cmp119 = selected)
    (hTotalSelected : total = selected) :
    effective = total :=
  single_active_sector_source_factorisation
    hEffectiveCMP hCMPSelected hTotalSelected

theorem gr_anchored_factorisation_boundary_parity :
    primitiveGRSourceFactorisationLeafRequired = false :=
  primitive_gr_source_factorisation_not_required

theorem cross_sector_stress_leaf_parity :
    crossSectorGRToCMP119StressEqualityRequired = true :=
  cross_sector_stress_equality_still_required

theorem schwarzschild_recovery_boundary_parity :
    schwarzschildRadialValuationRequiredForGenericAttachment = false :=
  schwarzschild_not_generic_recovery_premise

theorem single_sector_totalization_boundary_parity :
    singleSectorTotalEqualityIsPrimitiveTheorem = false :=
  single_sector_total_equality_not_primitive

theorem aggregation_packaging_boundary_parity :
    aggregationIsPremiseOfCrossSectorEquality = false :=
  aggregation_not_cross_sector_equality_premise

theorem promotion_packaging_boundary_parity :
    promotionTokenIsPremiseOfCrossSectorEquality = false :=
  promotion_not_cross_sector_equality_premise

theorem gr_request_vs_evidence_boundary_parity :
    requestSurfaceAloneClosesCurvatureConvergence = false :=
  request_surface_is_not_curvature_proof

theorem recovery_core_boundary_parity :
    fullRecoveryReceiptRequiredForSameObjectEquality = false :=
  full_recovery_receipt_not_same_object_premise

theorem regime_core_boundary_parity :
    regimePromotionTokenIsMathematicalOverlapPremise = false :=
  regime_token_not_overlap_math

theorem w4_validation_split_parity :
    w4DrellYanIsPremiseOfMathematicalGRQFTCore = false :=
  w4_not_theory_core_premise

theorem common_regime_theory_core_parity :
    commonRegimeBackreactionIsPartOfTheoryCore = true :=
  common_regime_backreaction_is_theory_core

theorem component_cut_parity :
    secondTensorEqualityTheoremAfterSixteenComponentsRequired = false :=
  no_second_tensor_theorem_after_components

theorem overlap_failure_coordinate_parity :
    commonRegimeAttemptRetainsFourSeparateFailureCoordinates = true :=
  overlap_attempt_preserves_failures

theorem overlap_promotion_boundary_parity :
    missingCommonRegimePromotionTokenBlocksAttemptExecution = false :=
  promotion_does_not_block_overlap_attempt

theorem candidate_aggregate_construction_parity :
    unifiedCandidateInhabitationIsAggregateConsequence = true :=
  candidate_inhabitation_not_extra_leaf

end AgdaMirror.GRQFTPostMergeLocalization
