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

end AgdaMirror.GRQFTPostMergeLocalization
