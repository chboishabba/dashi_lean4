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

end AgdaMirror.GRQFTPostMergeLocalization
