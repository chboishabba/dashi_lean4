import Integration.F4MinusculeOnePlus26

namespace Integration.F4MinusculeOnePlus26Regression

open Integration.F4MinusculeOnePlus26

example : zeroPermutationImage.card = 6 := zero_permutation_image_card_6
example : zeroPermOrbitN 4 = zeroPermutationImage := zero_permutation_image_stable
example : foldedZeroTrace f4UnitCandidate = 3 := folded_zero_trace_unit
example : Module.finrank ℝ F4TracelessCandidate = 26 :=
  f4_traceless_candidate_finrank_26
example : ∀ g, f4WeylLinearAction g f4UnitCandidate = f4UnitCandidate :=
  folded_action_fixes_unit
example : ∀ g f, foldedZeroTrace (f4WeylLinearAction g f) = foldedZeroTrace f :=
  folded_action_preserves_trace
example : canonicalBoundary.zeroWeightTripleExplicit = true := rfl
example : canonicalBoundary.zeroWeightPermutationImageS3Paid = true := rfl
example : canonicalBoundary.invariantAllOnesLinePaid = true := rfl
example : canonicalBoundary.traceKernelDimension26Paid = true := rfl
example : canonicalBoundary.foldedWeylPreservesTraceKernelPaid = true := rfl
example : canonicalBoundary.finiteRepresentationOnePlus26Paid = true := rfl
example : canonicalBoundary.actualAlbertProductCompatibilityPaidHere = false := rfl
example : canonicalBoundary.actualAlbertUnitIdentificationPaidHere = false := rfl

end Integration.F4MinusculeOnePlus26Regression
