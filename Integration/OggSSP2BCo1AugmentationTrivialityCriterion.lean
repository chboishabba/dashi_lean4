import Integration.OggSSP2BMod4ExtensionAcquisition

/-!
# Co1 augmentation-filtration triviality criterion

For P ~= F2^24 normal in P.Co1, the augmentation filtration of any
characteristic-two module has P-trivial graded pieces and multiplication maps

  24 ⊗ gr_i(M) -> gr_{i+1}(M)

which are Co1-equivariant.  If the Co1 composition factors are only 1 and 274,
and the four possible Hom spaces from 24⊗X to Y (X,Y in {1,274}) vanish, then
there is no nonzero first augmentation action, so P acts trivially.

This owner records the exact promotion interface used by the GAP Hom screen.  It
intentionally does not claim the runtime vanishings or the actual Tate 1/274/1
profile before those receipts exist.
-/

namespace Integration.OggSSP2BCo1AugmentationTrivialityCriterion

structure HomReceipt where
  hom24To1Dimension : Nat
  hom24To274Dimension : Nat
  hom24Tensor274To1Dimension : Nat
  hom24Tensor274To274Dimension : Nat
  allRelevantHomSpacesZero : Bool

structure TateCo1ProfileReceipt where
  trivialFactorCount : Nat
  factor274Count : Nat
  unidentifiedFactorCount : Nat
  profileIsOne274One : Bool

structure PromotionBoundary where
  homReceiptRuntimePaid : Bool
  actualTateCo1ProfilePaid : Bool
  augmentationFiltrationCriterionAvailable : Bool
  normal2Pow24ActionOnActualTateProvedTrivial : Bool

def canonicalBoundary : PromotionBoundary where
  homReceiptRuntimePaid := false
  actualTateCo1ProfilePaid := false
  augmentationFiltrationCriterionAvailable := true
  normal2Pow24ActionOnActualTateProvedTrivial := false

 theorem promotion_not_yet_paid :
    canonicalBoundary.normal2Pow24ActionOnActualTateProvedTrivial = false := rfl

end Integration.OggSSP2BCo1AugmentationTrivialityCriterion
