import Integration.OggSSP2BWeightTwoIntegralC2Decomposition

/-!
# Weight-two 2B Tate as a mod-2 plus/minus cokernel

For the sourced integral C2 decomposition E+^276 ⊕ E0^98304, reduction mod 2
identifies the minus generator e-ae of each E0 with its plus generator e+ae.
Thus the Tate quotient is structurally the cokernel

  0 -> L-/2L- -> L+/2L+ -> Hhat^0(<a>,L) -> 0

with dimensions 98304 -> 98580 -> 276.  The actual same-object issue is the
centralizer-equivariant embedding: the candidate is a common 98280 piece plus
the Frobenius-square 24 inside the 300 = Sym^2(24) positive piece, leaving
300/24 = wedge^2(24).
-/

namespace Integration.OggSSP2BTatePlusMinusCokernel

abbrev minusReductionDimension : Nat := 98304
abbrev plusReductionDimension : Nat := 98580
abbrev tateCokernelDimension : Nat := 276
abbrev positiveOrdinaryPiece98280 : Nat := 98280
abbrev positiveOrdinaryPiece300 : Nat := 300
abbrev candidateFrobeniusSquareDimension : Nat := 24
abbrev candidateNormReductionDimension : Nat := positiveOrdinaryPiece98280 + candidateFrobeniusSquareDimension
abbrev candidateSym2QuotientDimension : Nat := positiveOrdinaryPiece300 - candidateFrobeniusSquareDimension

theorem dimension_closure :
    minusReductionDimension + tateCokernelDimension = plusReductionDimension := by decide
 theorem positive_branch_closure :
    positiveOrdinaryPiece98280 + positiveOrdinaryPiece300 = plusReductionDimension := by decide
 theorem candidate_norm_dimension_is_98304 :
    candidateNormReductionDimension = minusReductionDimension := by decide
 theorem candidate_sym2_quotient_is_276 : candidateSym2QuotientDimension = 276 := by decide

structure Boundary where
  integralEPlusE0DecompositionPaid : Bool
  modTwoMinusToPlusCokernelStructurePaid : Bool
  centralizerEquivarianceStructural : Bool
  virtualBrauerCharacterShadowPassed : Bool
  sym2Frobenius24QuotientConstructed : Bool
  actualMinusReductionEmbeddingIdentified : Bool
  actualTateIdentifiedWithWedge2_24 : Bool

def canonicalBoundary : Boundary where
  integralEPlusE0DecompositionPaid := true
  modTwoMinusToPlusCokernelStructurePaid := true
  centralizerEquivarianceStructural := true
  virtualBrauerCharacterShadowPassed := true
  sym2Frobenius24QuotientConstructed := true
  actualMinusReductionEmbeddingIdentified := false
  actualTateIdentifiedWithWedge2_24 := false

end Integration.OggSSP2BTatePlusMinusCokernel
