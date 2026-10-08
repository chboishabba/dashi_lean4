import Integration.OggSSP2BCo1FrobeniusHomRigidity

/-!
# Centralizer mod-2 cancellation rigidity frontier

The source-native weight-two Tate sequence has dimensions

  0 -> 98304 -> 98580 -> 276 -> 0.

The rational `C_M(2B)` branching is `98304_-` versus
`98280_+ ⊕ (1 ⊕ 299)_+`.  The CTblLib decomposition-matrix screen tests the
strong characteristic-two statement

  [98304]_2 = [98280]_2 + [24]

and the induced Tate profile `1,274,1`.  It also tests support separation of the
common `98280` factors from both residual lanes.

If that runtime receipt and the independent `Hom_Co1(24,Sym^2(24)) = 1` receipt
both pass, the remaining same-object seam is the actual norm-map placement on
the common 98280 extension lane, not an ambiguity of semisimplified content.
-/

namespace Integration.OggSSP2BCentralizerMod2CancellationRigidity

abbrev commonDimension : Nat := 98280
abbrev residualNaturalDimension : Nat := 24
abbrev minusDimension : Nat := 98304

theorem common_plus_residual_is_minus :
    commonDimension + residualNaturalDimension = minusDimension := by decide

structure RuntimeReceipt where
  candidateCount : Nat
  strongCandidateCount : Nat
  rigidSupportCandidateCount : Nat
  residual24IsSingleDegree24Simple : Bool
  residual276ProfileIsOne274One : Bool
  common98280SupportSeparatedFromResidual24 : Bool
  common98280SupportSeparatedFromResidual276 : Bool

structure Boundary where
  decompositionScreenImplemented : Bool
  runtimeDecompositionPaid : Bool
  actualTateJHProfileOne274OnePaid : Bool
  common98280SupportSeparated : Bool
  actualNormCommon98280IsomorphismPaid : Bool
  actualTateExteriorSquareWeldPaid : Bool

def canonicalBoundary : Boundary where
  decompositionScreenImplemented := true
  runtimeDecompositionPaid := false
  actualTateJHProfileOne274OnePaid := false
  common98280SupportSeparated := false
  actualNormCommon98280IsomorphismPaid := false
  actualTateExteriorSquareWeldPaid := false

theorem runtime_still_open : canonicalBoundary.runtimeDecompositionPaid = false := rfl
 theorem common_98280_norm_map_still_open : canonicalBoundary.actualNormCommon98280IsomorphismPaid = false := rfl
 theorem same_object_weld_still_open : canonicalBoundary.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BCentralizerMod2CancellationRigidity
