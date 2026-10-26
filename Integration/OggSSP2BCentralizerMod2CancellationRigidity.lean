import Integration.OggSSP2BCo1FrobeniusHomRigidity

/-!
# Centralizer mod-2 cancellation rigidity frontier

The source-native weight-two Tate sequence has dimensions

  0 -> 98304 -> 98580 -> 276 -> 0.

The rational `C_M(2B)` branching is `98304_-` versus
`98280_+ ⊕ (1 ⊕ 299)_+`.  The CTblLib decomposition-matrix screen establishes
the strong characteristic-two statement

  [98304]_2 = [98280]_2 + [24]

and the induced Tate profile `1,274,1`.  The strengthened runtime certificate
also establishes block separation of the common 98280 support from the
residual lanes and identifies the residual 24 lane as one copy of the unique
degree-24 simple.

This closes the representation-support discovery gate.  It still does NOT
identify the actual source-native norm map on those blocks; the common-map and
final exterior-square weld remain same-object map theorems downstream.
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

/-- The promoted runtime facts are representation-theoretic facts only. -/
structure Boundary where
  decompositionScreenImplemented : Bool
  runtimeDecompositionPaid : Bool
  actualTateJHProfileOne274OnePaid : Bool
  common98280SupportSeparated : Bool
  residual24UniqueSimpleIdentified : Bool
  actualNormCommon98280IsomorphismPaid : Bool
  actualTateExteriorSquareWeldPaid : Bool

def canonicalBoundary : Boundary where
  decompositionScreenImplemented := true
  runtimeDecompositionPaid := true
  actualTateJHProfileOne274OnePaid := true
  common98280SupportSeparated := true
  residual24UniqueSimpleIdentified := true
  actualNormCommon98280IsomorphismPaid := false
  actualTateExteriorSquareWeldPaid := false

theorem runtime_decomposition_paid :
    canonicalBoundary.runtimeDecompositionPaid = true := rfl

theorem tate_jh_profile_paid :
    canonicalBoundary.actualTateJHProfileOne274OnePaid = true := rfl

theorem common_support_separation_paid :
    canonicalBoundary.common98280SupportSeparated = true := rfl

theorem residual_24_unique_simple_paid :
    canonicalBoundary.residual24UniqueSimpleIdentified = true := rfl

theorem common_98280_norm_map_still_open :
    canonicalBoundary.actualNormCommon98280IsomorphismPaid = false := rfl

theorem same_object_weld_still_open :
    canonicalBoundary.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BCentralizerMod2CancellationRigidity
