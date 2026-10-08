import Integration.OggSSP2BTatePlusMinusCokernel

/-!
# Co1 Frobenius-square Hom rigidity frontier

The actual weight-two 2B Tate object is a centralizer-equivariant cokernel

  L-/2L- -> L+/2L+ -> Tate276 -> 0

with dimensions 98304 -> 98580 -> 276.  The finite Co1 route isolates the
candidate residual map 24 -> 300 = Sym^2(24).  The explicit Frobenius-square
embedding has image dimension 24 and quotient wedge^2(24), dimension 276.

The accompanying GAP screen computes `Hom_Co1(24, Sym^2(24))`.  If that Hom
space is one-dimensional, then over GF(2) the explicit Frobenius-square map is
the unique nonzero equivariant map.  This removes ambiguity from the residual
24-dimensional lane; it does not identify the common 98280-dimensional part of
the actual norm map.
-/

namespace Integration.OggSSP2BCo1FrobeniusHomRigidity

abbrev naturalDimension : Nat := 24
abbrev symmetricSquareDimension : Nat := 300
abbrev frobeniusImageDimension : Nat := 24
abbrev exteriorQuotientDimension : Nat := symmetricSquareDimension - frobeniusImageDimension

theorem exterior_quotient_dimension_is_276 : exteriorQuotientDimension = 276 := by decide

structure RuntimeReceipt where
  hom24ToSym2Dimension : Nat
  explicitFrobeniusRank : Nat
  uniqueNonzeroHomLine : Bool
  explicitFrobeniusSpansHom : Bool

structure Boundary where
  explicitFrobeniusEmbeddingConstructed : Bool
  homUniquenessScreenImplemented : Bool
  homUniquenessRuntimePaid : Bool
  residual24LaneRigid : Bool
  common98280MapIdentified : Bool
  actualTateExteriorSquareWeldPaid : Bool

def canonicalBoundary : Boundary where
  explicitFrobeniusEmbeddingConstructed := true
  homUniquenessScreenImplemented := true
  homUniquenessRuntimePaid := false
  residual24LaneRigid := false
  common98280MapIdentified := false
  actualTateExteriorSquareWeldPaid := false

theorem runtime_still_open : canonicalBoundary.homUniquenessRuntimePaid = false := rfl
 theorem common_98280_map_still_open : canonicalBoundary.common98280MapIdentified = false := rfl
 theorem same_object_weld_still_open : canonicalBoundary.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BCo1FrobeniusHomRigidity
