import Integration.RationalAlbertNative
import Mathlib

/-!
# Explicit S3 automorphisms of the native rational Albert algebra

Native Lean mirror of the Agda `RationalAlbertS3Automorphism*` owners.
These are genuine coordinate automorphisms of the explicit rational Jordan
product/cubic, but only an S3 subgroup; no promotion to full F4 occurs here.
-/

namespace Integration.RationalAlbertS3Native

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open RationalAlbertNative.RationalAlbert

abbrev A := RationalAlbertNative.RationalAlbert

/-- 3-cycle of the three Hermitian axes. -/
def cycleA (X : A) : A :=
  ⟨X.diagonal2,X.diagonal0,X.diagonal1,X.off01,X.off12,X.off20⟩

/-- Transposition of the last two Hermitian axes, including conjugation on
corresponding octonion slots. -/
def swapA (X : A) : A :=
  ⟨X.diagonal0,X.diagonal2,X.diagonal1,
   RationalOctonion.conj X.off12,
   RationalOctonion.conj X.off01,
   RationalOctonion.conj X.off20⟩

@[simp] theorem cycle_cubed (X : A) : cycleA (cycleA (cycleA X)) = X := by
  cases X <;> rfl

@[simp] theorem swap_squared (X : A) : swapA (swapA X) = X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  simp [swapA, RationalOctonion.conj_involutive]

/-- `srs=r⁻¹=r²`. -/
theorem swap_cycle_swap (X : A) : swapA (cycleA (swapA X)) = cycleA (cycleA X) := by
  rcases X with ⟨a,b,c,x,y,z⟩
  simp [swapA,cycleA,RationalOctonion.conj_involutive]

@[simp] theorem cycle_unit : cycleA unit = unit := by rfl
@[simp] theorem swap_unit : swapA unit = unit := by
  simp [swapA,unit,RationalOctonion.conj]

@[simp] theorem cycle_trace (X : A) : trace (cycleA X) = trace X := by
  simp [trace,cycleA]; ring

@[simp] theorem swap_trace (X : A) : trace (swapA X) = trace X := by
  simp [trace,swapA]; ring

/-- The cycle is an actual Jordan-product automorphism. -/
theorem cycle_preserves_product (X Y : A) :
    cycleA (jordanProduct X Y) = jordanProduct (cycleA X) (cycleA Y) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [cycleA,jordanProduct,innerO, RationalAlbert.halfO,
      RationalOctonion.mul,RationalOctonion.conj,RationalOctonion.realPart,
      RationalQuaternion.mul,RationalQuaternion.conj] <;> ring

/-- The transposition is an actual Jordan-product automorphism. -/
theorem swap_preserves_product (X Y : A) :
    swapA (jordanProduct X Y) = jordanProduct (swapA X) (swapA Y) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [swapA,jordanProduct,innerO, RationalAlbert.halfO,
      RationalOctonion.mul,RationalOctonion.conj,RationalOctonion.realPart,
      RationalQuaternion.mul,RationalQuaternion.conj] <;> ring

/-- The standard cubic is invariant under cyclic permutation of slots. -/
theorem cycle_preserves_cubic (X : A) : cubic (cycleA X) = cubic X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [cubic,cycleA,RationalOctonion.normSq,RationalOctonion.mul,
    RationalOctonion.realPart,RationalQuaternion.mul,RationalQuaternion.normSq,
    RationalQuaternion.conj]
  ring

/-- The standard cubic is invariant under the conjugating transposition. -/
theorem swap_preserves_cubic (X : A) : cubic (swapA X) = cubic X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [cubic,swapA,RationalOctonion.normSq,RationalOctonion.mul,
    RationalOctonion.conj,RationalOctonion.realPart,RationalQuaternion.mul,
    RationalQuaternion.normSq,RationalQuaternion.conj]
  ring

structure Boundary where
  orderThreePaid : Bool
  orderTwoPaid : Bool
  dihedralRelationPaid : Bool
  productPreservationSourceWritten : Bool
  traceUnitPreservationSourceWritten : Bool
  cubicPreservationSourceWritten : Bool
  genuineS3SubgroupSourceWritten : Bool
  fullF4Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  orderThreePaid := true
  orderTwoPaid := true
  dihedralRelationPaid := true
  productPreservationSourceWritten := true
  traceUnitPreservationSourceWritten := true
  cubicPreservationSourceWritten := true
  genuineS3SubgroupSourceWritten := true
  fullF4Paid := false

end Integration.RationalAlbertS3Native
