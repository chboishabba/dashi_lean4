import Integration.RationalAlbertCubicRigidity
import Integration.RationalAlbertTracePairNondegenerate
import Mathlib

/-!
# Native norm/unit rigidity for the rational Albert algebra

This closes the local cubic-rigidity seam left by
`RationalAlbertCubicRigidity`: a Q-linear bijection preserving the standard
Albert cubic and distinguished unit automatically preserves the reconstructed
trace, bilinear trace and adjoint.  Nondegeneracy of the native trace pairing
then upgrades it to a cubic-norm automorphism, hence to a Jordan automorphism.

The remaining exceptional-group theorem is therefore group/form
classification, not product recovery.
-/

namespace Integration.RationalAlbertNormUnitRigidityProof

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertCubicNormStructure
open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertTracePairNondegenerate
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

@[simp] theorem neg_one_smul (X : A27) : (-1 : ℚ) • X = -X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp

/-- Coordinate cancellation for the octonion carrier. -/
theorem oct_add_neg_eq_zero_implies_eq
    (x y : RationalOctonion) (h : x + (-y) = 0) : x = y := by
  rcases x with ⟨xa,xb⟩; rcases y with ⟨ya,yb⟩
  rcases xa with ⟨a0,a1,a2,a3⟩; rcases xb with ⟨b0,b1,b2,b3⟩
  rcases ya with ⟨c0,c1,c2,c3⟩; rcases yb with ⟨d0,d1,d2,d3⟩
  injection h with hfirst hsecond
  injection hfirst with h0 h1 h2 h3
  injection hsecond with h4 h5 h6 h7
  apply RationalOctonion.ext <;> apply RationalQuaternion.ext <;>
    simp at h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;> linarith

/-- Coordinate cancellation for the literal Albert carrier. -/
theorem albert_add_neg_eq_zero_implies_eq
    (X Y : A27) (h : X + (-Y) = 0) : X = Y := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  injection h with h0 h1 h2 hx hy hz
  apply RationalAlbert.ext
  · simp at h0; linarith
  · simp at h1; linarith
  · simp at h2; linarith
  · exact oct_add_neg_eq_zero_implies_eq x u hx
  · exact oct_add_neg_eq_zero_implies_eq y v hy
  · exact oct_add_neg_eq_zero_implies_eq z w hz

/-- The explicit trace pairing is additive in the first argument. -/
theorem tracePair_add_left (X Y Z : A27) :
    tracePair (X + Y) Z = tracePair X Z + tracePair Y Z := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases Z with ⟨p,q,r,l,m,n⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  rcases l with ⟨l1,l2⟩; rcases m with ⟨m1,m2⟩; rcases n with ⟨n1,n2⟩
  simp [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- The explicit trace pairing respects negation in the first argument. -/
theorem tracePair_neg_left (X Z : A27) :
    tracePair (-X) Z = -(tracePair X Z) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Z with ⟨p,q,r,l,m,n⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases l with ⟨l1,l2⟩; rcases m with ⟨m1,m2⟩; rcases n with ⟨n1,n2⟩
  simp [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Affine compatibility around the distinguished unit. -/
theorem map_unit_affine (g : UnitFixingNormSymmetry) (q : ℚ) (X : A27) :
    g.forward (unit + q • X) = unit + q • g.forward X := by
  rw [g.map_add, g.map_unit, g.map_smul]

/-- Cubic equality on every affine line through the distinguished unit. -/
theorem map_unit_affine_cubic (g : UnitFixingNormSymmetry) (q : ℚ) (X : A27) :
    cubic (unit + q • g.forward X) = cubic (unit + q • X) := by
  rw [← map_unit_affine g q X]
  exact g.map_cubic _

/-- The reconstructed linear trace is invariant under every unit-fixing norm
symmetry. -/
theorem normSymmetry_map_trace (g : UnitFixingNormSymmetry) (X : A27) :
    trace (g.forward X) = trace X := by
  rw [← traceFromNorm_eq, ← traceFromNorm_eq]
  unfold traceFromNorm cubicLinearCoefficient
  have h1 := map_unit_affine_cubic g (1 : ℚ) X
  have hm1 := map_unit_affine_cubic g (-1 : ℚ) X
  have h2 := map_unit_affine_cubic g (2 : ℚ) X
  have hm2 := map_unit_affine_cubic g (-2 : ℚ) X
  simpa [neg_one_smul] using congrArg id (by linarith [h1,hm1,h2,hm2] :
    (8 * (cubic (unit + g.forward X) - cubic (unit + (-g.forward X))) -
      (cubic (unit + (2 : ℚ) • g.forward X) - cubic (unit + (-2 : ℚ) • g.forward X))) / 12 =
    (8 * (cubic (unit + X) - cubic (unit + (-X))) -
      (cubic (unit + (2 : ℚ) • X) - cubic (unit + (-2 : ℚ) • X))) / 12)

/-- The quadratic trace reconstructed from the even norm coefficient is
invariant as well. -/
theorem normSymmetry_map_quadraticTrace (g : UnitFixingNormSymmetry) (X : A27) :
    quadraticTraceFromNorm (g.forward X) = quadraticTraceFromNorm X := by
  unfold quadraticTraceFromNorm
  have h1 := map_unit_affine_cubic g (1 : ℚ) X
  have hm1 := map_unit_affine_cubic g (-1 : ℚ) X
  simpa [neg_one_smul] using congrArg id (by linarith [h1,hm1] :
    (cubic (unit + g.forward X) + cubic (unit + (-g.forward X)) - 2) / 2 =
    (cubic (unit + X) + cubic (unit + (-X)) - 2) / 2)

/-- Hence the bilinear trace pairing is forced by the norm and unit. -/
theorem normSymmetry_map_tracePair (g : UnitFixingNormSymmetry) (X Y : A27) :
    tracePair (g.forward X) (g.forward Y) = tracePair X Y := by
  rw [← tracePairFromNorm_eq, ← tracePairFromNorm_eq]
  unfold tracePairFromNorm
  rw [traceFromNorm_eq, traceFromNorm_eq, traceFromNorm_eq, traceFromNorm_eq]
  rw [normSymmetry_map_trace, normSymmetry_map_trace]
  rw [← g.map_add]
  rw [normSymmetry_map_quadraticTrace, normSymmetry_map_quadraticTrace,
    normSymmetry_map_quadraticTrace]

/-- The cubic gradient coefficient is invariant on mapped pairs. -/
theorem normSymmetry_map_gradient (g : UnitFixingNormSymmetry) (X Y : A27) :
    tracePair (adjoint (g.forward X)) (g.forward Y) = tracePair (adjoint X) Y := by
  rw [← cubicLinearCoefficient_eq, ← cubicLinearCoefficient_eq]
  unfold cubicLinearCoefficient
  have hp (q : ℚ) :
      cubic (g.forward X + q • g.forward Y) = cubic (X + q • Y) := by
    rw [← g.map_smul, ← g.map_add]
    exact g.map_cubic _
  have h1 := hp (1 : ℚ)
  have hm1 := hp (-1 : ℚ)
  have h2 := hp (2 : ℚ)
  have hm2 := hp (-2 : ℚ)
  simpa [neg_one_smul] using congrArg id (by linarith [h1,hm1,h2,hm2] :
    (8 * (cubic (g.forward X + g.forward Y) - cubic (g.forward X + (-g.forward Y))) -
      (cubic (g.forward X + (2 : ℚ) • g.forward Y) - cubic (g.forward X + (-2 : ℚ) • g.forward Y))) / 12 =
    (8 * (cubic (X + Y) - cubic (X + (-Y))) -
      (cubic (X + (2 : ℚ) • Y) - cubic (X + (-2 : ℚ) • Y))) / 12)

/-- Nondegeneracy upgrades gradient preservation to literal adjoint
intertwining. -/
theorem normSymmetry_map_adjoint (g : UnitFixingNormSymmetry) (X : A27) :
    adjoint (g.forward X) = g.forward (adjoint X) := by
  let D : A27 := adjoint (g.forward X) + (-(g.forward (adjoint X)))
  have hzero : ∀ Z : A27, tracePair D Z = 0 := by
    intro Z
    let Y : A27 := g.backward Z
    have hZ : g.forward Y = Z := g.forward_backward Z
    have hgrad := normSymmetry_map_gradient g X Y
    have hpair := normSymmetry_map_tracePair g (adjoint X) Y
    rw [tracePair_add_left, tracePair_neg_left, hZ]
    linarith
  have hD : D = 0 := tracePair_nondegenerate D hzero
  unfold D at hD
  exact albert_add_neg_eq_zero_implies_eq
    (adjoint (g.forward X)) (g.forward (adjoint X)) hD

/-- The exact local rigidity payment. -/
def canonicalNormUnitRigidity : NormUnitRigidity where
  upgrade g :=
    { toUnitFixingNormSymmetry := g
      map_trace := normSymmetry_map_trace g
      map_tracePair := normSymmetry_map_tracePair g
      map_adjoint := normSymmetry_map_adjoint g }

/-- Therefore every Q-linear norm symmetry fixing the distinguished Albert unit
acts by Jordan automorphisms on the same carrier. -/
def jordanAutomorphismOfNormUnitSymmetry (g : UnitFixingNormSymmetry) :
    RationalJordanAutomorphism :=
  jordanAutomorphismOfUnitFixingNormSymmetry canonicalNormUnitRigidity g

structure Boundary where
  normSymmetryPreservesTrace : Bool
  normSymmetryPreservesTracePair : Bool
  nativeTracePairNondegenerate : Bool
  normSymmetryPreservesAdjoint : Bool
  unitFixingNormSymmetryIsJordan : Bool
  abstractAutomorphismGroupTypeF4 : Bool
  cubicSymmetryGroupTypeE6 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  normSymmetryPreservesTrace := true
  normSymmetryPreservesTracePair := true
  nativeTracePairNondegenerate := true
  normSymmetryPreservesAdjoint := true
  unitFixingNormSymmetryIsJordan := true
  abstractAutomorphismGroupTypeF4 := false
  cubicSymmetryGroupTypeE6 := false

end Integration.RationalAlbertNormUnitRigidityProof
