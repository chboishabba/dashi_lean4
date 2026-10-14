import Integration.RationalAlbertCubicRigidity
import Mathlib

/-!
# Native norm+unit rigidity on the rational Albert carrier

This file pays the local premise isolated by `RationalAlbertCubicRigidity`.
The proof uses only the literal rational coordinates, the already-recovered
trace pairing, cubic polarization, and bijectivity.  It does not invoke or
manufacture the global classification `Aut(J) = F4`.
-/

namespace Integration.RationalAlbertCubicRigidity

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertCubicNormStructure
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

/-- The octonion trace pairing is nondegenerate in the second argument on the
literal eight rational coordinates. -/
theorem innerO_nondegenerate_right
    (x y : RationalOctonion)
    (h : ∀ z, innerO x z = innerO y z) : x = y := by
  rcases x with ⟨⟨a0,a1,a2,a3⟩,⟨b0,b1,b2,b3⟩⟩
  rcases y with ⟨⟨c0,c1,c2,c3⟩,⟨d0,d1,d2,d3⟩⟩
  have h0 := h ⟨⟨1,0,0,0⟩,⟨0,0,0,0⟩⟩
  have h1 := h ⟨⟨0,1,0,0⟩,⟨0,0,0,0⟩⟩
  have h2 := h ⟨⟨0,0,1,0⟩,⟨0,0,0,0⟩⟩
  have h3 := h ⟨⟨0,0,0,1⟩,⟨0,0,0,0⟩⟩
  have h4 := h ⟨⟨0,0,0,0⟩,⟨1,0,0,0⟩⟩
  have h5 := h ⟨⟨0,0,0,0⟩,⟨0,1,0,0⟩⟩
  have h6 := h ⟨⟨0,0,0,0⟩,⟨0,0,1,0⟩⟩
  have h7 := h ⟨⟨0,0,0,0⟩,⟨0,0,0,1⟩⟩
  simp [innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul,
    RationalQuaternion.conj] at h0 h1 h2 h3 h4 h5 h6 h7
  apply RationalOctonion.ext
  · apply RationalQuaternion.ext <;> assumption
  · apply RationalQuaternion.ext <;> assumption

/-- The native Albert trace pairing is nondegenerate.  Three diagonal probes
recover the scalar coordinates; three octonion probe families recover the
remaining 24 coordinates through `innerO_nondegenerate_right`. -/
theorem tracePair_nondegenerate_right
    (X Y : A27)
    (h : ∀ Z, tracePair X Z = tracePair Y Z) : X = Y := by
  apply RationalAlbert.ext
  · have hz := h ⟨1,0,0,0,0,0⟩
    simpa [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] using hz
  · have hz := h ⟨0,1,0,0,0,0⟩
    simpa [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] using hz
  · have hz := h ⟨0,0,1,0,0,0⟩
    simpa [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] using hz
  · apply innerO_nondegenerate_right
    intro z
    have hz := h ⟨0,0,0,z,0,0⟩
    simp [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] at hz
    linarith
  · apply innerO_nondegenerate_right
    intro z
    have hz := h ⟨0,0,0,0,z,0⟩
    simp [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] at hz
    linarith
  · apply innerO_nondegenerate_right
    intro z
    have hz := h ⟨0,0,0,0,0,z⟩
    simp [tracePair, innerO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul,
      RationalQuaternion.conj] at hz
    linarith

/-- A linear cubic symmetry preserves every affine-line cubic coefficient. -/
theorem unitFixingNorm_preserves_line_cubic
    (g : UnitFixingNormSymmetry) (X Y : A27) (q : ℚ) :
    cubic (g.forward X + q • g.forward Y) = cubic (X + q • Y) := by
  calc
    cubic (g.forward X + q • g.forward Y)
        = cubic (g.forward (X + q • Y)) := by
            rw [g.map_add, g.map_smul]
    _ = cubic (X + q • Y) := g.map_cubic _

/-- The gradient coefficient of the cubic is invariant under the symmetry. -/
theorem unitFixingNorm_preserves_cubicLinearCoefficient
    (g : UnitFixingNormSymmetry) (X Y : A27) :
    cubicLinearCoefficient (g.forward X) (g.forward Y) =
      cubicLinearCoefficient X Y := by
  have h1 := unitFixingNorm_preserves_line_cubic g X Y (1 : ℚ)
  have hm1 := unitFixingNorm_preserves_line_cubic g X Y (-1 : ℚ)
  have h2 := unitFixingNorm_preserves_line_cubic g X Y (2 : ℚ)
  have hm2 := unitFixingNorm_preserves_line_cubic g X Y (-2 : ℚ)
  simp at h1 hm1 h2 hm2
  simp [cubicLinearCoefficient, h1, hm1, h2, hm2]

/-- Unit+cubic preservation forces preservation of the reconstructed trace. -/
theorem unitFixingNorm_preserves_trace
    (g : UnitFixingNormSymmetry) (X : A27) :
    trace (g.forward X) = trace X := by
  rw [← traceFromNorm_eq, ← traceFromNorm_eq, traceFromNorm]
  calc
    cubicLinearCoefficient unit (g.forward X)
        = cubicLinearCoefficient (g.forward unit) (g.forward X) := by
            rw [g.map_unit]
    _ = cubicLinearCoefficient unit X :=
      unitFixingNorm_preserves_cubicLinearCoefficient g unit X

/-- The quadratic trace coefficient is likewise fixed. -/
theorem unitFixingNorm_preserves_quadraticTraceFromNorm
    (g : UnitFixingNormSymmetry) (X : A27) :
    quadraticTraceFromNorm (g.forward X) = quadraticTraceFromNorm X := by
  have h1 := unitFixingNorm_preserves_line_cubic g unit X (1 : ℚ)
  have hm1 := unitFixingNorm_preserves_line_cubic g unit X (-1 : ℚ)
  rw [g.map_unit] at h1 hm1
  simp at h1 hm1
  simp [quadraticTraceFromNorm, h1, hm1]

/-- Hence the entire bilinear trace pairing reconstructed from `N` and `1` is
preserved. -/
theorem unitFixingNorm_preserves_tracePair
    (g : UnitFixingNormSymmetry) (X Y : A27) :
    tracePair (g.forward X) (g.forward Y) = tracePair X Y := by
  rw [← tracePairFromNorm_eq, ← tracePairFromNorm_eq]
  simp only [tracePairFromNorm]
  rw [traceFromNorm_eq, traceFromNorm_eq, traceFromNorm_eq, traceFromNorm_eq]
  rw [unitFixingNorm_preserves_trace g X, unitFixingNorm_preserves_trace g Y]
  rw [← g.map_add]
  rw [unitFixingNorm_preserves_quadraticTraceFromNorm g (X + Y)]
  rw [unitFixingNorm_preserves_quadraticTraceFromNorm g X]
  rw [unitFixingNorm_preserves_quadraticTraceFromNorm g Y]

/-- Nondegeneracy turns invariance of the cubic gradient pairing into literal
adjoint intertwining. -/
theorem unitFixingNorm_preserves_adjoint
    (g : UnitFixingNormSymmetry) (X : A27) :
    adjoint (g.forward X) = g.forward (adjoint X) := by
  apply tracePair_nondegenerate_right
  intro Y
  let Z := g.backward Y
  have hYZ : g.forward Z = Y := g.forward_backward Y
  calc
    tracePair (adjoint (g.forward X)) Y
        = tracePair (adjoint (g.forward X)) (g.forward Z) := by rw [hYZ]
    _ = cubicLinearCoefficient (g.forward X) (g.forward Z) :=
      (cubicLinearCoefficient_eq (g.forward X) (g.forward Z)).symm
    _ = cubicLinearCoefficient X Z :=
      unitFixingNorm_preserves_cubicLinearCoefficient g X Z
    _ = tracePair (adjoint X) Z := cubicLinearCoefficient_eq X Z
    _ = tracePair (g.forward (adjoint X)) (g.forward Z) :=
      (unitFixingNorm_preserves_tracePair g (adjoint X) Z).symm
    _ = tracePair (g.forward (adjoint X)) Y := by rw [hYZ]

/-- The local rigidity premise is now inhabited on the native rational carrier.
This closes the structural unit-stabilizer -> Jordan-automorphism seam while
leaving abstract/algebraic-group F4 classification untouched. -/
def canonicalNormUnitRigidity : NormUnitRigidity where
  upgrade g :=
    { toUnitFixingNormSymmetry := g
      map_trace := unitFixingNorm_preserves_trace g
      map_tracePair := unitFixingNorm_preserves_tracePair g
      map_adjoint := unitFixingNorm_preserves_adjoint g }

/-- Direct theorem-facing corollary for consumers. -/
theorem unitFixingNormSymmetry_map_jordan
    (g : UnitFixingNormSymmetry) (X Y : A27) :
    g.forward (jordanProduct X Y) =
      jordanProduct (g.forward X) (g.forward Y) :=
  cubicNormAutomorphism_map_jordan (canonicalNormUnitRigidity.upgrade g) X Y

end Integration.RationalAlbertCubicRigidity
