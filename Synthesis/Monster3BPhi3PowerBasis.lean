import Mathlib

/-!
# Monster 3B cyclotomic pair-coordinate seam

Tiny Lean donor for the DASHI/Agda `LeanPhi3PowerBasisCoordinateReceipt`.

Mathematical provenance remains Lawrence C. Washington, *Introduction to
Cyclotomic Fields*, 2nd ed., DOI 10.1007/978-1-4612-1934-7.  Machine-checked
implementation authority here is mathlib v4.28.0.  QID/Dewey/OEIS coordinates
are deliberately not proof inputs; OEIS A005052 remains numerical provenance
for `90 = 10 * 3^2` only and has no authority for this field equivalence.

This module proves only the exact `Q(zeta_3)` coordinate seam.  It does not
identify an actual Monster constituent, construct an FDRep, or prove the
12+78 inertia decomposition.
-/

namespace Synthesis
namespace Monster3BPhi3PowerBasis

noncomputable section

open Polynomial

/-- The canonical mathlib cyclotomic field used by the scalar-extension lane. -/
abbrev K := CyclotomicField 3 ℚ

/-- Mathlib's selected primitive cubic root in `CyclotomicField 3 ℚ`. -/
noncomputable def zeta : K := IsCyclotomicExtension.zeta 3 ℚ K

/-- The selected root really is primitive of order three. -/
theorem zeta_primitive : IsPrimitiveRoot zeta 3 := by
  simpa [zeta] using IsCyclotomicExtension.zeta_spec 3 ℚ K

/-- Primitive-root power basis of the cubic cyclotomic field. -/
noncomputable def powerBasis : PowerBasis ℚ K := zeta_primitive.powerBasis ℚ

/-- `Q(zeta_3)` has the expected two power-basis coordinates. -/
theorem powerBasis_dim_two : powerBasis.dim = 2 := by
  calc
    powerBasis.dim = Module.finrank ℚ K := (PowerBasis.finrank powerBasis).symm
    _ = Nat.totient 3 :=
      IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (by norm_num))
    _ = 2 := by norm_num

/-- Exact Phi_3 relation for the selected primitive root. -/
theorem phi3_relation : zeta ^ 2 + zeta + 1 = 0 := by
  have h := IsCyclotomicExtension.aeval_zeta 3 ℚ K
  rw [Polynomial.cyclotomic_three] at h
  simpa [zeta] using h

/-- Coordinates supplied by the primitive-root power basis, reindexed to the
literal pair `(u,v)`. -/
noncomputable def coordinateEquiv : K ≃ₗ[ℚ] (ℚ × ℚ) := by
  let e : K ≃ₗ[ℚ] (Fin powerBasis.dim → ℚ) := powerBasis.basis.equivFun
  let e2 : K ≃ₗ[ℚ] (Fin 2 → ℚ) := by
    simpa only [powerBasis_dim_two] using e
  exact e2.trans (LinearEquiv.piFinTwo ℚ (fun _ : Fin 2 => ℚ))

/-- The pair-to-field map is the inverse power-basis coordinate map. -/
noncomputable def pairToField : (ℚ × ℚ) → K := coordinateEquiv.symm

/-- Every cyclotomic-field element has one and only one rational pair of
coordinates.  This is the exact bijectivity payment required by the Agda
cross-prover receipt. -/
theorem uniquePairCoordinates (x : K) :
    ∃! p : ℚ × ℚ, pairToField p = x := by
  refine ⟨coordinateEquiv x, ?_, ?_⟩
  · exact coordinateEquiv.symm_apply_apply x
  · intro y hy
    apply coordinateEquiv.symm.injective
    simpa [pairToField] using hy

/-- The basis inverse is literally `u + v*zeta`, not merely an abstract
2-dimensional vector-space isomorphism. -/
theorem pairToField_eq_u_add_v_zeta (u v : ℚ) :
    pairToField (u, v) = algebraMap ℚ K u + algebraMap ℚ K v * zeta := by
  apply coordinateEquiv.injective
  ext <;>
    simp [coordinateEquiv, pairToField, powerBasis, zeta, zeta_primitive,
      PowerBasis.basis_eq_pow, Algebra.smul_def]

/-- Multiplication in pair coordinates is exactly reduction by
`zeta^2 = -zeta - 1`:
`(u,v)*(x,y) = (ux-vy, uy+vx-vy)`. -/
theorem pairToField_mul (u v x y : ℚ) :
    pairToField (u * x - v * y, u * y + v * x - v * y) =
      pairToField (u, v) * pairToField (x, y) := by
  rw [pairToField_eq_u_add_v_zeta, pairToField_eq_u_add_v_zeta,
    pairToField_eq_u_add_v_zeta]
  have hz2 : zeta ^ 2 = -zeta - 1 := by
    linear_combination phi3_relation
  rw [show zeta * zeta = -zeta - 1 by simpa [pow_two] using hz2]
  push_cast
  ring

end

end Monster3BPhi3PowerBasis
end Synthesis
