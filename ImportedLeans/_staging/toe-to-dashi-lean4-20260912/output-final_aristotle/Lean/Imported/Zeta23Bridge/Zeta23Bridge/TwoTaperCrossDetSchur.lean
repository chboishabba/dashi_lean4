/-
# The two-taper cross determinant as the Gram admission certificate

With exactly two admissible tapers every channel is a vector in `ℝ²`, and the
Gram determinant of a nuisance vector `n` and a target vector `x` collapses to
the square of the ordinary scalar cross determinant

    det₂(n, x) = n₀ x₁ - n₁ x₀.

So the first concrete admission test of the Schur programme is a *single scalar*:

    det₂(n, x) ≠ 0  ⟹  wedgeSq n x > 0  ⟹  P_{n^⊥} x ≠ 0,

i.e. the target survives the exact removal of the nuisance direction.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.MultiTaperSchurCore

noncomputable section

namespace Zeta23Bridge
namespace TwoTaperCrossDetSchur

open Zeta23Bridge.MultiTaperSchurCore

/-- The scalar cross determinant of two two-taper channel vectors. -/
def det2 (n x : Fin 2 → ℝ) : ℝ := n 0 * x 1 - n 1 * x 0

/-- **Lagrange's identity in the plane**: the Gram determinant of a pair of
two-taper channel vectors is the square of their cross determinant. -/
theorem wedgeSq_eq_det2_sq (n x : Fin 2 → ℝ) : wedgeSq n x = det2 n x ^ 2 := by
  unfold wedgeSq normSqP dotP det2
  simp only [Fin.sum_univ_two]
  ring

/-- A nonzero cross determinant is a strict Gram wedge. -/
theorem wedgeSq_pos_of_det2_ne_zero {n x : Fin 2 → ℝ} (h : det2 n x ≠ 0) : 0 < wedgeSq n x := by
  rw [wedgeSq_eq_det2_sq]
  exact pow_pos (abs_pos.mpr h) 2 |>.trans_le (le_of_eq (sq_abs _))

/-- **The admission certificate.**  If the cross determinant of the nuisance vector
and the target vector is nonzero, the target survives the exact elimination of the
nuisance direction. -/
theorem transverseComp_ne_zero_of_det2_ne_zero {n x : Fin 2 → ℝ} (h : det2 n x ≠ 0) :
    transverseComp n x ≠ 0 :=
  transverseComp_ne_zero_of_wedgeSq_pos (wedgeSq_pos_of_det2_ne_zero h)

/-- The direct proof of the same fact, without the Gram determinant: if the
transverse component vanishes then `x` is a scalar multiple of `n`, so the cross
determinant vanishes too. -/
theorem det2_eq_zero_of_transverseComp_eq_zero {n x : Fin 2 → ℝ}
    (h : transverseComp n x = 0) : det2 n x = 0 := by
  have hx : x = (dotP n x / normSqP n) • n := by
    have := congrArg (fun y : Fin 2 → ℝ => y + (dotP n x / normSqP n) • n) h
    simpa [transverseComp, sub_add_cancel] using this
  rw [hx]
  unfold det2
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The nuisance direction of a nonzero cross determinant is itself nonzero. -/
theorem ne_zero_of_det2_ne_zero {n x : Fin 2 → ℝ} (h : det2 n x ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact h (by simp [det2])

end TwoTaperCrossDetSchur
end Zeta23Bridge
