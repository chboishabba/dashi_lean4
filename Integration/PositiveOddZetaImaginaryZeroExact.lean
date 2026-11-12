import Integration.BishopOddZetaHalfPlaneSpecialization
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Positive odd Riemann zeta values have zero imaginary part

External mathematical sources: Dirichlet's convergent zeta series for
Re(s)>1, its Mathlib theorem `zeta_nat_eq_tsum_of_gt_one`, and
`Complex.ofReal_tsum`. The latter preserves the ORIGINAL value of the
infinite series, rather than introducing a new complex function.

DASHI contribution: specialize this source to all positive odd integers,
the Z7 eight-member window and the source-faithful Bishop/Dirichlet
15-member window. This is a Lean companion, not Agda kernel acceptance,
nor a proof that one particular odd zeta value is irrational.

No 'sorry', new axiom, or arbitrary analytic-function interface.
Source-written; local kernel receipt and pinned version check pending.
-/

namespace Integration.PositiveOddZetaImaginaryZeroExact

open Integration.BishopOddZetaHalfPlaneSpecialization
open Integration.BishopRiemannZetaNativeMachinContinuity

noncomputable section

/-- Same actual value, computed as a REAL Dirichlet series at each
natural argument n>1, using only the selected Mathlib zeta. -/
theorem riemannZeta_nat_eq_real_tsum
    (n : ℕ) (hn : 1 < n) :
    riemannZeta (n : ℂ) =
      (((∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ n) : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one hn]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  push_cast
  rfl

theorem riemannZeta_nat_im_zero
    (n : ℕ) (hn : 1 < n) :
    (riemannZeta (n : ℂ)).im = 0 := by
  rw [riemannZeta_nat_eq_real_tsum n hn]
  simp

/-- Requested parameterization, including the lower-bound witness.
The theorem is also valid for n=2 and for all n>1. -/
theorem positive_odd_zeta_im_zero
    (k : ℕ) (hk : 1 ≤ k) :
    (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).im = 0 :=
  riemannZeta_nat_im_zero (2 * k + 1) (by omega)

/-- The eight odd values 7, 9, ..., 21 in the external Z7 theorem. -/
theorem z7_eight_window_im_zero (k : Fin 8) :
    (riemannZeta ((7 + 2 * k.val : ℕ) : ℂ)).im = 0 :=
  riemannZeta_nat_im_zero (7 + 2 * k.val) (by omega)

/-- The fifteen values 5, 7, ..., 33 used by the original Bishop
witness transport; the value is the same Mathlib `riemannZeta`. -/
theorem fifteen_window_im_zero (k : Fin 15) :
    (riemannZeta ((oddArgument k.val : ℕ) : ℂ)).im = 0 :=
  riemannZeta_nat_im_zero (oddArgument k.val) (by
    unfold oddArgument
    omega)

/-- The pre-existing Bishop/Dirichlet coefficient series inherits the
genuine Mathlib zero-imaginary-coordinate property by SAME-VALUE
equality, not by a new or assumed continuity theorem. -/
theorem originalDirichlet_fifteen_window_im_zero (k : Fin 15) :
    (originalDirichletValue ((oddArgument k.val : ℕ) : ℂ)).im = 0 := by
  rw [originalOddWindow_eq_riemannZeta]
  exact fifteen_window_im_zero k

#print axioms riemannZeta_nat_eq_real_tsum
#print axioms positive_odd_zeta_im_zero
#print axioms originalDirichlet_fifteen_window_im_zero

end
end Integration.PositiveOddZetaImaginaryZeroExact
