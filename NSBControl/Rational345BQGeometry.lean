import Mathlib.Tactic
import NSBControl.Rational345RealInitialState

/-!
# B_Q radius-four geometry and bootstrap-ball constants

This file contains only finite geometric facts needed by the coarse vector
field bound.  The bootstrap radius is 1.  On that ball the state sup norm is
at most 7 because the exact 3-4-5 initial state has sup norm at most 6.

The finite Leray ratio certificate is kept at the integer level:

  2 |k_j| (|kx|+|ky|+|kz|) <= 3 |k|^2.

It is executable over all 9^3 radius-four modes and three components.
-/

namespace NSBControl
namespace Rational345BQGeometry

open Rational345RealRadius4
open Rational345RealInitialState

classical

def bootstrapRadius : ℝ := 1

def absCoord (k : Mode) (j : Fin 3) : ℕ :=
  Int.natAbs (kInt k j)

def sumAbs (k : Mode) : ℕ :=
  absCoord k 0 + absCoord k 1 + absCoord k 2

def normSqNat (k : Mode) : ℕ :=
  absCoord k 0 ^ 2 + absCoord k 1 ^ 2 + absCoord k 2 ^ 2

/-- Every centered radius-four coordinate has absolute value at most four. -/
theorem axisInt_abs_le_four (i : Fin 9) : Int.natAbs (axisInt i) ≤ 4 := by
  fin_cases i <;> norm_num [axisInt]

theorem axisInt_real_abs_le_four (i : Fin 9) : |(axisInt i : ℝ)| ≤ 4 := by
  fin_cases i <;> norm_num [axisInt]

theorem kReal_abs_le_four (k : Mode) (j : Fin 3) : |kReal k j| ≤ 4 := by
  fin_cases j
  · simpa [kReal, kInt] using axisInt_real_abs_le_four k.x
  · simpa [kReal, kInt] using axisInt_real_abs_le_four k.y
  · simpa [kReal, kInt] using axisInt_real_abs_le_four k.z

private theorem sq_le_sixteen {x : ℝ} (h : |x| ≤ 4) : x ^ 2 ≤ 16 := by
  have hx := abs_le.mp h
  have hp : 0 ≤ (4 - x) * (4 + x) :=
    mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hx.1)
  nlinarith

/-- Uniform Laplacian eigenvalue bound on the radius-four cube. -/
theorem normSq_le_48 (k : Mode) : normSq k ≤ 48 := by
  have h0 := sq_le_sixteen (kReal_abs_le_four k 0)
  have h1 := sq_le_sixteen (kReal_abs_le_four k 1)
  have h2 := sq_le_sixteen (kReal_abs_le_four k 2)
  simp [normSq, Fin.sum_univ_succ]
  nlinarith

/-- Integer form of the componentwise Leray multiplier bound.  Native
computation checks all 2187 mode/component pairs. -/
theorem leray_ratio_nat :
    ∀ (k : Mode) (j : Fin 3),
      2 * absCoord k j * sumAbs k ≤ 3 * normSqNat k := by
  native_decide

/-- The initial state has component-sup norm at most six. -/
theorem u₀_norm_le_six : ‖u₀‖ ≤ 6 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro k
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  unfold u₀
  split_ifs with h1 h2 h3 h4 h5 h6
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [v300])
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [vecConj, v300])
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [v040])
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [vecConj, v040])
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [v340])
  · subst k
    fin_cases j <;>
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
        norm_num [vecConj, v340])
  · simp

/-- Radius-one bootstrap states have sup norm at most seven. -/
theorem norm_le_seven_of_mem_bootstrapBall
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius) :
    ‖x‖ ≤ 7 := by
  have hdist : ‖x - u₀‖ ≤ 1 := by
    simpa [bootstrapRadius, Metric.mem_closedBall, dist_eq_norm] using hx
  calc
    ‖x‖ = ‖(x - u₀) + u₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - u₀‖ + ‖u₀‖ := norm_add_le _ _
    _ ≤ 1 + 6 := add_le_add hdist u₀_norm_le_six
    _ = 7 := by norm_num

/-- Every scalar component of a bootstrap state is bounded by seven. -/
theorem component_norm_le_seven_of_mem_bootstrapBall
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖x k j‖ ≤ 7 := by
  exact (norm_le_pi_norm (x k) j).trans
    ((norm_le_pi_norm x k).trans (norm_le_seven_of_mem_bootstrapBall hx))

end Rational345BQGeometry
end NSBControl
