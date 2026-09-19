import Mathlib

/-!
# Uniform quadratic-margin no-go for a fixed positive error

If the off-line margin vanishes like c*a^2 as a -> 0, then no fixed positive
error E independent of a can fit below that margin for every nonzero a.

This is the abstract obstruction behind the current centered-complement route:
a magnitude estimate with a positive a-independent remainder cannot by itself
close the uniform RH contradiction near the critical line.  One needs a
favourable sign, exact cancellation, or an error carrying its own a^2 factor.
-/

noncomputable section

namespace Synthesis

theorem exists_nonzero_square_margin_below_positive_error
    {E c : ℝ} (hE : 0 < E) (hc : 0 ≤ c) :
    ∃ a : ℝ, a ≠ 0 ∧ c * a ^ 2 < E := by
  have hc1 : 0 < c + 1 := by linarith
  let delta : ℝ := min 1 (E / (c + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos hE hc1)
  let a : ℝ := delta / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hadelta : a < delta := by
    dsimp [a]
    linarith
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdeltaE : delta ≤ E / (c + 1) := min_le_right _ _
  have ha1 : a < 1 := lt_of_lt_of_le hadelta hdelta1
  have haE : a < E / (c + 1) := lt_of_lt_of_le hadelta hdeltaE
  have hca2 : c * a ^ 2 ≤ c * a := by
    have ha0 : 0 ≤ a := ha.le
    have haa : a ^ 2 ≤ a := by nlinarith
    exact mul_le_mul_of_nonneg_left haa hc
  have hcaE : c * a < E := by
    have hsum : (c + 1) * a < E := by
      exact (lt_div_iff₀ hc1).mp haE
    nlinarith [ha]
  refine ⟨a, ne_of_gt ha, ?_⟩
  exact lt_of_le_of_lt hca2 hcaE

theorem fixed_positive_error_cannot_fit_all_nonzero_quadratic_margins
    {E c : ℝ} (hE : 0 < E) (hc : 0 ≤ c) :
    ¬ (∀ a : ℝ, a ≠ 0 → E < c * a ^ 2) := by
  intro hall
  obtain ⟨a, ha0, hsmall⟩ :=
    exists_nonzero_square_margin_below_positive_error hE hc
  have hlarge := hall a ha0
  linarith

/--
A terminal quadratic-margin route with an a-independent nonnegative remainder
can only be uniform if that remainder is not strictly positive.
-/
theorem nonpositive_of_uniform_strict_quadratic_fit
    {E c : ℝ} (hc : 0 ≤ c)
    (hall : ∀ a : ℝ, a ≠ 0 → E < c * a ^ 2) :
    E ≤ 0 := by
  by_contra h
  have hE : 0 < E := lt_of_not_ge h
  exact fixed_positive_error_cannot_fit_all_nonzero_quadratic_margins hE hc hall

end Synthesis
