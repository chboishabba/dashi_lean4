import Mathlib

/-!
# Physical time normalization of the Wilson half-rate

The lattice-step half-rate `2^{-n}` only becomes a physical mass after a
positive Euclidean time step `a` has been identified.  If a spectral mode of
energy `E` contributes transfer eigenvalue `exp (-a E)` and the same-H
half-rate forces that eigenvalue below `1/2`, then necessarily

  E >= log 2 / a.

This file proves only that elementary normalization implication.  It does not
select the physical lattice spacing or manufacture the spectral-mode premise.
-/

namespace RequestProject.YangMills

/-- `1/2` is the exponential of `-log 2`. -/
theorem half_eq_exp_neg_log_two :
    (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/--
A transfer eigenvalue at most one half over physical Euclidean time step `a`
forces the corresponding energy above `log 2 / a`.
-/
theorem energy_ge_log_two_div_step_of_half_rate
    (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E := by
  rw [half_eq_exp_neg_log_two] at hDecay
  have hExp : -a * E ≤ -Real.log 2 := by
    exact Real.exp_le_exp.mp hDecay
  have hMul : Real.log 2 ≤ a * E := by
    linarith
  exact (div_le_iff₀ ha).2 hMul

/--
Contrapositive form used by the spectral-window argument: any energy strictly
below the half-rate mass floor produces a one-step transfer value strictly
above one half.
-/
theorem transfer_above_half_of_energy_below_log_two_div_step
    (a E : ℝ) (ha : 0 < a)
    (hSubgap : E < Real.log 2 / a) :
    (1 / 2 : ℝ) < Real.exp (-a * E) := by
  by_contra hNotAbove
  have hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ) :=
    le_of_not_gt hNotAbove
  have hFloor :=
    energy_ge_log_two_div_step_of_half_rate a E ha hDecay
  exact (not_lt_of_ge hFloor) hSubgap

/--
Exact physical normalization receipt left to the Yang--Mills source: identify
one lattice transfer step with a strictly positive physical Euclidean time.
-/
structure WilsonPhysicalTimeStep where
  step : ℝ
  stepPositive : 0 < step

namespace WilsonPhysicalTimeStep

/-- Physical mass floor associated with the source half-rate. -/
def halfRateMassFloor (time : WilsonPhysicalTimeStep) : ℝ :=
  Real.log 2 / time.step

/-- The source half-rate gives the canonical mass floor once the time step is fixed. -/
theorem energy_ge_halfRateMassFloor
    (time : WilsonPhysicalTimeStep) (E : ℝ)
    (hDecay : Real.exp (-time.step * E) ≤ (1 / 2 : ℝ)) :
    time.halfRateMassFloor ≤ E :=
  energy_ge_log_two_div_step_of_half_rate
    time.step E time.stepPositive hDecay

/-- Any energy strictly below the mass floor maps to transfer value above one half. -/
theorem transfer_above_half_of_energy_below_massFloor
    (time : WilsonPhysicalTimeStep) (E : ℝ)
    (hSubgap : E < time.halfRateMassFloor) :
    (1 / 2 : ℝ) < Real.exp (-time.step * E) :=
  transfer_above_half_of_energy_below_log_two_div_step
    time.step E time.stepPositive hSubgap

end WilsonPhysicalTimeStep

end RequestProject.YangMills
