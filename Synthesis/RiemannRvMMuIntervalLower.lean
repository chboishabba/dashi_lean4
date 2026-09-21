import Synthesis.RiemannRvMMuHighUniformLower
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Linear lower mass for the exact RvM density on high intervals

The crude pointwise bound mu(tau) >= 1/20 for tau>=100 integrates directly:

  integral_A^B mu(tau) d tau >= (B-A)/20

whenever 100 <= A <= B.

This deliberately weak linear lower bound is already sufficient for the
quartic macroscopic-window argument, because the arbitrary-endpoint counting
error is only logarithmic.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

theorem zetaMu_intervalIntegral_ge_width_div_twenty
    {A B : ℝ}
    (hA : 100 <= A)
    (hAB : A <= B) :
    (B - A) / 20
      <=
    ∫ tau in A..B, Zeta23.mu tau := by
  have hconst :
      IntervalIntegrable (fun _ : ℝ => (1/20 : ℝ)) volume A B :=
    intervalIntegrable_const
  have hmu :
      IntervalIntegrable Zeta23.mu volume A B :=
    Zeta23.gammaFacts.smooth.continuous.intervalIntegrable A B
  have hpoint :
      ∀ tau ∈ Set.Icc A B,
        (1/20 : ℝ) <= Zeta23.mu tau := by
    intro tau htau
    exact zetaMu_ge_one_twentieth_of_hundred_le
      (hA.trans htau.1)
  have hmono :=
    intervalIntegral.integral_mono_on
      hAB hconst hmu hpoint
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmono

end Synthesis
