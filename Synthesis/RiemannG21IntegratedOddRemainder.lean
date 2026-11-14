import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Synthesis.RiemannG21SineFifthRemainder

/-!
# G21 integrated sixth-scaled odd Taylor remainder

The historical cubic truncation

  T_y(r) = -6 r N1(y) + r^3 N3(y)

is the Taylor truncation of the literal `-6 sin(r u)` odd channel.  Therefore
the same-object integrated remainder is

  -6 [sin(ru) - (ru - (ru)^3/6)].

Its absolute value has the same fifth-order bound as the positive-six version:

  |E_y(r)| <= |r|^5 N5(y)/20.

With this sign, `T_y(r)+E_y(r)` is literally the integral of `-6 sin(ru)`
against `phi(u)sinh(yu)` on the positive half support.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- Fifth odd moment matching the historical G21 owner. -/
def oddN5 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, x^4 * oddHeightWeight R w y x ∂volume

/-- Same-object remainder for the literal `-6 sin` odd response. -/
def oddSixScaledRemainder
    (R : ℝ) (w : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ∫ x,
    g21ClippedWeight R w x * Real.sinh (y*x) *
      (-(6 * (Real.sin (r*x) - ((r*x) - (r*x)^3/6)))) ∂volume

/-- Exact integrated fifth-order bound. -/
theorem oddSixScaledRemainder_le_N5
    {w : ℝ → ℝ} {R y r : ℝ}
    (hy : 0 < y)
    (hw : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hN5 : Integrable (fun x => x^4 * oddHeightWeight R w y x) volume) :
    |oddSixScaledRemainder R w y r| <= |r|^5 * oddN5 R w y / 20 := by
  let g : ℝ → ℝ := fun x => (|r|^5 / 20) * (x^4 * oddHeightWeight R w y x)
  have hg : Integrable g volume := by
    dsimp [g]
    exact hN5.const_mul _
  have hpoint : ∀ x : ℝ,
      ‖g21ClippedWeight R w x * Real.sinh (y*x) *
        (-(6 * (Real.sin (r*x) - ((r*x) - (r*x)^3/6))))‖ <= g x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hx0 : 0 <= x := hx.1
      have hwx : 0 <= g21ClippedWeight R w x := by
        simpa [g21ClippedWeight, hx] using hw x hx
      have hsinh : 0 <= Real.sinh (y*x) :=
        (Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx0)
      have hs := six_scaled_sin_cubic_remainder (r*x)
      have hsneg :
          |-(6 * (Real.sin (r*x) - ((r*x) - (r*x)^3/6)))|
            <= |r*x|^5/20 := by
        simpa using hs
      have hbase : 0 <= g21ClippedWeight R w x * Real.sinh (y*x) :=
        mul_nonneg hwx hsinh
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hwx, abs_of_nonneg hsinh]
      have habspow : |r*x|^5 = |r|^5 * x^5 := by
        rw [abs_mul, abs_of_nonneg hx0, mul_pow]
      rw [habspow] at hsneg
      have hscaled := mul_le_mul_of_nonneg_left hsneg hbase
      dsimp [g, oddHeightWeight]
      rw [show g21ClippedWeight R w x * Real.sinh (y*x) *
          (|r|^5 * x^5 / 20)
          = (|r|^5 / 20) *
            (x^4 * (x * g21ClippedWeight R w x * Real.sinh (y*x))) by ring]
      exact hscaled
    · simp [g, oddHeightWeight, g21ClippedWeight, hx]
  have hnorm := norm_integral_le_of_norm_le hg (Eventually.of_forall hpoint)
  unfold oddSixScaledRemainder oddN5
  rw [Real.norm_eq_abs] at hnorm
  dsimp [g] at hnorm
  rw [integral_const_mul] at hnorm
  nlinarith

end Synthesis
