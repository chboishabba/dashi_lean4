import Synthesis.RiemannCompactCoshQuantitativeQuarticBand
import Zeta23Bridge.LiteralWeilProjectiveStripConstant

/-!
# Support/L1 bound for the compact-cosh fourth-derivative Lipschitz constant

For
  K(P) = integral |P(u)| cosh(|u|) |u|^5,
a support radius and an L1 mass bound immediately give

  K(P) <= M cosh(L) L^5.

This deliberately coarse compiler is enough for the high-zero quartic strip
calculation; it keeps bump-specific bookkeeping out of the calculus layer.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveStripConstant

theorem compactCoshFourthLipschitzConstant_le_support_mass
    {P : ℝ -> ℝ} {L M : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hL : 0 <= L)
    (hsupp : ∀ u : ℝ, P u ≠ 0 -> |u| <= L)
    (hmass : taperMass P <= M) :
    compactCoshFourthLipschitzConstant P
      <= M * Real.cosh L * L^5 := by
  have hi :
      Integrable
        (fun u : ℝ => |P u| * Real.cosh |u| * |u|^5) :=
    compactCoshFourthLipschitzMajorant_integrable hP hPc
  have hmassI : Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  have hC : 0 <= Real.cosh L := (Real.cosh_pos L).le
  have hL5 : 0 <= L^5 := pow_nonneg hL _
  have hconst :
      Integrable
        (fun u : ℝ => (Real.cosh L * L^5) * |P u|) :=
    hmassI.const_mul (Real.cosh L * L^5)
  unfold compactCoshFourthLipschitzConstant
  calc
    (∫ u : ℝ, |P u| * Real.cosh |u| * |u|^5)
      <=
    ∫ u : ℝ, (Real.cosh L * L^5) * |P u| := by
      apply integral_mono hi hconst
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hu := hsupp u hzero
        have hcosh : Real.cosh |u| <= Real.cosh L := by
          rw [Real.cosh_le_cosh]
          rw [abs_of_nonneg (abs_nonneg u), abs_of_nonneg hL]
          exact hu
        have hpow : |u|^5 <= L^5 :=
          pow_le_pow_left₀ (abs_nonneg u) hu (by norm_num)
        have hPu : 0 <= |P u| := abs_nonneg _
        nlinarith [mul_nonneg hC hL5]
    _ =
      (Real.cosh L * L^5) * taperMass P := by
        rw [integral_const_mul]
        rfl
    _ <= (Real.cosh L * L^5) * M := by
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hC hL5)
    _ = M * Real.cosh L * L^5 := by ring

end Synthesis
