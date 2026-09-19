import Synthesis.RiemannCenteredOffFarOnlyUpper
import Zeta23Bridge.FarShellCutoffTailBound
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A natural cutoff inside the canonical centered-sign window

For |t| >= 18 and support

    Lambda <= 9*pi/(4|t|),

choose

    J = floor(|t|/9).

Then

    1 <= J,
    J*Lambda <= pi/2,
    |t|/18 <= J.

Consequently the explicit far-shell bound admits the high-ordinate estimate

    farShellBound A |t| J
      <= 324 A log(|t|+4)/|t|
         + 72 A sqrt(18/|t|).

This is conservative but completely explicit.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def canonicalSignedWindowCutoff (t : ℝ) : ℕ :=
  ⌊|t| / 9⌋₊

theorem canonicalSignedWindowCutoff_one_le
    {t : ℝ} (ht : 18 <= |t|) :
    1 <= canonicalSignedWindowCutoff t := by
  unfold canonicalSignedWindowCutoff
  have h2 : (2 : ℝ) <= |t| / 9 := by linarith
  have hfloor : 2 <= ⌊|t| / 9⌋₊ := by
    rw [Nat.le_floor_iff (by positivity : (0:ℝ) <= |t| / 9)]
    exact h2
  omega

theorem canonicalSignedWindowCutoff_cast_le
    (t : ℝ) :
    (canonicalSignedWindowCutoff t : ℝ) <= |t| / 9 := by
  unfold canonicalSignedWindowCutoff
  exact Nat.floor_le (by positivity)

theorem canonicalSignedWindowCutoff_lower
    {t : ℝ} (ht : 18 <= |t|) :
    |t| / 18 <= (canonicalSignedWindowCutoff t : ℝ) := by
  unfold canonicalSignedWindowCutoff
  have hfloorUpper :
      |t| / 9 < (⌊|t| / 9⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (|t| / 9)
  have ht18 : 18 <= |t| := ht
  linarith

theorem canonicalSignedWindowCutoff_mul_support_le
    {t Lambda : ℝ}
    (ht : 18 <= |t|)
    (hLambda : 0 <= Lambda)
    (hsupp : Lambda <= 9 * Real.pi / (4 * |t|)) :
    (canonicalSignedWindowCutoff t : ℝ) * Lambda <= Real.pi / 2 := by
  have htpos : 0 < |t| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 18) ht
  have hJ := canonicalSignedWindowCutoff_cast_le t
  have hmul1 :
      (canonicalSignedWindowCutoff t : ℝ) * Lambda
        <= (|t| / 9) * Lambda :=
    mul_le_mul_of_nonneg_right hJ hLambda
  have hmul2 :
      (|t| / 9) * Lambda
        <= (|t| / 9) * (9 * Real.pi / (4 * |t|)) :=
    mul_le_mul_of_nonneg_left hsupp (by positivity)
  have hsimp :
      (|t| / 9) * (9 * Real.pi / (4 * |t|)) = Real.pi / 4 := by
    field_simp [ne_of_gt htpos]
    ring
  rw [hsimp] at hmul2
  nlinarith [Real.pi_pos, hmul1, hmul2]

theorem inv_cutoff_le_eighteen_div_abs
    {t : ℝ} (ht : 18 <= |t|) :
    1 / (canonicalSignedWindowCutoff t : ℝ)
      <= 18 / |t| := by
  have htpos : 0 < |t| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 18) ht
  have hJpos : 0 < (canonicalSignedWindowCutoff t : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt
      (canonicalSignedWindowCutoff_one_le ht)
  have hlower := canonicalSignedWindowCutoff_lower ht
  rw [div_le_iff₀ hJpos, div_eq_mul_inv]
  have hmul := mul_le_mul_of_nonneg_left hlower (18 / |t|) (by positivity)
  have hsimp : (18 / |t|) * (|t| / 18) = 1 := by
    field_simp [ne_of_gt htpos]
  nlinarith [hmul, hsimp]

theorem inv_sqrt_cutoff_le_sqrt_eighteen_div_abs
    {t : ℝ} (ht : 18 <= |t|) :
    1 / Real.sqrt (canonicalSignedWindowCutoff t : ℝ)
      <= Real.sqrt (18 / |t|) := by
  have htpos : 0 < |t| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 18) ht
  have hJpos : 0 < (canonicalSignedWindowCutoff t : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt
      (canonicalSignedWindowCutoff_one_le ht)
  have hInv := inv_cutoff_le_eighteen_div_abs ht
  have hleft :
      1 / Real.sqrt (canonicalSignedWindowCutoff t : ℝ)
        = Real.sqrt (1 / (canonicalSignedWindowCutoff t : ℝ)) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) <= 1),
      Real.sqrt_one]
  rw [hleft]
  exact Real.sqrt_le_sqrt hInv

theorem farShellBound_canonicalSignedWindowCutoff_le
    {A t : ℝ}
    (hA : 0 <= A)
    (ht : 18 <= |t|) :
    Zeta23Bridge.FarShellCutoffTailBound.farShellBound
        A |t| (canonicalSignedWindowCutoff t)
      <=
      324 * A * Real.log (|t| + 4) / |t|
        + 72 * A * Real.sqrt (18 / |t|) := by
  open Zeta23Bridge.FarShellCutoffTailBound
  rw [farShellBound_eq]
  have hlog : 0 <= Real.log (|t| + 4) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have h1 := inv_cutoff_le_eighteen_div_abs ht
  have h2 := inv_sqrt_cutoff_le_sqrt_eighteen_div_abs ht
  have hfirst :
      18 * A * Real.log (|t| + 4)
          / (canonicalSignedWindowCutoff t : ℝ)
        <= 324 * A * Real.log (|t| + 4) / |t| := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hm := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (mul_nonneg (by norm_num) hA) hlog)
    nlinarith
  have hsecond :
      72 * A / Real.sqrt (canonicalSignedWindowCutoff t : ℝ)
        <= 72 * A * Real.sqrt (18 / |t|) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h2
      (mul_nonneg (by norm_num) hA)
  linarith

end Synthesis
