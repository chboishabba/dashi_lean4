import Synthesis.RiemannNormalizedZeroCountingStieltjes
import Zeta23Bridge.LiteralWeilProjectiveStripConstant

/-!
# Quantitative horizontal-strip correction in normalized coordinates

After the exact split

  cosh(alpha v) = 1 + (cosh(alpha v)-1),

all horizontal dependence sits in the correction E_t(alpha,q).

For |x|<=1 we prove the elementary bound

  0 <= cosh x - 1 <= x^2.

The normalized centered profile is supported in |v|<9*pi/4.  For an actual
zeta zero, |heightOf rho|<=1/2; hence for t>=18,

  |(heightOf rho/t) v| <= 1

throughout the normalized support.

Therefore

  |E_t(alpha_rho,q)| <= 4 alpha_rho^2 M2_t

where

  M2_t = integral |H_t(v)| v^2 dv,

and consequently

  |E_t(alpha_rho,q)| <= M2_t / t^2.

After the outer Jacobian 1/t in the literal aggregate, the full horizontal
correction is bounded by

  M2_t / t^3 * (total multiplicity of the finite carrier).

Thus the genuinely difficult H2 aggregate is the one-dimensional q-counting
pair; horizontal strip variation is quantitatively lower order.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilProjectiveStripConstant
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def normalizedCenteredSecondMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ, |normalizedCenteredFixedProfile t v| * v ^ 2

def finiteZeroMultiplicity (F : Finset Zeros) : ℝ :=
  ∑ rho ∈ F, ((zetaZeroConfig).mult (rho : ℂ) : ℝ)

theorem normalizedInnerFixedProfile_support_upper
    {v : ℝ} (hv : normalizedInnerFixedProfile v ≠ 0) :
    |v| < 5 * Real.pi / 4 := by
  rw [normalizedInnerFixedProfile_eq_symBump] at hv
  unfold quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hv
  let R : ℝ := Real.pi / 4
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hp : scaledUnitBump Real.pi R v = 0
  · have hm : scaledUnitBump Real.pi R (-v) ≠ 0 := by
      intro hm
      apply hv
      simp [hp, hm]
    have hs := scaledUnitBump_support hR hm
    have hsL := (abs_lt.mp hs).1
    have hsR := (abs_lt.mp hs).2
    dsimp [R] at hsL hsR
    by_cases hv0 : 0 <= v
    · rw [abs_of_nonneg hv0]
      nlinarith [Real.pi_pos]
    · rw [abs_of_neg (lt_of_not_ge hv0)]
      nlinarith [Real.pi_pos]
  · have hs := scaledUnitBump_support hR hp
    have hsL := (abs_lt.mp hs).1
    have hsR := (abs_lt.mp hs).2
    dsimp [R] at hsL hsR
    by_cases hv0 : 0 <= v
    · rw [abs_of_nonneg hv0]
      nlinarith [Real.pi_pos]
    · rw [abs_of_neg (lt_of_not_ge hv0)]
      nlinarith [Real.pi_pos]

theorem normalizedOuterFixedProfile_support_upper
    {v : ℝ} (hv : normalizedOuterFixedProfile v ≠ 0) :
    |v| < 9 * Real.pi / 4 := by
  rw [normalizedOuterFixedProfile_eq_symBump] at hv
  unfold quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hv
  let R : ℝ := Real.pi / 4
  let c : ℝ := 2 * Real.pi
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hp : scaledUnitBump c R v = 0
  · have hm : scaledUnitBump c R (-v) ≠ 0 := by
      intro hm
      apply hv
      simp [hp, hm]
    have hs := scaledUnitBump_support hR hm
    have hsL := (abs_lt.mp hs).1
    have hsR := (abs_lt.mp hs).2
    dsimp [R, c] at hsL hsR
    by_cases hv0 : 0 <= v
    · rw [abs_of_nonneg hv0]
      nlinarith [Real.pi_pos]
    · rw [abs_of_neg (lt_of_not_ge hv0)]
      nlinarith [Real.pi_pos]
  · have hs := scaledUnitBump_support hR hp
    have hsL := (abs_lt.mp hs).1
    have hsR := (abs_lt.mp hs).2
    dsimp [R, c] at hsL hsR
    by_cases hv0 : 0 <= v
    · rw [abs_of_nonneg hv0]
      nlinarith [Real.pi_pos]
    · rw [abs_of_neg (lt_of_not_ge hv0)]
      nlinarith [Real.pi_pos]

theorem normalizedCenteredFixedProfile_support_upper
    {t v : ℝ} (hv : normalizedCenteredFixedProfile t v ≠ 0) :
    |v| < 9 * Real.pi / 4 := by
  unfold normalizedCenteredFixedProfile at hv
  have hbase : normalizedCanonicalFixedProfile t v ≠ 0 := by
    intro h
    apply hv
    simp [h]
  unfold normalizedCanonicalFixedProfile at hbase
  by_cases hi : normalizedInnerFixedProfile v = 0
  · have ho : normalizedOuterFixedProfile v ≠ 0 := by
      intro ho
      apply hbase
      simp [hi, ho]
    exact normalizedOuterFixedProfile_support_upper ho
  · have hin := normalizedInnerFixedProfile_support_upper hi
    nlinarith [Real.pi_pos]

theorem cosh_sub_one_nonneg (x : ℝ) :
    0 <= Real.cosh x - 1 := by
  linarith [Real.one_le_cosh x]

theorem cosh_sub_one_le_sq
    {x : ℝ} (hx : |x| <= 1) :
    Real.cosh x - 1 <= x ^ 2 := by
  have hcosh := Real.cosh_le_exp_half_sq x
  let y : ℝ := x ^ 2 / 2
  have hy0 : 0 <= y := by dsimp [y]; positivity
  have hx2 : x ^ 2 <= 1 := by
    nlinarith [sq_abs x]
  have hy1 : |y| <= 1 := by
    rw [abs_of_nonneg hy0]
    dsimp [y]
    nlinarith
  have hexp := Real.abs_exp_sub_one_sub_id_le hy1
  have hup : Real.exp y - 1 - y <= y ^ 2 :=
    le_trans (le_abs_self _) hexp
  have hy_sq : y ^ 2 <= y := by
    have : y <= 1 := le_trans (le_abs_self y) hy1
    nlinarith
  dsimp [y] at hcosh ⊢
  nlinarith

theorem normalizedCenteredSecondMoment_nonneg (t : ℝ) :
    0 <= normalizedCenteredSecondMoment t := by
  unfold normalizedCenteredSecondMoment
  positivity

theorem normalizedHorizontalCorrection_abs_le
    {t alpha q : ℝ}
    (hsmall :
      ∀ v, normalizedCenteredFixedProfile t v ≠ 0 ->
        |alpha * v| <= 1) :
    |normalizedCenteredHorizontalCorrection t alpha q|
      <= 4 * alpha ^ 2 * normalizedCenteredSecondMoment t := by
  unfold normalizedCenteredHorizontalCorrection
  have hHc := (normalizedCenteredFixedProfile_contDiff t).continuous
  have hHs := normalizedCenteredFixedProfile_compact t
  have hi :
      Integrable
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfile t v
            * (Real.cosh (alpha * v) - 1)
            * Real.cos (q * v)) :=
    integrable_normalizedCenteredHorizontalCorrection t alpha q
  have himom :
      Integrable
        (fun v : ℝ =>
          4 * alpha ^ 2 *
            (|normalizedCenteredFixedProfile t v| * v ^ 2)) := by
    have hbase :
        Integrable
          (fun v : ℝ =>
            |normalizedCenteredFixedProfile t v| * v ^ 2) := by
      exact (hHc.abs.mul (by fun_prop)).integrable_of_hasCompactSupport
        hHs.abs.mul_right
    exact hbase.const_mul (4 * alpha ^ 2)
  calc
    |∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v
        * (Real.cosh (alpha * v) - 1)
        * Real.cos (q * v)|
      <= ∫ v : ℝ,
        |4 * normalizedCenteredFixedProfile t v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)| :=
        abs_integral_le_integral_abs
    _ <= ∫ v : ℝ,
        4 * alpha ^ 2 *
          (|normalizedCenteredFixedProfile t v| * v ^ 2) := by
      apply integral_mono hi.abs himom
      intro v
      by_cases hzero : normalizedCenteredFixedProfile t v = 0
      · simp [hzero]
      · have hch0 := cosh_sub_one_nonneg (alpha * v)
        have hch := cosh_sub_one_le_sq (hsmall v hzero)
        have hcos := Real.abs_cos_le_one (q * v)
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) <= 4),
          abs_of_nonneg hch0]
        calc
          4 * |normalizedCenteredFixedProfile t v|
              * (Real.cosh (alpha * v) - 1)
              * |Real.cos (q * v)|
            <=
          4 * |normalizedCenteredFixedProfile t v|
              * (Real.cosh (alpha * v) - 1) := by
                gcongr
          _ <=
          4 * |normalizedCenteredFixedProfile t v|
              * (alpha * v) ^ 2 := by
                gcongr
          _ =
          4 * alpha ^ 2 *
              (|normalizedCenteredFixedProfile t v| * v ^ 2) := by
                ring
    _ = 4 * alpha ^ 2 * normalizedCenteredSecondMoment t := by
      rw [integral_const_mul]
      rfl

theorem normalized_actual_zero_small_horizontal
    {t : ℝ} (ht : 18 <= t) (rho : Zeros) :
    ∀ v, normalizedCenteredFixedProfile t v ≠ 0 ->
      |normalizedHorizontalHeight t rho * v| <= 1 := by
  intro v hv
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ha := abs_heightOf_le rho
  have hvU := normalizedCenteredFixedProfile_support_upper hv
  unfold normalizedHorizontalHeight
  rw [abs_mul, abs_div, abs_of_pos ht0]
  have hprod1 :
      |heightOf rho| * |v|
        <= |heightOf rho| * (9 * Real.pi / 4) := by
    exact mul_le_mul_of_nonneg_left hvU.le (abs_nonneg _)
  have hprod2 :
      |heightOf rho| * (9 * Real.pi / 4)
        <= (1 / 2 : ℝ) * (9 * Real.pi / 4) := by
    exact mul_le_mul_of_nonneg_right ha (by positivity)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hsmallnum : |heightOf rho| * |v| <= t := by
    calc
      |heightOf rho| * |v|
        <= (1 / 2 : ℝ) * (9 * Real.pi / 4) :=
          le_trans hprod1 hprod2
      _ < 18 := by nlinarith
      _ <= t := ht
  exact (div_le_one ht0).2 hsmallnum

theorem normalizedHorizontalCorrection_actual_zero_le
    {t : ℝ} (ht : 18 <= t) (rho : Zeros) :
    |normalizedCenteredHorizontalCorrection t
        (normalizedHorizontalHeight t rho)
        (normalizedGap t rho)|
      <= normalizedCenteredSecondMoment t / t ^ 2 := by
  have h0 := normalizedHorizontalCorrection_abs_le
    (t := t)
    (alpha := normalizedHorizontalHeight t rho)
    (q := normalizedGap t rho)
    (normalized_actual_zero_small_horizontal ht rho)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ha := abs_heightOf_le rho
  have ha2 :
      (normalizedHorizontalHeight t rho) ^ 2 <= 1 / (4 * t ^ 2) := by
    unfold normalizedHorizontalHeight
    have hs : (heightOf rho) ^ 2 <= (1 / 2 : ℝ) ^ 2 := by
      nlinarith [sq_abs (heightOf rho)]
    have ht2 : 0 < t ^ 2 := by positivity
    calc
      (heightOf rho / t) ^ 2
          = (heightOf rho) ^ 2 / t ^ 2 := by ring
      _ <= ((1 / 2 : ℝ) ^ 2) / t ^ 2 :=
        (div_le_div_iff_of_pos_right ht2).2 hs
      _ = 1 / (4 * t ^ 2) := by ring
  have hm := normalizedCenteredSecondMoment_nonneg t
  calc
    |normalizedCenteredHorizontalCorrection t
        (normalizedHorizontalHeight t rho)
        (normalizedGap t rho)|
      <= 4 * (normalizedHorizontalHeight t rho) ^ 2
          * normalizedCenteredSecondMoment t := h0
    _ <= normalizedCenteredSecondMoment t / t ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right ha2 hm
      calc
        4 * (normalizedHorizontalHeight t rho) ^ 2
            * normalizedCenteredSecondMoment t
          <= 4 * (1 / (4 * t ^ 2))
            * normalizedCenteredSecondMoment t := by
              nlinarith
        _ = normalizedCenteredSecondMoment t / t ^ 2 := by ring

theorem finiteZeroMultiplicity_nonneg (F : Finset Zeros) :
    0 <= finiteZeroMultiplicity F := by
  unfold finiteZeroMultiplicity
  positivity

theorem normalizedHorizontalAtomicAggregate_abs_le
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    |normalizedHorizontalAtomicAggregate t F|
      <=
    (normalizedCenteredSecondMoment t / t ^ 2)
      * finiteZeroMultiplicity F := by
  classical
  unfold normalizedHorizontalAtomicAggregate finiteZeroMultiplicity
  have htri :
      |∑ rho ∈ F,
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * normalizedCenteredHorizontalCorrection t
              (normalizedHorizontalHeight t rho)
              (normalizedGap t rho)|
      <=
      ∑ rho ∈ F,
        |((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * normalizedCenteredHorizontalCorrection t
              (normalizedHorizontalHeight t rho)
              (normalizedGap t rho)| := by
    exact Finset.abs_sum_le_sum_abs _ _
  calc
    |∑ rho ∈ F,
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * normalizedCenteredHorizontalCorrection t
            (normalizedHorizontalHeight t rho)
            (normalizedGap t rho)|
      <=
      ∑ rho ∈ F,
        |((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * normalizedCenteredHorizontalCorrection t
              (normalizedHorizontalHeight t rho)
              (normalizedGap t rho)| := htri
    _ <=
      ∑ rho ∈ F,
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * (normalizedCenteredSecondMoment t / t ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [abs_mul, abs_of_nonneg (by positivity :
        (0:ℝ) <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ))]
      exact mul_le_mul_of_nonneg_left
        (normalizedHorizontalCorrection_actual_zero_le ht rho)
        (by positivity)
    _ =
      (normalizedCenteredSecondMoment t / t ^ 2)
        * ∑ rho ∈ F, ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring

end Synthesis
