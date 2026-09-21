import Synthesis.RiemannQuantitativeSymmetricBumpMass
import Synthesis.RiemannQuantitativeScaledBumpPositivity
import Zeta23Bridge.PoleQuotientComplementMargin

/-!
# Uniform mixing bound for the quantitative two-window taper

Use the same scaled unit bump in both windows of the canonical even-channel
construction:

  outer center c1 = 2*pi/t,
  inner center c2 = pi/t,
  radius R = pi/(4t),
  sample radius r = t/16.

For t >= 18 the outer pole weight is uniformly >= 1/2 on the outer bump.
The inner pole-weight magnitude is uniformly bounded by cosh(5*pi/144).
Since the two raw bump masses are identical, the pole-cancelling mixing
coefficient admits a t-independent upper bound.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.PoleQuotientComplementMargin
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def quantitativeTaperR (t : ℝ) : ℝ := Real.pi / (4 * t)
def quantitativeTaperOuterCenter (t : ℝ) : ℝ := 2 * Real.pi / t
def quantitativeTaperInnerCenter (t : ℝ) : ℝ := Real.pi / t
def quantitativeSampleRadius (t : ℝ) : ℝ := t / 16

def quantitativeOuterBump (t : ℝ) : ℝ → ℝ :=
  quantitativeSymBump (quantitativeTaperOuterCenter t) (quantitativeTaperR t)

def quantitativeInnerBump (t : ℝ) : ℝ → ℝ :=
  quantitativeSymBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t)

def quantitativeMixUpper : ℝ :=
  2 * Real.cosh (5 * Real.pi / 144)

theorem unitBumpMass0_pos : 0 < unitBumpMass0 := by
  unfold unitBumpMass0 taperMass
  have hpos := scaledUnitBump_positive_integral
    (c := (0:ℝ)) (R := (1:ℝ)) (by norm_num)
    (w := fun _ => (1:ℝ)) (by fun_prop)
    (by intro u hu; norm_num)
  simpa [scaledUnitBump, unitBump, unitContDiffBump,
    abs_of_nonneg (unitBump_nonneg _)] using hpos

theorem cos_ge_sqrtTwoHalf_of_near_twoPi
    {x : ℝ}
    (hx : |x - 2 * Real.pi| <= Real.pi / 4) :
    Real.sqrt 2 / 2 <= Real.cos x := by
  have hp := Real.pi_pos
  have hy0 : 0 <= |x - 2 * Real.pi| := abs_nonneg _
  have hypi : |x - 2 * Real.pi| <= Real.pi := by
    linarith
  have hmono :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      hy0 (by linarith : Real.pi / 4 <= Real.pi) hx
  have hcosabs :
      Real.cos |x - 2 * Real.pi|
        = Real.cos (x - 2 * Real.pi) := Real.cos_abs _
  have hperiod :
      Real.cos (x - 2 * Real.pi) = Real.cos x := by
    rw [Real.cos_sub_int_mul_two_pi]
    norm_num
  rw [Real.cos_pi_div_four, hcosabs, hperiod] at hmono
  exact hmono

theorem outerPoleWeight_ge_half
    {t u : ℝ} (ht : 0 < t)
    (hu : |u - quantitativeTaperOuterCenter t|
      < quantitativeTaperR t) :
    (1 / 2 : ℝ) <=
      Real.cosh (u / 2) * Real.cos (t * u)
        * Real.cos (quantitativeSampleRadius t * u) := by
  have hp := Real.pi_pos
  unfold quantitativeTaperOuterCenter quantitativeTaperR at hu
  rw [abs_lt] at hu
  have htuLow : 7 * Real.pi / 4 < t * u := by
    have h := mul_lt_mul_of_pos_left hu.1 ht
    field_simp at h ⊢
    nlinarith
  have htuHigh : t * u < 9 * Real.pi / 4 := by
    have h := mul_lt_mul_of_pos_left hu.2 ht
    field_simp at h ⊢
    nlinarith
  have hnear2pi : |t * u - 2 * Real.pi| <= Real.pi / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hct :
      Real.sqrt 2 / 2 <= Real.cos (t * u) :=
    cos_ge_sqrtTwoHalf_of_near_twoPi hnear2pi
  have hsampleWindow :
      2 * quantitativeSampleRadius t * |u| < Real.pi / 2 := by
    unfold quantitativeSampleRadius
    have huPos : 0 < u := by
      have : 0 < 7 * Real.pi / (4*t) := by positivity
      linarith
    rw [abs_of_pos huPos]
    have htu : t * u < 9 * Real.pi / 4 := htuHigh
    nlinarith
  have hcr :
      Real.sqrt 2 / 2
        <= Real.cos (quantitativeSampleRadius t * u) :=
    cos_ge_of_window
      (by unfold quantitativeSampleRadius; positivity)
      hsampleWindow
  have hch : 1 <= Real.cosh (u/2) := Real.one_le_cosh _
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt0 : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hct.le hcr.le]

theorem innerPoleWeight_abs_le
    {t u : ℝ} (ht : 18 <= t)
    (hu : |u - quantitativeTaperInnerCenter t|
      < quantitativeTaperR t) :
    |Real.cosh (u / 2) * Real.cos (t*u)
        * Real.cos (quantitativeSampleRadius t*u)|
      <= Real.cosh (5 * Real.pi / 144) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativeTaperInnerCenter quantitativeTaperR at hu
  rw [abs_lt] at hu
  have huPos : 0 < u := by
    have hlow : 3 * Real.pi / (4*t) < u := by
      have h := hu.1
      field_simp at h ⊢
      nlinarith [Real.pi_pos]
    positivity
  have huHigh : u < 5 * Real.pi / (4*t) := by
    have h := hu.2
    field_simp at h ⊢
    nlinarith
  have hu2 : |u/2| <= 5 * Real.pi / 144 := by
    rw [abs_of_pos (by positivity : 0 < u/2)]
    have htinv : 1/t <= 1/18 := one_div_le_one_div_of_le (by norm_num) ht
    have hbound : u/2 < 5 * Real.pi / (8*t) := by linarith
    have hpi := Real.pi_pos
    have : 5 * Real.pi / (8*t) <= 5 * Real.pi / 144 := by
      have hm := mul_le_mul_of_nonneg_left htinv
        (by positivity : 0 <= 5*Real.pi/8)
      simpa [div_eq_mul_inv, mul_assoc] using hm
    linarith
  have hcosh :
      Real.cosh (u/2) <= Real.cosh (5 * Real.pi / 144) := by
    rw [Real.cosh_le_cosh]
    simpa [abs_of_nonneg (by positivity : 0 <= 5 * Real.pi / 144)] using hu2
  have hct : |Real.cos (t*u)| <= 1 := Real.abs_cos_le_one _
  have hcr :
      |Real.cos (quantitativeSampleRadius t*u)| <= 1 :=
    Real.abs_cos_le_one _
  rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
  have hnonneg : 0 <= Real.cosh (5 * Real.pi / 144) := (Real.cosh_pos _).le
  nlinarith [mul_nonneg (abs_nonneg (Real.cos (t*u)))
    (abs_nonneg (Real.cos (quantitativeSampleRadius t*u)))]

/--
Uniform ratio bound.  It is stated abstractly in terms of the two pole responses
so it can be reused by the quantitative taper constructor.
-/
theorem quantitativeMixingRatio_le
    {t Pouter Pinner : ℝ}
    (ht : 18 <= t)
    (hOuter :
      (quantitativeTaperR t * unitBumpMass0)
        <= Pouter)
    (hInner :
      -Pinner <=
        2 * Real.cosh (5 * Real.pi / 144)
          * quantitativeTaperR t * unitBumpMass0)
    (hPouter : 0 < Pouter)
    (hPinner : Pinner < 0) :
    -Pinner / Pouter <= quantitativeMixUpper := by
  have hR : 0 < quantitativeTaperR t := by
    unfold quantitativeTaperR
    positivity
  have hM : 0 < unitBumpMass0 := unitBumpMass0_pos
  have hden : 0 < quantitativeTaperR t * unitBumpMass0 :=
    mul_pos hR hM
  have hnum :
      -Pinner <= quantitativeMixUpper *
        (quantitativeTaperR t * unitBumpMass0) := by
    simpa [quantitativeMixUpper, mul_assoc] using hInner
  have hratio :
      -Pinner / Pouter
        <= (-Pinner) / (quantitativeTaperR t * unitBumpMass0) := by
    exact div_le_div_of_nonneg_left
      (by linarith) hden hOuter
  have hratio2 :
      (-Pinner) / (quantitativeTaperR t * unitBumpMass0)
        <= quantitativeMixUpper := by
    rw [div_le_iff₀ hden]
    exact hnum
  exact le_trans hratio hratio2

end Synthesis
