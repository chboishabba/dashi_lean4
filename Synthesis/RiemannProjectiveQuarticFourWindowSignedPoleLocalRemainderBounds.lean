import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative local remainder bounds for the joint quartic G3 kernel

This file starts the only Taylor work that is useful to the Clay-facing
cone/good/far decomposition.  The far carrier remains exact.

The canonical normalized local radius is

  eta0 = 1 / (pi+1).

The signed combined profile is supported in |u| <= pi+1, so |q| <= eta0
implies |q*u| <= 1 everywhere the profile is nonzero.

Mathlib's certified bound

  |cos z - (1-z^2/2)| <= (5/96)|z|^4

then gives an explicit fourth-order error for the horizontal quadratic
coefficient.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def quarticSignedPoleCanonicalLocalRadius : ℝ :=
  1 / (Real.pi + 1)

theorem quarticSignedPoleCanonicalLocalRadius_pos :
    0 < quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalLocalRadius
  positivity

theorem quarticSignedPoleCanonicalLocalRadius_lt_one :
    quarticSignedPoleCanonicalLocalRadius < 1 := by
  unfold quarticSignedPoleCanonicalLocalRadius
  rw [div_lt_one (by positivity : 0 < Real.pi + 1)]
  linarith [Real.pi_pos]

def QuarticFourSignedPolePair.signedProfileAbsMomentSix
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  compactProfileAbsMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) 6

theorem QuarticFourSignedPolePair.signedProfileAbsMomentSix_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.signedProfileAbsMomentSix := by
  unfold QuarticFourSignedPolePair.signedProfileAbsMomentSix
    compactProfileAbsMoment
  positivity

theorem QuarticFourSignedPolePair.abs_q_mul_u_le_one_of_local
    {t q u : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius)
    (hu :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t u ≠ 0) :
    |q*u| <= 1 := by
  have hus := W.combinedProfile_support_abs_le_pi_add_one u hu
  rw [abs_mul]
  unfold quarticSignedPoleCanonicalLocalRadius at hq
  have hpi : 0 < Real.pi + 1 := by positivity
  have hq' :
      |q| * (Real.pi + 1) <= 1 := by
    calc
      |q| * (Real.pi + 1)
        <= quarticSignedPoleCanonicalLocalRadius
          * (Real.pi + 1) :=
        mul_le_mul_of_nonneg_right hq hpi.le
      _ = 1 := by
        unfold quarticSignedPoleCanonicalLocalRadius
        field_simp [hpi.ne']
  exact (mul_le_mul_of_nonneg_left hus (abs_nonneg q)).trans hq'

theorem QuarticFourSignedPolePair.horizontalQuadraticKernel_referenceIntegral
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        * u^2
        * (1 - (q*u)^2/2)
      =
    2 * W.targetStrength * q^2 := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have h2 :
      Integrable (fun u : ℝ => P u * u^2) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have h4 :
      Integrable (fun u : ℝ => P u * u^4) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hM2 :
      ∫ u : ℝ, P u * u^2 = 0 := by
    change profileSecondMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have hM4 :
      ∫ u : ℝ, P u * u^4 = -4 * W.targetStrength := by
    change profileFourthMoment P = -4 * W.targetStrength
    rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
    unfold QuarticFourSignedPolePair.targetStrength
    ring
  rw [show
      (fun u : ℝ =>
        P u * u^2 * (1 - (q*u)^2/2))
      =
      fun u =>
        P u * u^2 - (q^2/2) * (P u * u^4) by
      funext u
      ring]
  rw [integral_sub h2 (h4.const_mul _),
      integral_const_mul, hM2, hM4]
  ring

theorem QuarticFourSignedPolePair.horizontalQuadraticJetRemainder_eq_integral
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.horizontalQuadraticJetRemainder q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        * u^2
        *
      (Real.cos (q*u) - (1 - (q*u)^2/2)) := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hcos :
      Integrable (fun u : ℝ => P u * u^2 * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have href :
      Integrable
        (fun u : ℝ => P u * u^2 * (1 - (q*u)^2/2)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  unfold QuarticFourSignedPolePair.horizontalQuadraticJetRemainder
  rw [W.signedHorizontalQuadraticKernel_eq_neg_D2]
  unfold compactCosineD2
  have hQ :
      - (∫ u : ℝ, -P u * Real.cos (q*u) * u^2)
        =
      ∫ u : ℝ, P u * u^2 * Real.cos (q*u) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring
  rw [hQ, ← W.horizontalQuadraticKernel_referenceIntegral (q:=q)]
  rw [← integral_sub hcos href]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

/--
Explicit local fourth-order error of the horizontal quadratic coefficient.
-/
theorem QuarticFourSignedPolePair.horizontalQuadraticJetRemainder_abs_le
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.horizontalQuadraticJetRemainder q|
      <=
    (5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentSix := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          P u * u^2
            * (Real.cos (q*u) - (1 - (q*u)^2/2))) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hmaj :
      Integrable
        (fun u : ℝ =>
          (5/96 : ℝ) * |q|^4 * (|P u| * |u|^6)) :=
    (compactProfile_absMoment_integrable hP hPc 6).const_mul
      ((5/96 : ℝ) * |q|^4)
  rw [W.horizontalQuadraticJetRemainder_eq_integral]
  calc
    |∫ u : ℝ,
      P u * u^2
        * (Real.cos (q*u) - (1 - (q*u)^2/2))|
      <=
    ∫ u : ℝ,
      |P u * u^2
        * (Real.cos (q*u) - (1 - (q*u)^2/2))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      (5/96 : ℝ) * |q|^4 * (|P u| * |u|^6) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hqu := W.abs_q_mul_u_le_one_of_local hq hzero
        have hc := Real.cos_bound hqu
        rw [abs_mul, abs_mul, abs_pow]
        have hqupow : |q*u|^4 = |q|^4 * |u|^4 := by
          rw [abs_mul, mul_pow]
        rw [hqupow] at hc
        nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ =
    (5/96 : ℝ) * |q|^4
      * compactProfileAbsMoment P 6 := by
      rw [integral_const_mul]
      rfl
    _ =
    (5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentSix := by
      rfl


/-!
## Direct quartic local bound for the base cosine channel

Because the signed combined profile has M0=M2=0, the same certified cosine
bound controls the exact base channel at quartic scale.  No sixth-order Taylor
remainder is needed for this debt estimate.
-/

def QuarticFourSignedPolePair.signedProfileAbsMomentFour
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  compactProfileAbsMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) 4

theorem QuarticFourSignedPolePair.signedProfileAbsMomentFour_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.signedProfileAbsMomentFour := by
  unfold QuarticFourSignedPolePair.signedProfileAbsMomentFour
    compactProfileAbsMoment
  positivity

theorem QuarticFourSignedPolePair.signedNormalizedBaseKernel_eq_cosineRemainder
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedBaseKernel q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        *
      (Real.cos (q*u) - (1 - (q*u)^2/2)) := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hcos :
      Integrable (fun u : ℝ => P u * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have href :
      Integrable
        (fun u : ℝ => P u * (1 - (q*u)^2/2)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hM0 :
      ∫ u : ℝ, P u = 0 := by
    change profileZerothMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos
  have hM2 :
      ∫ u : ℝ, P u * u^2 = 0 := by
    change profileSecondMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have href0 :
      ∫ u : ℝ, P u * (1 - (q*u)^2/2) = 0 := by
    rw [show
        (fun u : ℝ => P u * (1 - (q*u)^2/2))
        =
        fun u => P u - (q^2/2) * (P u * u^2) by
      funext u
      ring]
    have hPint :
        Integrable P :=
      hP.integrable_of_hasCompactSupport hPc
    have h2 :
        Integrable (fun u : ℝ => P u * u^2) :=
      Continuous.integrable_of_hasCompactSupport
        (by fun_prop) hPc.mul_right
    rw [integral_sub hPint (h2.const_mul _),
      integral_const_mul, hM0, hM2]
    ring
  rw [W.signedNormalizedBaseKernel_eq_compactCosine]
  unfold compactCosineTransform
  rw [← sub_zero (∫ u : ℝ, P u * Real.cos (q*u)), ← href0]
  rw [← integral_sub hcos href]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem QuarticFourSignedPolePair.signedNormalizedBaseKernel_abs_le_local_quartic
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.signedNormalizedBaseKernel q|
      <=
    (5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentFour := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          P u * (Real.cos (q*u) - (1 - (q*u)^2/2))) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hmaj :
      Integrable
        (fun u : ℝ =>
          (5/96 : ℝ) * |q|^4 * (|P u| * |u|^4)) :=
    (compactProfile_absMoment_integrable hP hPc 4).const_mul
      ((5/96 : ℝ) * |q|^4)
  rw [W.signedNormalizedBaseKernel_eq_cosineRemainder]
  calc
    |∫ u : ℝ,
      P u * (Real.cos (q*u) - (1 - (q*u)^2/2))|
      <=
    ∫ u : ℝ,
      |P u * (Real.cos (q*u) - (1 - (q*u)^2/2))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      (5/96 : ℝ) * |q|^4 * (|P u| * |u|^4) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hqu := W.abs_q_mul_u_le_one_of_local hq hzero
        have hc := Real.cos_bound hqu
        rw [abs_mul]
        have hqupow : |q*u|^4 = |q|^4 * |u|^4 := by
          rw [abs_mul, mul_pow]
        rw [hqupow] at hc
        nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ =
    (5/96 : ℝ) * |q|^4
      * compactProfileAbsMoment P 4 := by
      rw [integral_const_mul]
      rfl
    _ =
    (5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentFour := by
      rfl


/-!
## Certified quartic hyperbolic remainder
-/

open Finset

/--
Real-hyperbolic analogue of Mathlib's certified cosine fourth-order bound.
-/
theorem real_cosh_sub_one_sub_sq_half_abs_le
    {x : ℝ}
    (hx : |x| <= 1) :
    |Real.cosh x - 1 - x^2/2|
      <= |x|^4 * (5/96 : ℝ) := by
  calc
    |Real.cosh x - 1 - x^2/2|
      =
    |(Real.exp x
        - ∑ m ∈ Finset.range 4, x^m / m.factorial) / 2
      +
      (Real.exp (-x)
        - ∑ m ∈ Finset.range 4, (-x)^m / m.factorial) / 2| := by
        rw [Real.cosh_eq]
        simp [Finset.sum_range_succ, Nat.factorial]
        ring
    _ <=
      |Real.exp x
        - ∑ m ∈ Finset.range 4, x^m / m.factorial| / 2
      +
      |Real.exp (-x)
        - ∑ m ∈ Finset.range 4, (-x)^m / m.factorial| / 2 := by
        have h2 : (0:ℝ) < 2 := by norm_num
        calc
          |(Real.exp x
              - ∑ m ∈ Finset.range 4, x^m / m.factorial) / 2
            +
            (Real.exp (-x)
              - ∑ m ∈ Finset.range 4, (-x)^m / m.factorial) / 2|
            <=
          |(Real.exp x
              - ∑ m ∈ Finset.range 4, x^m / m.factorial) / 2|
            +
          |(Real.exp (-x)
              - ∑ m ∈ Finset.range 4, (-x)^m / m.factorial) / 2| :=
            abs_add _ _
          _ =
          |Real.exp x
              - ∑ m ∈ Finset.range 4, x^m / m.factorial| / 2
            +
          |Real.exp (-x)
              - ∑ m ∈ Finset.range 4, (-x)^m / m.factorial| / 2 := by
            rw [abs_div, abs_div, abs_of_pos h2]
    _ <=
      (|x|^4 * (5/96 : ℝ)) / 2
        + (|-x|^4 * (5/96 : ℝ)) / 2 := by
      gcongr
      · exact Real.exp_bound hx (by norm_num)
      · exact Real.exp_bound (by simpa [abs_neg] using hx) (by norm_num)
    _ = |x|^4 * (5/96 : ℝ) := by
      rw [abs_neg]
      ring

/--
The signed horizontal quartic remainder is literally the hyperbolic
fourth-order remainder integrated against the same combined profile.
-/
theorem QuarticFourSignedPolePair.signedHorizontalQuarticRemainder_eq_integral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedHorizontalQuarticRemainder alpha q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        * (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
        * Real.cos (q*u) := by
  let P1 :=
    quarticFourNormalizedProjectiveProfile
      W.R (1/2) W.muHalf
  let P2 :=
    quarticFourNormalizedProjectiveProfile
      W.R (2/3) W.muTwo
  let H : ℝ -> ℝ :=
    fun u =>
      (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
        * Real.cos (q*u)
  have h1 :
      Integrable (fun u : ℝ => P1 u * H u) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P1,H]; fun_prop)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right
  have h2 :
      Integrable (fun u : ℝ => P2 u * H u) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P2,H]; fun_prop)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right
  unfold QuarticFourSignedPolePair.signedHorizontalQuarticRemainder
    genericProjectiveHorizontalQuarticRemainder
    quarticFourSignedPoleCombinedProfile profileLinearCombination
    quarticFourNormalizedProjectiveProfile
  change
    W.poleTwo * (∫ u : ℝ, P1 u * H u)
      + (-W.poleHalf) * (∫ u : ℝ, P2 u * H u)
      =
    ∫ u : ℝ,
      (W.poleTwo * P1 u + (-W.poleHalf) * P2 u) * H u
  rw [show
      (fun u : ℝ =>
        (W.poleTwo * P1 u + (-W.poleHalf) * P2 u) * H u)
      =
      fun u =>
        W.poleTwo * (P1 u * H u)
          + (-W.poleHalf) * (P2 u * H u) by
      funext u
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]

/--
Explicit alpha^4 local bound for the exact signed horizontal remainder.
-/
theorem QuarticFourSignedPolePair.signedHorizontalQuarticRemainder_abs_le
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.signedHorizontalQuarticRemainder alpha q|
      <=
    (5/96 : ℝ) * |alpha|^4 * W.signedProfileAbsMomentFour := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          P u
            * (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
            * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hmaj :
      Integrable
        (fun u : ℝ =>
          (5/96 : ℝ) * |alpha|^4 * (|P u| * |u|^4)) :=
    (compactProfile_absMoment_integrable hP hPc 4).const_mul
      ((5/96 : ℝ) * |alpha|^4)
  rw [W.signedHorizontalQuarticRemainder_eq_integral]
  calc
    |∫ u : ℝ,
      P u * (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
        * Real.cos (q*u)|
      <=
    ∫ u : ℝ,
      |P u * (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
        * Real.cos (q*u)| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      (5/96 : ℝ) * |alpha|^4 * (|P u| * |u|^4) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hau := W.abs_q_mul_u_le_one_of_local
          (q:=alpha) (u:=u) ha hzero
        have hh :=
          real_cosh_sub_one_sub_sq_half_abs_le hau
        have hc := Real.abs_cos_le_one (q*u)
        rw [abs_mul, abs_mul]
        have haupow :
            |alpha*u|^4 = |alpha|^4 * |u|^4 := by
          rw [abs_mul, mul_pow]
        rw [haupow] at hh
        nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ =
    (5/96 : ℝ) * |alpha|^4
      * compactProfileAbsMoment P 4 := by
      rw [integral_const_mul]
      rfl
    _ =
    (5/96 : ℝ) * |alpha|^4
      * W.signedProfileAbsMomentFour := by
      rfl

end Synthesis
