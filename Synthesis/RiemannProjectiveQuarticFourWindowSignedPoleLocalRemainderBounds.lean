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


/-!
## One same-object bound for the complete local joint remainder
-/

def QuarticFourSignedPolePair.localJointQuarticRemainderBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  |q|^4 *
      ((5/96 : ℝ) * W.signedProfileAbsMomentFour
        + W.targetStrength/6)
    +
  (alpha^2/2) *
      ((5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentSix)
    +
  (5/96 : ℝ) * |alpha|^4 * W.signedProfileAbsMomentFour

theorem QuarticFourSignedPolePair.localJointQuarticRemainderBound_nonneg
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.localJointQuarticRemainderBound alpha q := by
  unfold QuarticFourSignedPolePair.localJointQuarticRemainderBound
  have h4 := W.signedProfileAbsMomentFour_nonneg
  have h6 := W.signedProfileAbsMomentSix_nonneg
  have hS := W.targetStrength_pos.le
  positivity

theorem QuarticFourSignedPolePair.baseQuarticJetRemainder_abs_le
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.baseQuarticJetRemainder q|
      <=
    |q|^4 *
      ((5/96 : ℝ) * W.signedProfileAbsMomentFour
        + W.targetStrength/6) := by
  have hb :=
    W.signedNormalizedBaseKernel_abs_le_local_quartic hq
  have heq :
      W.baseQuarticJetRemainder q
        =
      W.signedNormalizedBaseKernel q
        + (W.targetStrength/6) * q^4 := by
    unfold QuarticFourSignedPolePair.baseQuarticJetRemainder
    rw [W.signedNormalizedBaseKernel_eq_compactCosine]
  rw [heq]
  calc
    |W.signedNormalizedBaseKernel q
        + (W.targetStrength/6) * q^4|
      <=
    |W.signedNormalizedBaseKernel q|
      + |(W.targetStrength/6) * q^4| :=
      abs_add _ _
    _ <=
    (5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentFour
      + (W.targetStrength/6) * |q|^4 := by
      gcongr
      rw [abs_mul, abs_pow,
        abs_of_nonneg (by positivity : 0 <= W.targetStrength/6)]
    _ =
    |q|^4 *
      ((5/96 : ℝ) * W.signedProfileAbsMomentFour
        + W.targetStrength/6) := by ring

theorem QuarticFourSignedPolePair.jointQuarticJetRemainder_abs_le
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.jointQuarticJetRemainder alpha q|
      <=
    W.localJointQuarticRemainderBound alpha q := by
  have hb := W.baseQuarticJetRemainder_abs_le hq
  have hqerr := W.horizontalQuadraticJetRemainder_abs_le hq
  have hh := W.signedHorizontalQuarticRemainder_abs_le ha
  unfold QuarticFourSignedPolePair.jointQuarticJetRemainder
  have ha2 : 0 <= alpha^2/2 := by positivity
  calc
    |W.baseQuarticJetRemainder q
      + (alpha^2/2) * W.horizontalQuadraticJetRemainder q
      + W.signedHorizontalQuarticRemainder alpha q|
      <=
    |W.baseQuarticJetRemainder q|
      + |(alpha^2/2) * W.horizontalQuadraticJetRemainder q|
      + |W.signedHorizontalQuarticRemainder alpha q| := by
        exact (abs_add _ _).trans
          (add_le_add (abs_add _ _) le_rfl)
    _ <=
    |q|^4 *
        ((5/96 : ℝ) * W.signedProfileAbsMomentFour
          + W.targetStrength/6)
      +
    (alpha^2/2) *
        ((5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentSix)
      +
    (5/96 : ℝ) * |alpha|^4 * W.signedProfileAbsMomentFour := by
        rw [abs_mul, abs_of_nonneg ha2]
        gcongr
    _ = W.localJointQuarticRemainderBound alpha q := by
      rfl


/-!
## Automatic local-radius transport for every mixed-cone zero
-/

theorem one_fifth_lt_quarticSignedPoleCanonicalLocalRadius :
    (1/5 : ℝ) < quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalLocalRadius
  have hpi : 0 < Real.pi + 1 := by positivity
  rw [lt_div_iff₀ hpi]
  nlinarith [Real.pi_lt_four]

theorem quarticSignedPoleLocalCone_alpha_abs_le_canonicalRadius
    {t eta : ℝ}
    (ht : 200 <= t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |heightOf rho / (t/16)|
      <= quarticSignedPoleCanonicalLocalRadius := by
  have hr : 0 < t/16 := by linarith
  have hrlo : (25/2 : ℝ) <= t/16 := by linarith
  have hstrip := zetaZero_height_abs_le_half rho
  have heta := one_fifth_lt_quarticSignedPoleCanonicalLocalRadius
  have hetaPos : 0 < quarticSignedPoleCanonicalLocalRadius := by
    exact quarticSignedPoleCanonicalLocalRadius_pos
  have hprod :
      (1/2 : ℝ)
        < quarticSignedPoleCanonicalLocalRadius * (t/16) := by
    have hmul :=
      mul_lt_mul_of_pos_right heta hr
    have hlo :
        (5/2 : ℝ) <= (1/5 : ℝ) * (t/16) := by
      nlinarith
    linarith
  rw [abs_div, abs_of_pos hr]
  rw [div_le_iff₀ hr]
  exact hstrip.trans_lt hprod |>.le

theorem quarticSignedPoleLocalCone_q_abs_le_canonicalRadius
    {t eta : ℝ}
    (ht : 200 <= t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |quarticSignedPoleNormalizedOrdinateOffset t rho|
      <= quarticSignedPoleCanonicalLocalRadius := by
  have hr : 0 < t/16 := by linarith
  have hrlo : (25/2 : ℝ) <= t/16 := by linarith
  have hdelta :=
    quarticSignedPoleLocalCone_abs_delta_le_three_halves hc
  have heta := one_fifth_lt_quarticSignedPoleCanonicalLocalRadius
  have hprod :
      (3/2 : ℝ)
        < quarticSignedPoleCanonicalLocalRadius * (t/16) := by
    have hmul :=
      mul_lt_mul_of_pos_right heta hr
    have hlo :
        (5/2 : ℝ) <= (1/5 : ℝ) * (t/16) := by
      nlinarith
    linarith
  unfold quarticSignedPoleNormalizedOrdinateOffset
  rw [abs_div, abs_of_pos hr]
  rw [div_le_iff₀ hr]
  exact hdelta.trans_lt hprod |>.le

/--
Every mixed-cone zero at t>=200 satisfies the complete local same-object
remainder estimate automatically.
-/
theorem QuarticFourSignedPolePair.jointQuarticJetRemainder_abs_le_of_localCone
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |W.jointQuarticJetRemainder
        (heightOf rho / (t/16))
        (quarticSignedPoleNormalizedOrdinateOffset t rho)|
      <=
    W.localJointQuarticRemainderBound
      (heightOf rho / (t/16))
      (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  exact W.jointQuarticJetRemainder_abs_le
    (quarticSignedPoleLocalCone_alpha_abs_le_canonicalRadius ht hc)
    (quarticSignedPoleLocalCone_q_abs_le_canonicalRadius ht hc)


/-!
## Physical literal remainder transport on the mixed cone
-/

theorem QuarticFourSignedPolePair.literalJointQuarticRemainder_abs_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    |W.literalJointQuarticRemainder rho|
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
    |W.jointQuarticJetRemainder
        (heightOf rho / (t/16))
        (quarticSignedPoleNormalizedOrdinateOffset t rho)| := by
  unfold QuarticFourSignedPolePair.literalJointQuarticRemainder
    quarticSignedPoleNormalizedOrdinateOffset
  dsimp
  have hm :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  have hr2 : 0 < (t/16)^2 := by positivity
  rw [abs_mul, abs_div, abs_of_nonneg hm, abs_of_pos hr2]

theorem QuarticFourSignedPolePair.literalJointQuarticRemainder_abs_le_of_localCone
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |W.literalJointQuarticRemainder rho|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
    W.localJointQuarticRemainderBound
      (heightOf rho / (t/16))
      (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  have htpos : 0 < t := by linarith
  rw [W.literalJointQuarticRemainder_abs_eq_normalized htpos]
  have hfac :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2 := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (W.jointQuarticJetRemainder_abs_le_of_localCone ht hc)
    hfac


/-!
## Fail-fast uniform cone envelope

For a cone zero we use only the fixed strip bounds
  |a| <= 1/2, |delta| <= 3/2
and t>=200.  The constants below are intentionally coarse: the purpose is to
expose the structural log(t) / a_target^4 comparison, not optimize factors.
-/

def QuarticFourSignedPolePair.literalConeEnvelopeConstant
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (9/16 : ℝ) * W.targetStrength
    +
  (81/16 : ℝ) *
    ((5/96 : ℝ) * W.signedProfileAbsMomentFour
      + W.targetStrength/6)
    +
  (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
    +
  (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour

theorem QuarticFourSignedPolePair.literalConeEnvelopeConstant_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.literalConeEnvelopeConstant := by
  unfold QuarticFourSignedPolePair.literalConeEnvelopeConstant
  have hS := W.targetStrength_pos.le
  have h4 := W.signedProfileAbsMomentFour_nonneg
  have h6 := W.signedProfileAbsMomentSix_nonneg
  positivity

theorem quarticSignedPoleLocalCone_height_abs_le_half
    {t eta : ℝ} {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |heightOf rho| <= (1/2 : ℝ) := by
  exact zetaZero_height_abs_le_half rho

theorem QuarticFourSignedPolePair.localJointQuarticRemainderBound_le_cone_over_r4
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    W.localJointQuarticRemainderBound
      (heightOf rho / (t/16))
      (quarticSignedPoleNormalizedOrdinateOffset t rho)
      <=
    (1/(t/16)^4) *
      (
        (81/16 : ℝ) *
          ((5/96 : ℝ) * W.signedProfileAbsMomentFour
            + W.targetStrength/6)
        +
        (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
        +
        (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour
      ) := by
  have hr : 1 <= t/16 := by linarith
  have hrpos : 0 < t/16 := by linarith
  have ha :=
    quarticSignedPoleLocalCone_height_abs_le_half hc
  have hd :=
    quarticSignedPoleLocalCone_abs_delta_le_three_halves hc
  have hq :
      |quarticSignedPoleNormalizedOrdinateOffset t rho|
        <= (3/2 : ℝ) / (t/16) := by
    unfold quarticSignedPoleNormalizedOrdinateOffset
    rw [abs_div, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hd hrpos.le
  have halpha :
      |heightOf rho / (t/16)|
        <= (1/2 : ℝ) / (t/16) := by
    rw [abs_div, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right ha hrpos.le
  have hq4 :
      |quarticSignedPoleNormalizedOrdinateOffset t rho|^4
        <= (81/16 : ℝ) / (t/16)^4 := by
    have hnon : 0 <= |quarticSignedPoleNormalizedOrdinateOffset t rho| :=
      abs_nonneg _
    have hpow := pow_le_pow_left₀ hnon hq 4
    norm_num at hpow ⊢
    simpa [div_pow] using hpow
  have ha2 :
      (heightOf rho / (t/16))^2
        <= (1/4 : ℝ) / (t/16)^2 := by
    have hnon : 0 <= |heightOf rho / (t/16)| := abs_nonneg _
    have hpow := pow_le_pow_left₀ hnon halpha 2
    rw [sq_abs] at hpow
    norm_num at hpow ⊢
    simpa [div_pow] using hpow
  have ha4 :
      |heightOf rho / (t/16)|^4
        <= (1/16 : ℝ) / (t/16)^4 := by
    have hnon : 0 <= |heightOf rho / (t/16)| := abs_nonneg _
    have hpow := pow_le_pow_left₀ hnon halpha 4
    norm_num at hpow ⊢
    simpa [div_pow] using hpow
  have hrInv : 1 / (t/16)^2 <= 1 := by
    rw [div_le_one (by positivity : 0 < (t/16)^2)]
    nlinarith [sq_nonneg (t/16 - 1)]
  unfold QuarticFourSignedPolePair.localJointQuarticRemainderBound
  have h4 := W.signedProfileAbsMomentFour_nonneg
  have h6 := W.signedProfileAbsMomentSix_nonneg
  have hS := W.targetStrength_pos.le
  have hA0 :
      0 <= (5/96 : ℝ) * W.signedProfileAbsMomentFour
        + W.targetStrength/6 := by positivity
  have hB0 :
      0 <= (5/96 : ℝ) * W.signedProfileAbsMomentSix := by positivity
  have hC0 :
      0 <= (5/96 : ℝ) * W.signedProfileAbsMomentFour := by positivity
  calc
    |quarticSignedPoleNormalizedOrdinateOffset t rho|^4 * 
        ((5/96 : ℝ) * W.signedProfileAbsMomentFour + W.targetStrength/6)
      +
      ((heightOf rho / (t/16))^2/2) *
        ((5/96 : ℝ) *
          |quarticSignedPoleNormalizedOrdinateOffset t rho|^4 *
          W.signedProfileAbsMomentSix)
      +
      (5/96 : ℝ) * |heightOf rho / (t/16)|^4 *
        W.signedProfileAbsMomentFour
      <=
    ((81/16 : ℝ) / (t/16)^4) * 
        ((5/96 : ℝ) * W.signedProfileAbsMomentFour + W.targetStrength/6)
      +
      (((1/4 : ℝ) / (t/16)^2)/2) *
        ((5/96 : ℝ) * ((81/16 : ℝ) / (t/16)^4) *
          W.signedProfileAbsMomentSix)
      +
      (5/96 : ℝ) * ((1/16 : ℝ) / (t/16)^4) *
        W.signedProfileAbsMomentFour := by
          gcongr
    _ <=
    (1/(t/16)^4) *
      (
        (81/16 : ℝ) *
          ((5/96 : ℝ) * W.signedProfileAbsMomentFour
            + W.targetStrength/6)
        +
        (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
        +
        (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour
      ) := by
        have hr4 : 0 < (t/16)^4 := by positivity
        have hmid :
            1 / (t/16)^6 <= 1 / (t/16)^4 := by
          have hp : (t/16)^4 <= (t/16)^6 := by
            nlinarith [sq_nonneg ((t/16)^2 - 1)]
          exact one_div_le_one_div_of_le hr4 hp
        field_simp [hrpos.ne']
        nlinarith [h4,h6,hS]

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_le_cone_over_r6
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    W.literalJointQuarticPolynomial rho
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * ((9/16 : ℝ) * W.targetStrength)
      / (t/16)^6 := by
  have ha := quarticSignedPoleLocalCone_height_abs_le_half hc
  have hd := quarticSignedPoleLocalCone_abs_delta_le_three_halves hc
  have hm :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  have hS := W.targetStrength_pos.le
  rw [W.literalJointQuarticPolynomial_eq_mixed_sub_ordinate
      (by linarith : 0 < t)]
  have ha2 : heightOf rho^2 <= (1/4 : ℝ) := by
    nlinarith [sq_nonneg (heightOf rho), sq_abs (heightOf rho)]
  have hd2 : ((rho : ℂ).im-t)^2 <= (9/4 : ℝ) := by
    nlinarith [sq_nonneg ((rho : ℂ).im-t), sq_abs ((rho : ℂ).im-t)]
  have hden : 0 < (t/16)^6 := by positivity
  have hmix :
      heightOf rho^2 * ((rho : ℂ).im-t)^2 <= (9/16 : ℝ) := by
    nlinarith [sq_nonneg (heightOf rho), sq_nonneg ((rho : ℂ).im-t)]
  have hneg :
      0 <=
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength * ((rho : ℂ).im-t)^4
        / (6 * (t/16)^6) := by positivity
  have hmain :
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength * heightOf rho^2
        * ((rho : ℂ).im-t)^2 / (t/16)^6
      <=
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * ((9/16 : ℝ) * W.targetStrength)
        / (t/16)^6 := by
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  linarith

theorem QuarticFourSignedPolePair.literalConeExactSource_le_envelope
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho)
    (hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm
        (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros))
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.literalConeEnvelopeConstant
      / (t/16)^6 := by
  have htpos : 0 < t := by linarith
  rw [W.signedLiteralPairSourceTerm_eq_literalQuarticJet
      htpos (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros))]
  have hp :=
    W.literalJointQuarticPolynomial_le_cone_over_r6 ht hc
  have hr0 :=
    W.literalJointQuarticRemainder_abs_le_of_localCone ht hc
  have hrBound :=
    W.localJointQuarticRemainderBound_le_cone_over_r4 ht hc
  have hm :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  have hr2 : 0 < (t/16)^2 := by positivity
  have hr4 : 0 < (t/16)^4 := by positivity
  have hrem :
      W.literalJointQuarticRemainder rho
      <=
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        *
      (
        (81/16 : ℝ) *
          ((5/96 : ℝ) * W.signedProfileAbsMomentFour
            + W.targetStrength/6)
        +
        (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
        +
        (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour
      )
      / (t/16)^6 := by
    have h1 := le_abs_self (W.literalJointQuarticRemainder rho)
    have hfac :
        0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2 := by
      positivity
    have h2 := mul_le_mul_of_nonneg_left hrBound hfac
    calc
      W.literalJointQuarticRemainder rho
        <= |W.literalJointQuarticRemainder rho| := h1
      _ <=
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
          *
        W.localJointQuarticRemainderBound
          (heightOf rho / (t/16))
          (quarticSignedPoleNormalizedOrdinateOffset t rho) := hr0
      _ <=
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
          *
        ((1/(t/16)^4) *
          (
            (81/16 : ℝ) *
              ((5/96 : ℝ) * W.signedProfileAbsMomentFour
                + W.targetStrength/6)
            +
            (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
            +
            (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour
          )) := h2
      _ =
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          *
        (
          (81/16 : ℝ) *
            ((5/96 : ℝ) * W.signedProfileAbsMomentFour
              + W.targetStrength/6)
          +
          (81/128 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentSix
          +
          (1/16 : ℝ) * (5/96 : ℝ) * W.signedProfileAbsMomentFour
        )
        / (t/16)^6 := by
          field_simp [hr2.ne', hr4.ne']
          ring
  unfold QuarticFourSignedPolePair.literalConeEnvelopeConstant
  linarith

end Synthesis

end Synthesis
