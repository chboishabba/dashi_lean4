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
## Sixth-order scalar Taylor bounds
-/

theorem complex_cos_sub_quartic_abs_le_sixth
    {x : ℂ}
    (hx : ‖x‖ <= 1) :
    ‖Complex.cos x - (1 - x^2/2 + x^4/24)‖
      <= ‖x‖^6 * (7/4320 : ℝ) := by
  calc
    ‖Complex.cos x - (1 - x^2/2 + x^4/24)‖
      =
    ‖(Complex.exp (-x * Complex.I)
        - ∑ m ∈ Finset.range 6,
            (-x * Complex.I)^m / m.factorial) / 2
      +
      (Complex.exp (x * Complex.I)
        - ∑ m ∈ Finset.range 6,
            (x * Complex.I)^m / m.factorial) / 2‖ := by
        simp [Complex.cos, Finset.sum_range_succ, Nat.factorial]
        grind [Complex.I_sq, two_ne_zero]
    _ <=
      ‖Complex.exp (-x * Complex.I)
        - ∑ m ∈ Finset.range 6,
            (-x * Complex.I)^m / m.factorial‖ / 2
      +
      ‖Complex.exp (x * Complex.I)
        - ∑ m ∈ Finset.range 6,
            (x * Complex.I)^m / m.factorial‖ / 2 := by
        grw [norm_add_le]
        simp
    _ <=
      ‖-x * Complex.I‖^6
          * ((Nat.succ 6 : ℝ)
            * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2
      +
      ‖x * Complex.I‖^6
          * ((Nat.succ 6 : ℝ)
            * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
        grw [Complex.exp_bound (by simpa) (by norm_num),
          Complex.exp_bound (by simpa) (by norm_num)]
    _ <= ‖x‖^6 * (7/4320 : ℝ) := by
        norm_num

theorem real_cos_sub_quartic_abs_le_sixth
    {x : ℝ}
    (hx : |x| <= 1) :
    |Real.cos x - (1 - x^2/2 + x^4/24)|
      <= |x|^6 * (7/4320 : ℝ) := by
  have h :=
    complex_cos_sub_quartic_abs_le_sixth
      (x := (x : ℂ)) (by simpa using hx)
  simpa [Real.norm_eq_abs] using h

theorem real_cosh_sub_quartic_abs_le_sixth
    {x : ℝ}
    (hx : |x| <= 1) :
    |Real.cosh x - 1 - x^2/2 - x^4/24|
      <= |x|^6 * (7/4320 : ℝ) := by
  calc
    |Real.cosh x - 1 - x^2/2 - x^4/24|
      =
    |(Real.exp x
        - ∑ m ∈ Finset.range 6, x^m / m.factorial) / 2
      +
      (Real.exp (-x)
        - ∑ m ∈ Finset.range 6, (-x)^m / m.factorial) / 2| := by
        rw [Real.cosh_eq]
        simp [Finset.sum_range_succ, Nat.factorial]
        ring
    _ <=
      |Real.exp x
        - ∑ m ∈ Finset.range 6, x^m / m.factorial| / 2
      +
      |Real.exp (-x)
        - ∑ m ∈ Finset.range 6, (-x)^m / m.factorial| / 2 := by
        have h2 : (0:ℝ) < 2 := by norm_num
        calc
          |(Real.exp x
              - ∑ m ∈ Finset.range 6, x^m / m.factorial) / 2
            +
            (Real.exp (-x)
              - ∑ m ∈ Finset.range 6, (-x)^m / m.factorial) / 2|
            <=
          |(Real.exp x
              - ∑ m ∈ Finset.range 6, x^m / m.factorial) / 2|
            +
          |(Real.exp (-x)
              - ∑ m ∈ Finset.range 6, (-x)^m / m.factorial) / 2| :=
            abs_add _ _
          _ =
          |Real.exp x
              - ∑ m ∈ Finset.range 6, x^m / m.factorial| / 2
            +
          |Real.exp (-x)
              - ∑ m ∈ Finset.range 6, (-x)^m / m.factorial| / 2 := by
            rw [abs_div, abs_div, abs_of_pos h2]
    _ <=
      (|x|^6 * (7/4320 : ℝ)) / 2
        + (|-x|^6 * (7/4320 : ℝ)) / 2 := by
      gcongr
      · exact Real.exp_bound hx (by norm_num)
      · exact Real.exp_bound
          (by simpa [abs_neg] using hx) (by norm_num)
    _ = |x|^6 * (7/4320 : ℝ) := by
      rw [abs_neg]
      ring



/-!
## Genuine sixth-order remainder for the circular/base channel
-/

theorem QuarticFourSignedPolePair.baseQuarticJetRemainder_eq_sixthCosineRemainder
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.baseQuarticJetRemainder q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        *
      (Real.cos (q*u)
        - (1 - (q*u)^2/2 + (q*u)^4/24)) := by
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
        (fun u : ℝ =>
          P u * (1 - (q*u)^2/2 + (q*u)^4/24)) :=
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
  have hM4 :
      ∫ u : ℝ, P u * u^4 = -4 * W.targetStrength := by
    change profileFourthMoment P = -4 * W.targetStrength
    simpa [QuarticFourSignedPolePair.targetStrength] using
      quarticFourSignedPoleCombinedProfile_fourth
        (muHalf:=W.muHalf) (muTwo:=W.muTwo)
        (t:=t) W.Rpos
  have hrefValue :
      ∫ u : ℝ,
        P u * (1 - (q*u)^2/2 + (q*u)^4/24)
        =
      -(W.targetStrength/6) * q^4 := by
    rw [show
        (fun u : ℝ =>
          P u * (1 - (q*u)^2/2 + (q*u)^4/24))
        =
        fun u =>
          (P u - (q^2/2) * (P u * u^2))
            + (q^4/24) * (P u * u^4) by
      funext u
      ring]
    have hPint : Integrable P :=
      hP.integrable_of_hasCompactSupport hPc
    have h2 :
        Integrable (fun u : ℝ => P u * u^2) :=
      Continuous.integrable_of_hasCompactSupport
        (by fun_prop) hPc.mul_right
    have h4 :
        Integrable (fun u : ℝ => P u * u^4) :=
      Continuous.integrable_of_hasCompactSupport
        (by fun_prop) hPc.mul_right
    rw [integral_add
          (hPint.sub (h2.const_mul _))
          (h4.const_mul _),
        integral_sub hPint (h2.const_mul _),
        integral_const_mul, integral_const_mul,
        hM0,hM2,hM4]
    ring
  unfold QuarticFourSignedPolePair.baseQuarticJetRemainder
  rw [W.signedNormalizedBaseKernel_eq_compactCosine]
  unfold compactCosineTransform
  rw [show
      (W.targetStrength/6) * q^4
        = - (∫ u : ℝ,
          P u * (1 - (q*u)^2/2 + (q*u)^4/24)) by
      rw [hrefValue]
      ring]
  rw [← integral_sub hcos href]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem QuarticFourSignedPolePair.baseQuarticJetRemainder_abs_le_sixth
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.baseQuarticJetRemainder q|
      <=
    (7/4320 : ℝ) * |q|^6
      * W.signedProfileAbsMomentSix := by
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
            * (Real.cos (q*u)
              - (1 - (q*u)^2/2 + (q*u)^4/24))) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hmaj :
      Integrable
        (fun u : ℝ =>
          (7/4320 : ℝ) * |q|^6 * (|P u| * |u|^6)) :=
    (compactProfile_absMoment_integrable hP hPc 6).const_mul
      ((7/4320 : ℝ) * |q|^6)
  rw [W.baseQuarticJetRemainder_eq_sixthCosineRemainder]
  calc
    |∫ u : ℝ,
      P u
        * (Real.cos (q*u)
          - (1 - (q*u)^2/2 + (q*u)^4/24))|
      <=
    ∫ u : ℝ,
      |P u
        * (Real.cos (q*u)
          - (1 - (q*u)^2/2 + (q*u)^4/24))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      (7/4320 : ℝ) * |q|^6 * (|P u| * |u|^6) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hqu := W.abs_q_mul_u_le_one_of_local hq hzero
        have hc :=
          real_cos_sub_quartic_abs_le_sixth hqu
        rw [abs_mul]
        have hqupow :
            |q*u|^6 = |q|^6 * |u|^6 := by
          rw [abs_mul, mul_pow]
        rw [hqupow] at hc
        nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ =
    (7/4320 : ℝ) * |q|^6
      * compactProfileAbsMoment P 6 := by
      rw [integral_const_mul]
      rfl
    _ =
    (7/4320 : ℝ) * |q|^6
      * W.signedProfileAbsMomentSix := by
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
## Centered sixth-order hyperbolic remainder
-/

def QuarticFourSignedPolePair.horizontalCenteredQuarticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.signedHorizontalQuarticRemainder alpha q
    + (W.targetStrength/6) * alpha^4

theorem QuarticFourSignedPolePair.horizontalCenteredQuarticRemainder_eq_integral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.horizontalCenteredQuarticRemainder alpha q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        *
      ((Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
          * Real.cos (q*u)
        - (alpha*u)^4/24) := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hM4 :
      ∫ u : ℝ, P u * u^4 = -4 * W.targetStrength := by
    change profileFourthMoment P = -4 * W.targetStrength
    simpa [QuarticFourSignedPolePair.targetStrength] using
      quarticFourSignedPoleCombinedProfile_fourth
        (muHalf:=W.muHalf) (muTwo:=W.muTwo)
        (t:=t) W.Rpos
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hmain :
      Integrable
        (fun u : ℝ =>
          P u
            * (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
            * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have h4 :
      Integrable (fun u : ℝ => P u * u^4) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  unfold QuarticFourSignedPolePair.horizontalCenteredQuarticRemainder
  rw [W.signedHorizontalQuarticRemainder_eq_integral]
  have hquartic :
      (W.targetStrength/6) * alpha^4
        =
      - ∫ u : ℝ, P u * ((alpha*u)^4/24) := by
    rw [show
        (fun u : ℝ => P u * ((alpha*u)^4/24))
        =
        fun u => (alpha^4/24) * (P u * u^4) by
      funext u
      ring,
      integral_const_mul,hM4]
    ring
  rw [hquartic, ← integral_sub hmain (by
    simpa [show
      (fun u : ℝ => P u * ((alpha*u)^4/24))
      =
      fun u => (alpha^4/24) * (P u * u^4) by
        funext u
        ring] using h4.const_mul (alpha^4/24))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem QuarticFourSignedPolePair.horizontalCenteredQuarticRemainder_abs_le_sixth
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.horizontalCenteredQuarticRemainder alpha q|
      <=
    ((7/4320 : ℝ) * |alpha|^6
      + (1/48 : ℝ) * |alpha|^4 * |q|^2)
      * W.signedProfileAbsMomentSix := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          P u *
            ((Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
                * Real.cos (q*u)
              - (alpha*u)^4/24)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hmaj :
      Integrable
        (fun u : ℝ =>
          ((7/4320 : ℝ) * |alpha|^6
            + (1/48 : ℝ) * |alpha|^4 * |q|^2)
            * (|P u| * |u|^6)) :=
    (compactProfile_absMoment_integrable hP hPc 6).const_mul _
  rw [W.horizontalCenteredQuarticRemainder_eq_integral]
  calc
    |∫ u : ℝ,
      P u *
        ((Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
            * Real.cos (q*u)
          - (alpha*u)^4/24)|
      <=
    ∫ u : ℝ,
      |P u *
        ((Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
            * Real.cos (q*u)
          - (alpha*u)^4/24)| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      ((7/4320 : ℝ) * |alpha|^6
        + (1/48 : ℝ) * |alpha|^4 * |q|^2)
        * (|P u| * |u|^6) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hau :=
          W.abs_q_mul_u_le_one_of_local
            (q:=alpha) (u:=u) ha hzero
        have hqu :=
          W.abs_q_mul_u_le_one_of_local
            (q:=q) (u:=u) hq hzero
        have hh :=
          real_cosh_sub_quartic_abs_le_sixth hau
        have hc :=
          Zeta23Bridge.LiteralWeilProjectiveTaper.abs_cos_sub_one_le
            (q*u)
        have hcos : |Real.cos (q*u)| <= 1 :=
          Real.abs_cos_le_one _
        have halpha6 :
            |alpha*u|^6 = |alpha|^6 * |u|^6 := by
          rw [abs_mul, mul_pow]
        have halpha4 :
            |alpha*u|^4 = |alpha|^4 * |u|^4 := by
          rw [abs_mul, mul_pow]
        have hq2 :
            |q*u|^2 = |q|^2 * |u|^2 := by
          rw [abs_mul, mul_pow]
        rw [halpha6] at hh
        rw [hq2] at hc
        have hsplit :
            (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2)
                * Real.cos (q*u)
              - (alpha*u)^4/24
            =
            (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2
                - (alpha*u)^4/24)
              * Real.cos (q*u)
            +
            ((alpha*u)^4/24)
              * (Real.cos (q*u)-1) := by
          ring
        rw [abs_mul, hsplit]
        have htri :=
          abs_add
            ((Real.cosh (alpha*u) - 1 - (alpha*u)^2/2
                - (alpha*u)^4/24)
              * Real.cos (q*u))
            (((alpha*u)^4/24) * (Real.cos (q*u)-1))
        rw [abs_mul, abs_mul] at htri
        have hA :
            |Real.cosh (alpha*u) - 1 - (alpha*u)^2/2
                - (alpha*u)^4/24|
              * |Real.cos (q*u)|
            <=
            (7/4320 : ℝ) * |alpha|^6 * |u|^6 := by
          nlinarith [abs_nonneg
            (Real.cosh (alpha*u) - 1 - (alpha*u)^2/2
              - (alpha*u)^4/24)]
        have hB :
            |(alpha*u)^4/24|
              * |Real.cos (q*u)-1|
            <=
            (1/48 : ℝ) * |alpha|^4 * |q|^2 * |u|^6 := by
          rw [abs_div, abs_pow,
            abs_of_pos (by norm_num : (0:ℝ) < 24),
            halpha4]
          nlinarith [abs_nonneg u]
        nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ =
    ((7/4320 : ℝ) * |alpha|^6
      + (1/48 : ℝ) * |alpha|^4 * |q|^2)
      * compactProfileAbsMoment P 6 := by
      rw [integral_const_mul]
      rfl
    _ =
    ((7/4320 : ℝ) * |alpha|^6
      + (1/48 : ℝ) * |alpha|^4 * |q|^2)
      * W.signedProfileAbsMomentSix := by
      rfl



/-!
## Sixth-order remainder for the complete bivariate quartic jet
-/

def QuarticFourSignedPolePair.completeJointSixthRemainderBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  ((7/4320 : ℝ) * (|q|^6 + |alpha|^6)
    + (5/192 : ℝ) * alpha^2 * |q|^4
    + (1/48 : ℝ) * |alpha|^4 * |q|^2)
    * W.signedProfileAbsMomentSix

theorem QuarticFourSignedPolePair.completeJointSixthRemainderBound_nonneg
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.completeJointSixthRemainderBound alpha q := by
  unfold QuarticFourSignedPolePair.completeJointSixthRemainderBound
  have h6 := W.signedProfileAbsMomentSix_nonneg
  positivity

theorem QuarticFourSignedPolePair.completeJointQuarticRemainder_eq_components
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointQuarticRemainder alpha q
      =
    W.baseQuarticJetRemainder q
      + (alpha^2/2) * W.horizontalQuadraticJetRemainder q
      + W.horizontalCenteredQuarticRemainder alpha q := by
  unfold QuarticFourSignedPolePair.completeJointQuarticRemainder
    QuarticFourSignedPolePair.jointQuarticJetRemainder
    QuarticFourSignedPolePair.horizontalCenteredQuarticRemainder
  ring

theorem QuarticFourSignedPolePair.completeJointQuarticRemainder_abs_le_sixth
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.completeJointQuarticRemainder alpha q|
      <=
    W.completeJointSixthRemainderBound alpha q := by
  have hb :=
    W.baseQuarticJetRemainder_abs_le_sixth hq
  have hqerr :=
    W.horizontalQuadraticJetRemainder_abs_le hq
  have hh :=
    W.horizontalCenteredQuarticRemainder_abs_le_sixth ha hq
  rw [W.completeJointQuarticRemainder_eq_components]
  have ha2 : 0 <= alpha^2/2 := by positivity
  calc
    |W.baseQuarticJetRemainder q
      + (alpha^2/2) * W.horizontalQuadraticJetRemainder q
      + W.horizontalCenteredQuarticRemainder alpha q|
      <=
    |W.baseQuarticJetRemainder q|
      + |(alpha^2/2) * W.horizontalQuadraticJetRemainder q|
      + |W.horizontalCenteredQuarticRemainder alpha q| := by
        exact (abs_add _ _).trans
          (add_le_add (abs_add _ _) le_rfl)
    _ <=
    (7/4320 : ℝ) * |q|^6 * W.signedProfileAbsMomentSix
      +
    (alpha^2/2)
      * ((5/96 : ℝ) * |q|^4 * W.signedProfileAbsMomentSix)
      +
    ((7/4320 : ℝ) * |alpha|^6
      + (1/48 : ℝ) * |alpha|^4 * |q|^2)
      * W.signedProfileAbsMomentSix := by
        rw [abs_mul, abs_of_nonneg ha2]
        gcongr
    _ =
    W.completeJointSixthRemainderBound alpha q := by
      unfold QuarticFourSignedPolePair.completeJointSixthRemainderBound
      ring


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


/-!
## Fail-fast weighted cone multiplicity compiler
-/

def QuarticFourSignedPolePair.literalConeMultiplicityAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℕ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalCone t eta rho then
      zetaZeroConfig.mult (rho : ℂ)
    else
      0

theorem QuarticFourSignedPolePair.literalConeDebtAt_le_envelope_mul_multiplicity
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (W.literalConeMultiplicityAt eta n : ℝ) := by
  classical
  unfold QuarticFourSignedPolePair.literalConeDebtAt
    QuarticFourSignedPolePair.literalConeMultiplicityAt
  rw [Nat.cast_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hsrc :=
        W.literalConeExactSource_le_envelope
          ht hc hoff
      have hC := W.literalConeEnvelopeConstant_nonneg
      have hr6 : 0 < (t/16)^6 := by positivity
      have hR :
          0 <=
            W.literalConeEnvelopeConstant / (t/16)^6
              * (zetaZeroConfig.mult (rho : ℂ) : ℝ) := by
        positivity
      simp [hc,
        QuarticFourSignedPolePair.literalOffOrdSource,
        hoff]
      apply max_le
      · simpa [mul_comm, mul_left_comm, mul_assoc,
          div_eq_mul_inv] using hsrc
      · exact hR
    · simp [hc,
        QuarticFourSignedPolePair.literalOffOrdSource,
        hoff]
  · simp [hc]

def quarticSignedPoleConeComplexSet
    (t eta : ℝ) : Set ℂ :=
  {z : ℂ |
    ∃ hz : z ∈ zetaZeroConfig.carrier,
      quarticSignedPoleLocalCone t eta (⟨z,hz⟩ : Zeros)}

theorem quarticSignedPoleConeComplexSet_subset_fixedWindow
    {t eta : ℝ} :
    quarticSignedPoleConeComplexSet t eta
      ⊆
    zetaZeroConfig.window
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
  intro z hz
  rcases hz with ⟨hzCarrier,hcone⟩
  have hw :=
    quarticSignedPoleLocalCone_mem_fixed_window hcone
  exact ⟨hzCarrier,hw.1,hw.2⟩

theorem QuarticFourSignedPolePair.literalConeMultiplicityAt_le_fixedWindowN
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeMultiplicityAt eta n
      <=
    zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
  classical
  let F : Finset Zeros :=
    (centeredZeroFinset t n).filter
      (quarticSignedPoleLocalCone t eta)
  let s : Set ℂ :=
    (fun rho : Zeros => (rho : ℂ)) '' (↑F : Set Zeros)
  have hsWindow :
      s ⊆
        zetaZeroConfig.window
          (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
    intro z hz
    rcases hz with ⟨rho,hrho,rfl⟩
    have hcone :
        quarticSignedPoleLocalCone t eta rho := by
      have := (Finset.mem_filter.mp hrho).2
      exact this
    exact quarticSignedPoleConeComplexSet_subset_fixedWindow
      ⟨rho.2,hcone⟩
  have hmono :=
    zetaZeroConfig.finsum_mult_mono
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ))
      hsWindow subset_rfl
  have hsFinite :
      s.Finite := by
    exact Set.Finite.image F.finite_toSet _
  have hsum :
      W.literalConeMultiplicityAt eta n
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z := by
    unfold QuarticFourSignedPolePair.literalConeMultiplicityAt
    change
      (∑ rho ∈ centeredZeroFinset t n,
        if quarticSignedPoleLocalCone t eta rho then
          zetaZeroConfig.mult (rho : ℂ) else 0)
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [← Finset.sum_filter]
    change
      (∑ rho ∈ F, zetaZeroConfig.mult (rho : ℂ))
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [finsum_mem_eq_finite_toFinset_sum _ hsFinite]
    have himage :
        hsFinite.toFinset
          =
        F.image (fun rho : Zeros => (rho : ℂ)) := by
      ext z
      simp [s]
    rw [himage, Finset.sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [hsum]
  exact hmono

theorem QuarticFourSignedPolePair.literalConeDebtAt_le_fixedWindowN
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := by
  have hdebt :=
    W.literalConeDebtAt_le_envelope_mul_multiplicity
      ht n
  have hmult :=
    W.literalConeMultiplicityAt_le_fixedWindowN
      (eta:=eta) n
  have hC : 0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  exact hdebt.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmult) hC)


/--
Unconditional finite cone-debt bound at the correct physical t^-6 scale.

The witness-dependent constant is deliberately left explicit.  The theorem is
intended as a fail-fast scaling diagnostic, not a constant-optimization result.
-/
theorem exists_quarticFourSignedPole_literalConeDebtAt_le_log_over_r6 :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t eta : ℝ},
        200 <= t ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ n : ℕ,
          W.literalConeDebtAt eta n
            <=
          3 * A0 * W.literalConeEnvelopeConstant
            * Real.log (t + 5)
            / (t/16)^6 := by
  obtain ⟨A0,hA0,hcount⟩ :=
    exists_quarticSignedPole_fixedConeWindow_zeroCount_bound
  refine ⟨A0,hA0,?_⟩
  intro t eta ht W n
  have hdebt :=
    W.literalConeDebtAt_le_fixedWindowN
      (eta:=eta) ht n
  have hN := hcount ht
  have hC :
      0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hN hC
  calc
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := hdebt
    _ <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (3 * A0 * Real.log (t+5)) := hmul
    _ =
    3 * A0 * W.literalConeEnvelopeConstant
      * Real.log (t+5) / (t/16)^6 := by ring

/--
Canonical coefficient appearing after the common r^-6 factor is cancelled
against any target lower bound of the form c*S(W)*a^4/r^6.
-/
def QuarticFourSignedPolePair.coneLogCoefficient
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A0 : ℝ) : ℝ :=
  3 * A0 * W.literalConeEnvelopeConstant * Real.log (t+5)

theorem QuarticFourSignedPolePair.coneDebt_le_coneLogCoefficient_over_r6
    {t eta A0 : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hA0 :
      (zetaZeroConfig.N
        (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
        <= 3 * A0 * Real.log (t+5))
    (hA0nonneg : 0 <= A0) :
    W.literalConeDebtAt eta n
      <=
    W.coneLogCoefficient A0 / (t/16)^6 := by
  have hdebt :=
    W.literalConeDebtAt_le_fixedWindowN
      (eta:=eta) ht n
  have hC :
      0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hA0 hC
  unfold QuarticFourSignedPolePair.coneLogCoefficient
  calc
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := hdebt
    _ <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (3 * A0 * Real.log (t+5)) := hmul
    _ =
    (3 * A0 * W.literalConeEnvelopeConstant * Real.log (t+5))
      / (t/16)^6 := by ring


/-!
## Fail-fast target-scaling diagnostic

The absolute cone estimate has the correct r^-6 scale.  What it does not
supply is a quartic floor in the target horizontal displacement a.

The elementary lemma below is deliberately not a statement about existence of
zeta zeros at arbitrary horizontal coordinates.  It only records that the
strip hypothesis 0<|a|<=1/2, by itself, cannot imply a uniform positive lower
bound for a^4.
-/

theorem exists_punctured_half_with_quartic_below
    {B : ℝ} (hB : 0 < B) :
    ∃ a : ℝ,
      0 < |a| ∧
      |a| <= (1/2 : ℝ) ∧
      a^4 < B := by
  let a : ℝ := min (1/4 : ℝ) (B/8)
  have haPos : 0 < a := by
    dsimp [a]
    exact lt_min (by norm_num) (by positivity)
  have haQuarter : a <= (1/4 : ℝ) := by
    dsimp [a]
    exact min_le_left _ _
  have haB : a <= B/8 := by
    dsimp [a]
    exact min_le_right _ _
  have haOne : a <= 1 := by linarith
  have haNonneg : 0 <= a := haPos.le
  have ha2 : a^2 <= a := by
    nlinarith [mul_nonneg haNonneg (sub_nonneg.mpr haOne)]
  have ha2One : a^2 <= 1 := ha2.trans haOne
  have ha4 : a^4 <= a^2 := by
    have hnon2 : 0 <= a^2 := sq_nonneg a
    have hprod :=
      mul_nonneg hnon2 (sub_nonneg.mpr ha2One)
    nlinarith [show a^4 = (a^2)^2 by ring]
  refine ⟨a,?_,?_,?_⟩
  · simpa [abs_of_pos haPos]
  · rw [abs_of_pos haPos]
    linarith
  · have : a^4 <= a := ha4.trans ha2
    linarith

def QuarticFourSignedPolePair.absoluteConeTargetCoefficientCondition
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A0 c a : ℝ) : Prop :=
  W.coneLogCoefficient A0
    < c * W.targetStrength * a^4

/--
If a future target theorem supplies
  target >= c*S(W)*a^4/r^6,
then the absolute cone estimate is paid exactly by the scalar coefficient
condition above.  This theorem intentionally leaves that target lower bound
as an explicit hypothesis because the current quantitative target compiler
only proves positivity.
-/
theorem QuarticFourSignedPolePair.literalConeDebtAt_lt_target_of_quartic_floor
    {t eta A0 c a target : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hcount :
      (zetaZeroConfig.N
        (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
        <= 3 * A0 * Real.log (t+5))
    (hA0 : 0 <= A0)
    (hcoef : W.absoluteConeTargetCoefficientCondition A0 c a)
    (htarget :
      c * W.targetStrength * a^4 / (t/16)^6 <= target) :
    W.literalConeDebtAt eta n < target := by
  have hdebt :=
    W.coneDebt_le_coneLogCoefficient_over_r6
      ht n hcount hA0
  have hr6 : 0 < (t/16)^6 := by positivity
  have hcoefScaled :
      W.coneLogCoefficient A0 / (t/16)^6
        <
      c * W.targetStrength * a^4 / (t/16)^6 := by
    exact div_lt_div_of_pos_right hcoef hr6
  exact lt_of_le_of_lt hdebt
    (hcoefScaled.trans_le htarget)




/-!
## Physical r^-8 transport of the complete sixth-order remainder
-/

def QuarticFourSignedPolePair.literalCompleteSixthPhysicalPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  (7/4320 : ℝ)
      * (|((sigma : ℂ).im-t)|^6 + |heightOf sigma|^6)
    +
  (5/192 : ℝ)
      * heightOf sigma^2 * |((sigma : ℂ).im-t)|^4
    +
  (1/48 : ℝ)
      * |heightOf sigma|^4 * |((sigma : ℂ).im-t)|^2

def QuarticFourSignedPolePair.literalCompleteSixthRemainderBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * W.signedProfileAbsMomentSix
    * W.literalCompleteSixthPhysicalPolynomial sigma
    / (t/16)^8

theorem QuarticFourSignedPolePair.literalCompleteSixthPhysicalPolynomial_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    0 <= W.literalCompleteSixthPhysicalPolynomial sigma := by
  unfold QuarticFourSignedPolePair.literalCompleteSixthPhysicalPolynomial
  positivity

theorem QuarticFourSignedPolePair.literalCompleteSixthRemainderBound_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    0 <= W.literalCompleteSixthRemainderBound sigma := by
  unfold QuarticFourSignedPolePair.literalCompleteSixthRemainderBound
  have h6 := W.signedProfileAbsMomentSix_nonneg
  positivity

theorem QuarticFourSignedPolePair.completeJointSixthRemainderBound_physical_rescale
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.completeJointSixthRemainderBound
        (heightOf sigma/(t/16))
        (((sigma : ℂ).im-t)/(t/16))
      =
    W.signedProfileAbsMomentSix
      * W.literalCompleteSixthPhysicalPolynomial sigma
      / (t/16)^6 := by
  unfold QuarticFourSignedPolePair.completeJointSixthRemainderBound
    QuarticFourSignedPolePair.literalCompleteSixthPhysicalPolynomial
  have hr : 0 < t/16 := by positivity
  rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hr]
  field_simp [hr.ne']
  ring

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticRemainder_abs_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    |W.literalCompleteJointQuarticRemainder sigma|
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
      *
    |W.completeJointQuarticRemainder
        (heightOf sigma/(t/16))
        (((sigma : ℂ).im-t)/(t/16))| := by
  unfold QuarticFourSignedPolePair.literalCompleteJointQuarticRemainder
  dsimp
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hr2 : 0 < (t/16)^2 := by positivity
  rw [abs_mul, abs_div, abs_of_nonneg hm, abs_of_pos hr2]

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticRemainder_abs_le
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (ha :
      |heightOf sigma/(t/16)|
        <= quarticSignedPoleCanonicalLocalRadius)
    (hq :
      |((sigma : ℂ).im-t)/(t/16)|
        <= quarticSignedPoleCanonicalLocalRadius) :
    |W.literalCompleteJointQuarticRemainder sigma|
      <=
    W.literalCompleteSixthRemainderBound sigma := by
  rw [W.literalCompleteJointQuarticRemainder_abs_eq_normalized ht]
  have hnorm :=
    W.completeJointQuarticRemainder_abs_le_sixth ha hq
  have hfac :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2 := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hnorm hfac
  rw [W.completeJointSixthRemainderBound_physical_rescale ht] at hscaled
  unfold QuarticFourSignedPolePair.literalCompleteSixthRemainderBound
  have hr : 0 < t/16 := by positivity
  calc
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
        *
      |W.completeJointQuarticRemainder
          (heightOf sigma/(t/16))
          (((sigma : ℂ).im-t)/(t/16))|
      <=
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
        *
      (W.signedProfileAbsMomentSix
        * W.literalCompleteSixthPhysicalPolynomial sigma
        / (t/16)^6) := hscaled
    _ =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * W.signedProfileAbsMomentSix
      * W.literalCompleteSixthPhysicalPolynomial sigma
      / (t/16)^8 := by
        field_simp [hr.ne']
        ring



/-!
## Local fourth-harmonic normal form

Use the complete quartic jet on the whole canonical local carrier.  The far
carrier remains exact.  Same-ordinate zeros are excluded exactly as in the
literal pair source.
-/

theorem quarticSignedPole_normalizedHeight_abs_le_canonicalRadius
    {t : ℝ}
    (ht : 200 <= t)
    (rho : Zeros) :
    |heightOf rho / (t/16)|
      <= quarticSignedPoleCanonicalLocalRadius := by
  have hr : 0 < t/16 := by linarith
  have hstrip := zetaZero_height_abs_le_half rho
  have heta := one_fifth_lt_quarticSignedPoleCanonicalLocalRadius
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

def QuarticFourSignedPolePair.literalLocalExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleLocal t eta rho then
    W.literalOffOrdSource rho
  else
    0

def QuarticFourSignedPolePair.literalLocalCompletePolynomialTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ := by
  classical
  exact if quarticSignedPoleLocal t eta rho then
    if h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
      W.literalCompleteJointQuarticPolynomial rho
    else
      0
  else
    0

def QuarticFourSignedPolePair.literalLocalCompleteRemainderTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ := by
  classical
  exact if quarticSignedPoleLocal t eta rho then
    if h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
      W.literalCompleteJointQuarticRemainder rho
    else
      0
  else
    0

def QuarticFourSignedPolePair.literalLocalExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalLocalExactTerm eta rho

def QuarticFourSignedPolePair.literalLocalFourthHarmonicAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalLocalCompletePolynomialTerm eta rho

def QuarticFourSignedPolePair.literalLocalCompleteRemainderAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalLocalCompleteRemainderTerm eta rho

def QuarticFourSignedPolePair.literalLocalSixthDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
        W.literalCompleteSixthRemainderBound rho
      else
        0
    else
      0

theorem QuarticFourSignedPolePair.literalOffOrdSource_eq_local_add_far
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalOffOrdSource rho
      =
    W.literalLocalExactTerm eta rho
      + W.literalFarExactTerm eta rho := by
  by_cases hl : quarticSignedPoleLocal t eta rho
  · have hnf : ¬ quarticSignedPoleFar t eta rho := by
      intro hf
      linarith [hl,hf]
    simp [QuarticFourSignedPolePair.literalLocalExactTerm,
      QuarticFourSignedPolePair.literalFarExactTerm,hl,hnf]
  · have hf : quarticSignedPoleFar t eta rho := by
      exact lt_of_not_ge hl
    simp [QuarticFourSignedPolePair.literalLocalExactTerm,
      QuarticFourSignedPolePair.literalFarExactTerm,hl,hf]

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_eq_local_add_far
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      =
    W.literalLocalExactAt eta n
      + W.literalFarExactAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalOffOrdExactAt
    QuarticFourSignedPolePair.literalLocalExactAt
    QuarticFourSignedPolePair.literalFarExactAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact W.literalOffOrdSource_eq_local_add_far rho

theorem QuarticFourSignedPolePair.literalLocalExactTerm_eq_completeJet
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalLocalExactTerm eta rho
      =
    W.literalLocalCompletePolynomialTerm eta rho
      + W.literalLocalCompleteRemainderTerm eta rho := by
  classical
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have h :=
        W.signedLiteralPairSourceTerm_eq_literalCompleteQuarticJet
          ht (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros))
      simp [QuarticFourSignedPolePair.literalLocalExactTerm,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalLocalCompletePolynomialTerm,
        QuarticFourSignedPolePair.literalLocalCompleteRemainderTerm,
        hl,hoff] at h ⊢
      exact h
    · simp [QuarticFourSignedPolePair.literalLocalExactTerm,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalLocalCompletePolynomialTerm,
        QuarticFourSignedPolePair.literalLocalCompleteRemainderTerm,
        hl,hoff]
  · simp [QuarticFourSignedPolePair.literalLocalExactTerm,
      QuarticFourSignedPolePair.literalLocalCompletePolynomialTerm,
      QuarticFourSignedPolePair.literalLocalCompleteRemainderTerm,hl]

theorem QuarticFourSignedPolePair.literalLocalExactAt_eq_fourthHarmonic_add_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalExactAt eta n
      =
    W.literalLocalFourthHarmonicAt eta n
      + W.literalLocalCompleteRemainderAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalExactAt
    QuarticFourSignedPolePair.literalLocalFourthHarmonicAt
    QuarticFourSignedPolePair.literalLocalCompleteRemainderAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact W.literalLocalExactTerm_eq_completeJet ht rho

theorem QuarticFourSignedPolePair.literalLocalCompleteRemainderAt_le_sixthDebt
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalCompleteRemainderAt
        quarticSignedPoleCanonicalLocalRadius n
      <=
    W.literalLocalSixthDebtAt
        quarticSignedPoleCanonicalLocalRadius n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalCompleteRemainderAt
    QuarticFourSignedPolePair.literalLocalCompleteRemainderTerm
    QuarticFourSignedPolePair.literalLocalSixthDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl :
      quarticSignedPoleLocal
        t quarticSignedPoleCanonicalLocalRadius rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have ha :=
        quarticSignedPole_normalizedHeight_abs_le_canonicalRadius
          ht rho
      have hq : |((rho : ℂ).im-t)/(t/16)|
          <= quarticSignedPoleCanonicalLocalRadius := hl
      have hb :=
        W.literalCompleteJointQuarticRemainder_abs_le
          (by linarith) rho ha hq
      simp [hl,hoff]
      exact le_trans (le_abs_self _) hb
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_fourthHarmonic_add_sixthDebt_add_far
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <=
    W.literalLocalFourthHarmonicAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalLocalSixthDebtAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalFarExactAt
        quarticSignedPoleCanonicalLocalRadius n := by
  rw [W.literalOffOrdExactAt_eq_local_add_far
      (eta:=quarticSignedPoleCanonicalLocalRadius)]
  rw [W.literalLocalExactAt_eq_fourthHarmonic_add_remainder
      (eta:=quarticSignedPoleCanonicalLocalRadius)
      (by linarith)]
  have hr :=
    W.literalLocalCompleteRemainderAt_le_sixthDebt
      ht n
  linarith

def quarticSignedPolePhysicalFourthPhaseReal
    (t : ℝ) (sigma : Zeros) : ℝ :=
  heightOf sigma^4
    - 6 * heightOf sigma^2 * ((sigma : ℂ).im-t)^2
    + ((sigma : ℂ).im-t)^4

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial_eq_phase
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalCompleteJointQuarticPolynomial sigma
      =
    - (((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * W.targetStrength
        * quarticSignedPolePhysicalFourthPhaseReal t sigma)
      / (6 * (t/16)^6) := by
  unfold QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial
    quarticSignedPolePhysicalFourthPhaseReal
  field_simp [show t/16 ≠ 0 by positivity]
  ring



/-!
## Local fourth-harmonic moment of the actual zero cloud

The complete quartic jet is exactly a fourth angular harmonic.  Package the
remaining local zeta-specific information as a multiplicity-weighted moment of
the physical phase

  Re (a + i*delta)^4
    = a^4 - 6*a^2*delta^2 + delta^4.

No Taylor carrier is summed outside the canonical local region.
-/

def QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * quarticSignedPolePhysicalFourthPhaseReal t rho
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalFourthFavorableMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * max (quarticSignedPolePhysicalFourthPhaseReal t rho) 0
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalFourthAdverseMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * max (-quarticSignedPolePhysicalFourthPhaseReal t rho) 0
        else
          0
      else
        0

theorem quarticSignedPolePhysicalFourthPhaseReal_eq_radial_sub_mixed
    (t : ℝ) (rho : Zeros) :
    quarticSignedPolePhysicalFourthPhaseReal t rho
      =
    (heightOf rho^2 + ((rho : ℂ).im-t)^2)^2
      - 8 * heightOf rho^2 * ((rho : ℂ).im-t)^2 := by
  unfold quarticSignedPolePhysicalFourthPhaseReal
  ring

theorem QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt_eq_favorable_sub_adverse
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthPhaseMomentAt eta n
      =
    W.literalLocalFourthFavorableMassAt eta n
      - W.literalLocalFourthAdverseMassAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
    QuarticFourSignedPolePair.literalLocalFourthFavorableMassAt
    QuarticFourSignedPolePair.literalLocalFourthAdverseMassAt
  rw [Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl,hoff]
      have hmax :
          quarticSignedPolePhysicalFourthPhaseReal t rho
            =
          max (quarticSignedPolePhysicalFourthPhaseReal t rho) 0
            - max (-quarticSignedPolePhysicalFourthPhaseReal t rho) 0 := by
        by_cases hp :
            0 <= quarticSignedPolePhysicalFourthPhaseReal t rho
        · simp [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]
        · have hn :
              quarticSignedPolePhysicalFourthPhaseReal t rho < 0 :=
            lt_of_not_ge hp
          have hnp :
              0 <= -quarticSignedPolePhysicalFourthPhaseReal t rho := by
            linarith
          simp [max_eq_right (le_of_lt hn),
            max_eq_left hnp]
      rw [hmax]
      ring
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalFourthHarmonicAt_eq_phaseMoment
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthHarmonicAt eta n
      =
    - W.targetStrength
      / (6 * (t/16)^6)
      * W.literalLocalFourthPhaseMomentAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthHarmonicAt
    QuarticFourSignedPolePair.literalLocalCompletePolynomialTerm
    QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
  rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl,hoff]
      rw [W.literalCompleteJointQuarticPolynomial_eq_phase ht]
      ring
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalFourthHarmonicAt_eq_adverse_sub_favorable
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthHarmonicAt eta n
      =
    W.targetStrength
      / (6 * (t/16)^6)
      *
      (W.literalLocalFourthAdverseMassAt eta n
        - W.literalLocalFourthFavorableMassAt eta n) := by
  rw [W.literalLocalFourthHarmonicAt_eq_phaseMoment ht]
  rw [W.literalLocalFourthPhaseMomentAt_eq_favorable_sub_adverse]
  ring

theorem QuarticFourSignedPolePair.literalLocalFourthFavorableMassAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalLocalFourthFavorableMassAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthFavorableMassAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hl : quarticSignedPoleLocal t eta rho
    · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
      · simp [hl,hoff]
        positivity
      · simp [hl,hoff]
    · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalFourthAdverseMassAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalLocalFourthAdverseMassAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthAdverseMassAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hl : quarticSignedPoleLocal t eta rho
    · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
      · simp [hl,hoff]
        positivity
      · simp [hl,hoff]
    · simp [hl]

/--
The local exact-source budget can now be read directly as a balance of the
adverse and favorable fourth angular sectors, plus the certified sixth-order
debt and the untouched exact far source.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_scaledFourthAngularBalance_add_sixthDebt_add_far
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <=
    W.targetStrength
      / (6 * (t/16)^6)
      *
      (W.literalLocalFourthAdverseMassAt
          quarticSignedPoleCanonicalLocalRadius n
        - W.literalLocalFourthFavorableMassAt
          quarticSignedPoleCanonicalLocalRadius n)
      +
    W.literalLocalSixthDebtAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalFarExactAt
        quarticSignedPoleCanonicalLocalRadius n := by
  rw [W.literalLocalFourthHarmonicAt_eq_adverse_sub_favorable
      (eta:=quarticSignedPoleCanonicalLocalRadius)
      (by linarith)]
  exact
    W.literalOffOrdExactAt_le_fourthHarmonic_add_sixthDebt_add_far
      ht n


/-!
## Support geometry of adverse fourth-harmonic mass

Negative fourth phase requires both horizontal and ordinate displacement and
forces them to be comparable.  Thus adverse local fourth-harmonic mass is
supported only on genuinely off-line, off-ordinate zeros.
-/

theorem quarticSignedPolePhysicalFourthPhaseReal_nonneg_of_height_zero
    (t : ℝ) (rho : Zeros)
    (ha : heightOf rho = 0) :
    0 <= quarticSignedPolePhysicalFourthPhaseReal t rho := by
  unfold quarticSignedPolePhysicalFourthPhaseReal
  rw [ha]
  positivity

theorem quarticSignedPolePhysicalFourthPhaseReal_nonneg_of_same_ordinate
    (t : ℝ) (rho : Zeros)
    (hd : (rho : ℂ).im = t) :
    0 <= quarticSignedPolePhysicalFourthPhaseReal t rho := by
  unfold quarticSignedPolePhysicalFourthPhaseReal
  rw [hd]
  ring_nf
  positivity

theorem quarticSignedPole_adverseFourthPhase_height_ne_zero
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    heightOf rho ≠ 0 := by
  intro ha
  have hnonneg :=
    quarticSignedPolePhysicalFourthPhaseReal_nonneg_of_height_zero
      t rho ha
  linarith

theorem quarticSignedPole_adverseFourthPhase_ordinate_ne_center
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    (rho : ℂ).im ≠ t := by
  intro hd
  have hnonneg :=
    quarticSignedPolePhysicalFourthPhaseReal_nonneg_of_same_ordinate
      t rho hd
  linarith

theorem quarticSignedPole_adverseFourthPhase_height_sq_lt_six_delta_sq
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    heightOf rho^2 < 6 * ((rho : ℂ).im-t)^2 := by
  unfold quarticSignedPolePhysicalFourthPhaseReal at hneg
  have ha2 : 0 <= heightOf rho^2 := sq_nonneg _
  have hd2 : 0 <= ((rho : ℂ).im-t)^2 := sq_nonneg _
  by_contra h
  have hge :
      6 * ((rho : ℂ).im-t)^2 <= heightOf rho^2 :=
    le_of_not_gt h
  have ha4 :
      heightOf rho^4 = heightOf rho^2 * heightOf rho^2 := by ring
  have hd4 :
      ((rho : ℂ).im-t)^4 =
        ((rho : ℂ).im-t)^2 * ((rho : ℂ).im-t)^2 := by ring
  rw [ha4,hd4] at hneg
  nlinarith

theorem quarticSignedPole_adverseFourthPhase_delta_sq_lt_six_height_sq
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    ((rho : ℂ).im-t)^2 < 6 * heightOf rho^2 := by
  unfold quarticSignedPolePhysicalFourthPhaseReal at hneg
  have ha2 : 0 <= heightOf rho^2 := sq_nonneg _
  have hd2 : 0 <= ((rho : ℂ).im-t)^2 := sq_nonneg _
  by_contra h
  have hge :
      6 * heightOf rho^2 <= ((rho : ℂ).im-t)^2 :=
    le_of_not_gt h
  have ha4 :
      heightOf rho^4 = heightOf rho^2 * heightOf rho^2 := by ring
  have hd4 :
      ((rho : ℂ).im-t)^4 =
        ((rho : ℂ).im-t)^2 * ((rho : ℂ).im-t)^2 := by ring
  rw [ha4,hd4] at hneg
  nlinarith

theorem quarticSignedPole_adverseFourthPhase_comparable
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    heightOf rho^2 < 6 * ((rho : ℂ).im-t)^2
      ∧
    ((rho : ℂ).im-t)^2 < 6 * heightOf rho^2 := by
  exact ⟨
    quarticSignedPole_adverseFourthPhase_height_sq_lt_six_delta_sq hneg,
    quarticSignedPole_adverseFourthPhase_delta_sq_lt_six_height_sq hneg
  ⟩

/--
Every adverse fourth-phase zero is genuinely off the critical line in the
repo's horizontal coordinate and genuinely separated from the target
ordinate.
-/
theorem quarticSignedPole_adverseFourthPhase_offline_offordinate
    {t : ℝ} {rho : Zeros}
    (hneg : quarticSignedPolePhysicalFourthPhaseReal t rho < 0) :
    heightOf rho ≠ 0 ∧ (rho : ℂ).im ≠ t := by
  exact ⟨
    quarticSignedPole_adverseFourthPhase_height_ne_zero hneg,
    quarticSignedPole_adverseFourthPhase_ordinate_ne_center hneg
  ⟩

end Synthesis
