import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds

/-!
# Eighth-order remainder after the signed sixth harmonic

This file continues the preferred Clay-facing signed-pole lane after the exact
quartic + signed-sixth recut.

The scalar input is already source-written in the imported module:

  |cos x - T6_cos x|   <= |x|^8 / 35840,
  |cosh x - T6_cosh x| <= |x|^8 / 35840,

on the unit ball.

Here we combine those one-variable facts without feeding the complex argument
(q+i alpha)u to a unit-ball theorem.  Separately |alpha*u|<=1 and |q*u|<=1
only imply a sqrt(2) complex radius.

The mixed degree-six Taylor polynomial is retained exactly.  Only total degree
eight and above is majorized.

This file also cross-welds the selected-profile eighth absolute moment back to
the same G1 fourth-Lipschitz constant K(W):

  M8_abs(W) <= (pi+1)^2 M6_abs(W) <= (pi+1)^2 K(W).

Thus the post-sixth route introduces no new independent witness norm.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def quarticSignedPoleMixedDegreeSixTaylor
    (alpha q : ℝ) : ℝ :=
  1
    + (alpha^2 - q^2)/2
    + (alpha^4 + q^4 - 6*alpha^2*q^2)/24
    + quarticSignedPoleSixthPhaseReal alpha q / 720

def quarticSignedPoleMixedPolynomialTail
    (alpha q : ℝ) : ℝ :=
  -(alpha^2*q^6)/1440
    + (alpha^4*q^4)/576
    - (alpha^6*q^2)/1440
    - (alpha^4*q^6)/17280
    + (alpha^6*q^4)/17280
    - (alpha^6*q^6)/518400

def quarticSignedPoleMixedEighthEnvelope
    (alpha q : ℝ) : ℝ :=
  alpha^8 / 30000
    + q^8 / 17000
    + (1/300 : ℝ)
        * (alpha^2*q^6 + alpha^4*q^4 + alpha^6*q^2)

theorem quarticSignedPoleMixedDegreeSixProduct_eq
    (alpha q : ℝ) :
    (1 + alpha^2/2 + alpha^4/24 + alpha^6/720)
      * (1 - q^2/2 + q^4/24 - q^6/720)
      =
    quarticSignedPoleMixedDegreeSixTaylor alpha q
      + quarticSignedPoleMixedPolynomialTail alpha q := by
  unfold quarticSignedPoleMixedDegreeSixTaylor
    quarticSignedPoleMixedPolynomialTail
    quarticSignedPoleSixthPhaseReal
  ring

theorem quarticSignedPoleMixedPolynomialTail_abs_le_eighth
    {alpha q : ℝ}
    (ha : |alpha| <= 1)
    (hq : |q| <= 1) :
    |quarticSignedPoleMixedPolynomialTail alpha q|
      <=
    (1/300 : ℝ)
      * (alpha^2*q^6 + alpha^4*q^4 + alpha^6*q^2) := by
  have ha2abs := pow_le_one₀ (abs_nonneg alpha) ha 2
  have hq2abs := pow_le_one₀ (abs_nonneg q) hq 2
  have ha2 : alpha^2 <= 1 := by
    rw [← abs_pow] at ha2abs
    simpa [abs_of_nonneg (sq_nonneg alpha)] using ha2abs
  have hq2 : q^2 <= 1 := by
    rw [← abs_pow] at hq2abs
    simpa [abs_of_nonneg (sq_nonneg q)] using hq2abs

  have hred46 : alpha^4*q^6 <= alpha^4*q^4 := by
    have h :
        0 <= alpha^4*q^4*(1-q^2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hq2)
    nlinarith
  have hred64 : alpha^6*q^4 <= alpha^4*q^4 := by
    have h :
        0 <= alpha^4*q^4*(1-alpha^2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr ha2)
    nlinarith
  have ha2q2 : alpha^2*q^2 <= 1 := by
    have h :=
      mul_le_mul ha2 hq2 (sq_nonneg q) (by norm_num : (0:ℝ) <= 1)
    norm_num at h ⊢
    exact h
  have hred66 : alpha^6*q^6 <= alpha^4*q^4 := by
    have h :
        0 <= alpha^4*q^4*(1-alpha^2*q^2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr ha2q2)
    nlinarith

  unfold quarticSignedPoleMixedPolynomialTail
  apply abs_le.mpr
  constructor <;>
    nlinarith [hred46, hred64, hred66,
      mul_nonneg (sq_nonneg alpha) (by positivity : 0 <= q^6),
      mul_nonneg (by positivity : 0 <= alpha^4) (by positivity : 0 <= q^4),
      mul_nonneg (by positivity : 0 <= alpha^6) (sq_nonneg q)]

theorem real_cosh_mul_cos_sub_mixedSixth_abs_le_eighth
    {alpha q : ℝ}
    (ha : |alpha| <= 1)
    (hq : |q| <= 1) :
    |Real.cosh alpha * Real.cos q
        - quarticSignedPoleMixedDegreeSixTaylor alpha q|
      <= quarticSignedPoleMixedEighthEnvelope alpha q := by
  let Ch : ℝ :=
    1 + alpha^2/2 + alpha^4/24 + alpha^6/720
  let Co : ℝ :=
    1 - q^2/2 + q^4/24 - q^6/720

  have ha2abs := pow_le_one₀ (abs_nonneg alpha) ha 2
  have ha4abs := pow_le_one₀ (abs_nonneg alpha) ha 4
  have ha6abs := pow_le_one₀ (abs_nonneg alpha) ha 6
  have ha2 : alpha^2 <= 1 := by
    rw [← abs_pow] at ha2abs
    simpa [abs_of_nonneg (sq_nonneg alpha)] using ha2abs
  have ha4 : alpha^4 <= 1 := by
    rw [← abs_pow] at ha4abs
    simpa [abs_of_nonneg (by positivity : 0 <= alpha^4)] using ha4abs
  have ha6 : alpha^6 <= 1 := by
    rw [← abs_pow] at ha6abs
    simpa [abs_of_nonneg (by positivity : 0 <= alpha^6)] using ha6abs

  have hCh0 : 0 <= Ch := by
    dsimp [Ch]
    positivity
  have hChLe : Ch <= 2 := by
    dsimp [Ch]
    nlinarith
  have hChAbs : |Ch| <= 2 := by
    rw [abs_of_nonneg hCh0]
    exact hChLe

  have ha8eq : |alpha|^8 = alpha^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= alpha^8)]
  have hq8eq : |q|^8 = q^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= q^8)]

  have hCosh0 :=
    real_cosh_sub_sixth_abs_le_eighth (x:=alpha) ha
  have hCosh :
      |Real.cosh alpha - Ch| <= alpha^8 / 35840 := by
    rw [ha8eq] at hCosh0
    dsimp [Ch]
    convert hCosh0 using 1 <;> ring

  have hCos0 :=
    real_cos_sub_sixth_abs_le_eighth (x:=q) hq
  have hCos :
      |Real.cos q - Co| <= q^8 / 35840 := by
    rw [hq8eq] at hCos0
    dsimp [Co]
    convert hCos0 using 1 <;> ring

  have h1 :
      |(Real.cosh alpha - Ch) * Real.cos q|
        <= alpha^8 / 35840 := by
    rw [abs_mul]
    calc
      |Real.cosh alpha - Ch| * |Real.cos q|
        <= |Real.cosh alpha - Ch| * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.abs_cos_le_one q)
            (abs_nonneg _)
      _ <= (alpha^8 / 35840) * 1 :=
          mul_le_mul_of_nonneg_right hCosh (by norm_num)
      _ = alpha^8 / 35840 := by ring

  have h2 :
      |Ch * (Real.cos q - Co)|
        <= q^8 / 17920 := by
    rw [abs_mul]
    calc
      |Ch| * |Real.cos q - Co|
        <= 2 * (q^8 / 35840) := by
          exact mul_le_mul hChAbs hCos
            (abs_nonneg _) (by norm_num)
      _ = q^8 / 17920 := by ring

  have htail :=
    quarticSignedPoleMixedPolynomialTail_abs_le_eighth ha hq

  have hsplit :
      Real.cosh alpha * Real.cos q
          - quarticSignedPoleMixedDegreeSixTaylor alpha q
        =
      (Real.cosh alpha - Ch) * Real.cos q
        + Ch * (Real.cos q - Co)
        + quarticSignedPoleMixedPolynomialTail alpha q := by
    have hp :=
      quarticSignedPoleMixedDegreeSixProduct_eq alpha q
    dsimp [Ch,Co] at hp ⊢
    rw [hp]
    ring

  rw [hsplit]
  calc
    |(Real.cosh alpha - Ch) * Real.cos q
        + Ch * (Real.cos q - Co)
        + quarticSignedPoleMixedPolynomialTail alpha q|
      <=
    |(Real.cosh alpha - Ch) * Real.cos q|
      + |Ch * (Real.cos q - Co)|
      + |quarticSignedPoleMixedPolynomialTail alpha q| := by
        exact (abs_add _ _).trans
          (add_le_add (abs_add _ _) le_rfl)
    _ <=
      alpha^8 / 35840
        + q^8 / 17920
        + (1/300 : ℝ)
            * (alpha^2*q^6 + alpha^4*q^4 + alpha^6*q^2) := by
        exact add_le_add (add_le_add h1 h2) htail
    _ <= quarticSignedPoleMixedEighthEnvelope alpha q := by
        unfold quarticSignedPoleMixedEighthEnvelope
        have ha8 : 0 <= alpha^8 := by positivity
        have hq8 : 0 <= q^8 := by positivity
        nlinarith


def QuarticFourSignedPolePair.signedProfileAbsMomentEight
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  compactProfileAbsMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) 8

theorem QuarticFourSignedPolePair.signedProfileAbsMomentEight_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.signedProfileAbsMomentEight := by
  unfold QuarticFourSignedPolePair.signedProfileAbsMomentEight
    compactProfileAbsMoment
  positivity

theorem QuarticFourSignedPolePair.signedProfileAbsMomentEight_le_supportSq_mul_six
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.signedProfileAbsMomentEight
      <= (Real.pi + 1)^2 * W.signedProfileAbsMomentSix := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have h8 :
      Integrable (fun u : ℝ => |P u| * |u|^8) :=
    compactProfile_absMoment_integrable hP hPc 8
  have h6 :
      Integrable (fun u : ℝ => |P u| * |u|^6) :=
    compactProfile_absMoment_integrable hP hPc 6
  unfold QuarticFourSignedPolePair.signedProfileAbsMomentEight
    QuarticFourSignedPolePair.signedProfileAbsMomentSix
    compactProfileAbsMoment
  dsimp [P]
  rw [← integral_const_mul]
  apply integral_mono h8 (h6.const_mul _)
  intro u
  by_cases hz :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t u = 0
  · simp [hz]
  · have hu :=
      W.combinedProfile_support_abs_le_pi_add_one u hz
    have hu2 :
        |u|^2 <= (Real.pi + 1)^2 :=
      pow_le_pow_left₀ (abs_nonneg u) hu 2
    have hfac :
        0 <=
          |quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t u| * |u|^6 := by
      positivity
    calc
      |quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u| * |u|^8
        =
      (|quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u| * |u|^6) * |u|^2 := by
        ring
      _ <=
      (|quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u| * |u|^6)
        * (Real.pi + 1)^2 :=
          mul_le_mul_of_nonneg_left hu2 hfac
      _ =
      (Real.pi + 1)^2
        * (|quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t u| * |u|^6) := by
          ring

theorem QuarticFourSignedPolePair.signedProfileAbsMomentEight_le_supportSq_mul_fourthLipschitz
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.signedProfileAbsMomentEight
      <= (Real.pi + 1)^2 * W.fourthLipschitz := by
  exact
    W.signedProfileAbsMomentEight_le_supportSq_mul_six.trans
      (mul_le_mul_of_nonneg_left
        W.signedProfileAbsMomentSix_le_fourthLipschitz
        (sq_nonneg (Real.pi + 1)))



/-!
## Same-object normalized kernel bound

The mixed scalar theorem now feeds the actual selected signed profile.  The
degree-six Taylor reference integrates exactly to the already-exposed
quartic polynomial plus signed sixth harmonic because M0=M2=0, M4=-4S, and
M6 is retained with sign.
-/

theorem QuarticFourSignedPolePair.mixedDegreeSix_referenceIntegral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        * quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u))
      =
    W.completeJointQuarticPolynomial alpha q
      + W.completeJointSixthHarmonic alpha q := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let c2 : ℝ := (alpha^2-q^2)/2
  let c4 : ℝ :=
    (alpha^4+q^4-6*alpha^2*q^2)/24
  let c6 : ℝ :=
    quarticSignedPoleSixthPhaseReal alpha q / 720

  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have h0 : Integrable P :=
    hP.integrable_of_hasCompactSupport hPc
  have h2 : Integrable (fun u : ℝ => P u * u^2) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have h4 : Integrable (fun u : ℝ => P u * u^4) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have h6 : Integrable (fun u : ℝ => P u * u^6) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right

  have hM0 : ∫ u : ℝ, P u = 0 := by
    change profileZerothMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos
  have hM2 : ∫ u : ℝ, P u * u^2 = 0 := by
    change profileSecondMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have hM4 :
      ∫ u : ℝ, P u * u^4 = -4 * W.targetStrength := by
    change profileFourthMoment P = -4 * W.targetStrength
    rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
    unfold QuarticFourSignedPolePair.targetStrength
    ring
  have hM6 :
      ∫ u : ℝ, P u * u^6 = W.signedProfileMomentSix := by
    rfl

  rw [show
      (fun u : ℝ =>
        P u * quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u))
      =
      fun u =>
        P u
          + c2 * (P u * u^2)
          + c4 * (P u * u^4)
          + c6 * (P u * u^6) by
    funext u
    dsimp [c2,c4,c6]
    unfold quarticSignedPoleMixedDegreeSixTaylor
      quarticSignedPoleSixthPhaseReal
    ring]
  rw [integral_add
        (h0.add (h2.const_mul c2)).add (h4.const_mul c4)
        (h6.const_mul c6),
      integral_add (h0.add (h2.const_mul c2)) (h4.const_mul c4),
      integral_add h0 (h2.const_mul c2),
      integral_const_mul, integral_const_mul, integral_const_mul,
      hM0,hM2,hM4,hM6]
  dsimp [c2,c4,c6]
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
    QuarticFourSignedPolePair.completeJointSixthHarmonic
    quarticSignedPoleSixthPhaseReal
  ring

theorem QuarticFourSignedPolePair.completeJointBeyondSixthRemainder_eq_integral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointBeyondSixthRemainder alpha q
      =
    ∫ u : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
        *
      (Real.cosh (alpha*u) * Real.cos (q*u)
        - quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u)) := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hexact :
      Integrable
        (fun u : ℝ =>
          P u * Real.cosh (alpha*u) * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have href :
      Integrable
        (fun u : ℝ =>
          P u * quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by
        dsimp [P]
        unfold quarticSignedPoleMixedDegreeSixTaylor
          quarticSignedPoleSixthPhaseReal
        fun_prop)
      hPc.mul_right

  have hK :=
    W.signedNormalizedPairKernel_eq_combinedIntegral
      (alpha:=alpha) (q:=q)
  have hT :=
    W.mixedDegreeSix_referenceIntegral
      (alpha:=alpha) (q:=q)
  have hsplit :=
    W.signedNormalizedPairKernel_eq_completeQuarticSixth
      (alpha:=alpha) (q:=q)

  unfold QuarticFourSignedPolePair.completeJointBeyondSixthRemainder
  have hrem :
      W.completeJointQuarticRemainder alpha q
        - W.completeJointSixthHarmonic alpha q
      =
      W.signedNormalizedPairKernel alpha q
        - (W.completeJointQuarticPolynomial alpha q
            + W.completeJointSixthHarmonic alpha q) := by
    rw [W.signedNormalizedPairKernel_eq_completeQuarticJet]
    ring
  rw [hrem,hK,← hT,← integral_sub hexact href]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp [P]
    ring

theorem QuarticFourSignedPolePair.completeJointBeyondSixthRemainder_abs_le_eighth
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.completeJointBeyondSixthRemainder alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * W.signedProfileAbsMomentEight := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let E : ℝ := quarticSignedPoleMixedEighthEnvelope alpha q
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          P u *
          (Real.cosh (alpha*u) * Real.cos (q*u)
            - quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u))) :=
    Continuous.integrable_of_hasCompactSupport
      (by
        dsimp [P]
        unfold quarticSignedPoleMixedDegreeSixTaylor
          quarticSignedPoleSixthPhaseReal
        fun_prop)
      hPc.mul_right
  have hmaj :
      Integrable
        (fun u : ℝ => E * (|P u| * |u|^8)) :=
    (compactProfile_absMoment_integrable hP hPc 8).const_mul E

  rw [W.completeJointBeyondSixthRemainder_eq_integral]
  calc
    |∫ u : ℝ,
      P u *
      (Real.cosh (alpha*u) * Real.cos (q*u)
        - quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u))|
      <=
    ∫ u : ℝ,
      |P u *
      (Real.cosh (alpha*u) * Real.cos (q*u)
        - quarticSignedPoleMixedDegreeSixTaylor (alpha*u) (q*u))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ, E * (|P u| * |u|^8) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hz : P u = 0
      · simp [hz]
      · have hau :=
          W.abs_q_mul_u_le_one_of_local
            (q:=alpha) ha hz
        have hqu :=
          W.abs_q_mul_u_le_one_of_local
            (q:=q) hq hz
        have hmixed :=
          real_cosh_mul_cos_sub_mixedSixth_abs_le_eighth
            hau hqu
        have hu8 : |u|^8 = u^8 := by
          rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= u^8)]
        have hscale :
            quarticSignedPoleMixedEighthEnvelope (alpha*u) (q*u)
              =
            E * |u|^8 := by
          dsimp [E]
          unfold quarticSignedPoleMixedEighthEnvelope
          rw [hu8]
          ring
        rw [hscale] at hmixed
        rw [abs_mul]
        have hmul :=
          mul_le_mul_of_nonneg_left hmixed (abs_nonneg (P u))
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ =
    E * W.signedProfileAbsMomentEight := by
      unfold QuarticFourSignedPolePair.signedProfileAbsMomentEight
        compactProfileAbsMoment
      dsimp [P,E]
      rw [integral_const_mul]

theorem QuarticFourSignedPolePair.completeJointBeyondSixthRemainder_abs_le_G1
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= quarticSignedPoleCanonicalLocalRadius)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.completeJointBeyondSixthRemainder alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * ((Real.pi+1)^2 * W.fourthLipschitz) := by
  have hbase :=
    W.completeJointBeyondSixthRemainder_abs_le_eighth ha hq
  have hE :
      0 <= quarticSignedPoleMixedEighthEnvelope alpha q := by
    unfold quarticSignedPoleMixedEighthEnvelope
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left
      W.signedProfileAbsMomentEight_le_supportSq_mul_fourthLipschitz
      hE)


/-!
## Literal physical r^-10 transport

After the outer pair normalization r^-2, the homogeneous eighth envelope
contributes at physical scale r^-10.
-/

def QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let a := heightOf sigma
  let d := (sigma : ℂ).im - t
  a^8 / 30000
    + d^8 / 17000
    + (1/300 : ℝ)
        * (a^2*d^6 + a^4*d^4 + a^6*d^2)

def QuarticFourSignedPolePair.literalCompleteEighthRemainderBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * W.signedProfileAbsMomentEight
    * W.literalCompleteEighthPhysicalPolynomial sigma
    / (t/16)^10

theorem QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    0 <= W.literalCompleteEighthPhysicalPolynomial sigma := by
  unfold QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial
  positivity

theorem QuarticFourSignedPolePair.mixedEighthEnvelope_physical_rescale
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    quarticSignedPoleMixedEighthEnvelope
        (heightOf sigma/(t/16))
        (((sigma : ℂ).im-t)/(t/16))
      =
    W.literalCompleteEighthPhysicalPolynomial sigma / (t/16)^8 := by
  unfold quarticSignedPoleMixedEighthEnvelope
    QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial
  dsimp
  have hr : t/16 ≠ 0 := by positivity
  field_simp [hr]
  ring

theorem QuarticFourSignedPolePair.literalCompleteJointBeyondSixthRemainder_abs_le
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (ha :
      |heightOf sigma/(t/16)|
        <= quarticSignedPoleCanonicalLocalRadius)
    (hq :
      |((sigma : ℂ).im-t)/(t/16)|
        <= quarticSignedPoleCanonicalLocalRadius) :
    |W.literalCompleteJointBeyondSixthRemainder sigma|
      <= W.literalCompleteEighthRemainderBound sigma := by
  unfold QuarticFourSignedPolePair.literalCompleteJointBeyondSixthRemainder
  dsimp
  have hr2 : 0 < (t/16)^2 := by positivity
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  rw [abs_mul, abs_div, abs_of_nonneg hm, abs_of_pos hr2]
  have hnorm :=
    W.completeJointBeyondSixthRemainder_abs_le_eighth ha hq
  have hfac :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2 := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hnorm hfac
  rw [W.mixedEighthEnvelope_physical_rescale ht sigma] at hscaled
  unfold QuarticFourSignedPolePair.literalCompleteEighthRemainderBound
  have hr : 0 < t/16 := by positivity
  calc
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
      *
    |W.completeJointBeyondSixthRemainder
      (heightOf sigma/(t/16))
      (((sigma : ℂ).im-t)/(t/16))|
      <=
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
      *
    (W.literalCompleteEighthPhysicalPolynomial sigma / (t/16)^8
      * W.signedProfileAbsMomentEight) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * W.signedProfileAbsMomentEight
      * W.literalCompleteEighthPhysicalPolynomial sigma
      / (t/16)^10 := by
        field_simp [hr.ne']
        ring

end Synthesis
