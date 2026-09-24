import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleSmooth
import Synthesis.RiemannProjectiveResidualOrthogonalizedQuartic
import Synthesis.RiemannProjectiveCircularHyperbolicDuality

/-!
# Signed pole-cancelled four-window target profile

Positive-cone pole cancellation is impossible, but the signed endpoint
combination has positive quartic target transversality.

For two smooth endpoint profiles at lambda=1/2 and lambda=2/3 write

  P1 = smooth pole coordinate of the half-profile,
  P2 = smooth pole coordinate of the two-thirds profile.

Form the signed projective physical profile

  P_comb = P2 * P_half - P1 * P_twoThirds.

If both component profiles satisfy J2=0, then P_comb has zero zeroth and second
moments.  Its fourth moment is

  4(P2 J4_half - P1 J4_twoThirds)
    = -4 (P2 S_half - P1 S_twoThirds).

Hence the positive signed pole/target determinant proved in the previous file
makes the combined fourth moment strictly negative.

The generic fourth-order local-sign theorem then yields a punctured band on
which the combined hyperbolic transform is negative.  By exact
height/hyperbolic duality, the corresponding signed combination of target
height defects is strictly positive.

Thus signed pole orthogonalization can recover same-ordinate positivity as a
new combined observable; it does not need nonnegative coefficients termwise.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticFourNormalizedProjectiveProfile
    (R lam mu : ℝ) : ℝ -> ℝ :=
  genericProjectivePhysicalProfile
    (quarticFourWindowProfile R lam mu) 1

theorem quarticFourNormalizedProjectiveProfile_continuous
    {R lam mu : ℝ} (hR : 0 < R) :
    Continuous (quarticFourNormalizedProjectiveProfile R lam mu) :=
  genericProjectivePhysicalProfile_continuous
    (quarticFourWindowProfile_continuous (lam:=lam) (mu:=mu) hR) 1

theorem quarticFourNormalizedProjectiveProfile_compact
    {R lam mu : ℝ} (hR : 0 < R) :
    HasCompactSupport (quarticFourNormalizedProjectiveProfile R lam mu) :=
  genericProjectivePhysicalProfile_compact
    (quarticFourWindowProfile_compact (lam:=lam) (mu:=mu) hR) 1

def quarticFourSignedPoleCombinedProfile
    (R muHalf muTwo t : ℝ) : ℝ -> ℝ :=
  profileLinearCombination
    (quarticFourSmoothFinitePoleResidual R (2/3) muTwo t)
    (-quarticFourSmoothFinitePoleResidual R (1/2) muHalf t)
    (quarticFourNormalizedProjectiveProfile R (1/2) muHalf)
    (quarticFourNormalizedProjectiveProfile R (2/3) muTwo)

theorem quarticFourSignedPoleCombinedProfile_continuous
    {R muHalf muTwo t : ℝ} (hR : 0 < R) :
    Continuous
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t) := by
  unfold quarticFourSignedPoleCombinedProfile
  exact profileLinearCombination_continuous
    (quarticFourNormalizedProjectiveProfile_continuous
      (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
    (quarticFourNormalizedProjectiveProfile_continuous
      (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
    _ _

theorem quarticFourSignedPoleCombinedProfile_compact
    {R muHalf muTwo t : ℝ} (hR : 0 < R) :
    HasCompactSupport
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t) := by
  unfold quarticFourSignedPoleCombinedProfile
  exact profileLinearCombination_compact
    (quarticFourNormalizedProjectiveProfile_compact
      (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
    (quarticFourNormalizedProjectiveProfile_compact
      (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
    _ _

theorem quarticFourNormalizedProjectiveProfile_zeroth_zero
    {R lam mu : ℝ} (hR : 0 < R) :
    profileZerothMoment
      (quarticFourNormalizedProjectiveProfile R lam mu) = 0 := by
  unfold profileZerothMoment quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_integral_zero
    (quarticFourWindowProfile_continuous (lam:=lam) (mu:=mu) hR)
    (quarticFourWindowProfile_compact (lam:=lam) (mu:=mu) hR) 1

theorem quarticFourNormalizedProjectiveProfile_second
    {R lam mu : ℝ} (hR : 0 < R) :
    profileSecondMoment
      (quarticFourNormalizedProjectiveProfile R lam mu)
      =
    4 * projectiveBracketSecondMoment
      (quarticFourWindowProfile R lam mu) 1 := by
  unfold profileSecondMoment quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_secondMoment 1

theorem quarticFourNormalizedProjectiveProfile_fourth
    {R lam mu : ℝ} (hR : 0 < R) :
    profileFourthMoment
      (quarticFourNormalizedProjectiveProfile R lam mu)
      =
    4 * projectiveBracketFourthMoment
      (quarticFourWindowProfile R lam mu) 1 := by
  unfold profileFourthMoment quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_fourthMoment 1

theorem quarticFourSignedPoleCombinedProfile_zeroth_zero
    {R muHalf muTwo t : ℝ} (hR : 0 < R) :
    profileZerothMoment
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t) = 0 := by
  unfold quarticFourSignedPoleCombinedProfile profileZerothMoment
  rw [profileMoment_linearCombination
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      _ _ 0]
  simpa [pow_zero,
    quarticFourNormalizedProjectiveProfile_zeroth_zero
      (lam:=(1/2 : ℝ)) (mu:=muHalf) hR,
    quarticFourNormalizedProjectiveProfile_zeroth_zero
      (lam:=(2/3 : ℝ)) (mu:=muTwo) hR]

theorem quarticFourSignedPoleCombinedProfile_second_zero
    {R muHalf muTwo t : ℝ} (hR : 0 < R)
    (hJ2Half :
      projectiveBracketSecondMoment
        (quarticFourWindowProfile R (1/2) muHalf) 1 = 0)
    (hJ2Two :
      projectiveBracketSecondMoment
        (quarticFourWindowProfile R (2/3) muTwo) 1 = 0) :
    profileSecondMoment
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t) = 0 := by
  unfold quarticFourSignedPoleCombinedProfile profileSecondMoment
  rw [profileMoment_linearCombination
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      _ _ 2,
    show
      (∫ u : ℝ,
        quarticFourNormalizedProjectiveProfile R (1/2) muHalf u*u^2)
        = 0 by
      rw [quarticFourNormalizedProjectiveProfile_second hR, hJ2Half]
      ring,
    show
      (∫ u : ℝ,
        quarticFourNormalizedProjectiveProfile R (2/3) muTwo u*u^2)
        = 0 by
      rw [quarticFourNormalizedProjectiveProfile_second hR, hJ2Two]
      ring]
  ring

theorem quarticFourSignedPoleCombinedProfile_fourth
    {R muHalf muTwo t : ℝ} (hR : 0 < R) :
    profileFourthMoment
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t)
      =
    -4 * quarticFourSmoothPoleCancelledTarget
      R muHalf muTwo t := by
  unfold quarticFourSignedPoleCombinedProfile
    quarticFourSmoothPoleCancelledTarget profileFourthMoment
    quarticFourSmoothTargetStrength
  rw [profileMoment_linearCombination
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      _ _ 4,
    quarticFourNormalizedProjectiveProfile_fourth
      (lam:=(1/2 : ℝ)) (mu:=muHalf) hR,
    quarticFourNormalizedProjectiveProfile_fourth
      (lam:=(2/3 : ℝ)) (mu:=muTwo) hR]
  ring

theorem quarticFourSignedPoleCombinedProfile_fourth_neg
    {R muHalf muTwo t : ℝ} (hR : 0 < R)
    (htrans :
      0 < quarticFourSmoothPoleCancelledTarget
        R muHalf muTwo t) :
    profileFourthMoment
      (quarticFourSignedPoleCombinedProfile R muHalf muTwo t) < 0 := by
  rw [quarticFourSignedPoleCombinedProfile_fourth hR]
  nlinarith

theorem compactCoshTransform_profileLinearCombination
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (a b x : ℝ) :
    compactCoshTransform
      (profileLinearCombination a b P Q) x
      =
    a * compactCoshTransform P x
      + b * compactCoshTransform Q x := by
  unfold compactCoshTransform profileLinearCombination
  have hPi :
      Integrable (fun u => P u * Real.cosh (x*u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hQi :
      Integrable (fun u => Q u * Real.cosh (x*u)) :=
    (hQ.mul (by fun_prop)).integrable_of_hasCompactSupport hQc.mul_right
  have hpoint :
      (fun u : ℝ =>
        (a*P u+b*Q u)*Real.cosh (x*u))
        =
      fun u => a*(P u*Real.cosh (x*u))
        + b*(Q u*Real.cosh (x*u)) := by
    funext u
    ring
  rw [hpoint,
      integral_add (hPi.const_mul a) (hQi.const_mul b),
      integral_const_mul, integral_const_mul]

def quarticFourSignedPoleCombinedHeightDefect
    (R muHalf muTwo t a : ℝ) : ℝ :=
  quarticFourSmoothFinitePoleResidual R (2/3) muTwo t
      * heightDefect
          (quarticFourWindowProfile R (1/2) muHalf) 1 a 0
    -
  quarticFourSmoothFinitePoleResidual R (1/2) muHalf t
      * heightDefect
          (quarticFourWindowProfile R (2/3) muTwo) 1 a 0

theorem quarticFourSignedPoleCombinedHeightDefect_eq_cosh
    {R muHalf muTwo t : ℝ} (hR : 0 < R)
    (a : ℝ) :
    quarticFourSignedPoleCombinedHeightDefect
        R muHalf muTwo t a
      =
    -(1/4 : ℝ) *
      compactCoshTransform
        (quarticFourSignedPoleCombinedProfile
          R muHalf muTwo t) a := by
  let G1 := quarticFourWindowProfile R (1/2) muHalf
  let G2 := quarticFourWindowProfile R (2/3) muTwo
  have h1 :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (quarticFourWindowProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourWindowProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      1 a
  have h2 :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (quarticFourWindowProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      (quarticFourWindowProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      1 a
  unfold quarticFourSignedPoleCombinedHeightDefect
    quarticFourSignedPoleCombinedProfile
  rw [h1,h2,
    compactCoshTransform_profileLinearCombination
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR)]
  ring

/--
Positive punctured target band for the signed pole-cancelled observable.
-/
theorem exists_quarticFourSignedPoleCombinedHeightDefect_pos_punctured
    {R muHalf muTwo t : ℝ} (hR : 0 < R)
    (hJ2Half :
      projectiveBracketSecondMoment
        (quarticFourWindowProfile R (1/2) muHalf) 1 = 0)
    (hJ2Two :
      projectiveBracketSecondMoment
        (quarticFourWindowProfile R (2/3) muTwo) 1 = 0)
    (htrans :
      0 < quarticFourSmoothPoleCancelledTarget
        R muHalf muTwo t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < |a| -> |a| < eps ->
        0 <
        quarticFourSignedPoleCombinedHeightDefect
          R muHalf muTwo t a := by
  let P :=
    quarticFourSignedPoleCombinedProfile R muHalf muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous hR
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact hR
  have hP0 : profileZerothMoment P = 0 :=
    quarticFourSignedPoleCombinedProfile_zeroth_zero hR
  have hP2 : profileSecondMoment P = 0 :=
    quarticFourSignedPoleCombinedProfile_second_zero
      hR hJ2Half hJ2Two
  have hP4 : profileFourthMoment P < 0 :=
    quarticFourSignedPoleCombinedProfile_fourth_neg hR htrans

  obtain ⟨eps,heps,hcoshR⟩ :=
    exists_profile_cosh_neg_right_of_quartic_moments
      hP hPc hP0 hP2 hP4
  refine ⟨eps,heps,?_⟩
  intro a ha0 hae
  have hcosh : compactCoshTransform P a < 0 := by
    by_cases ha : 0 <= a
    · have habs : |a| = a := abs_of_nonneg ha
      exact hcoshR a
        (by simpa [habs] using ha0)
        (by simpa [habs] using hae)
    · have haneg : a < 0 := lt_of_not_ge ha
      have habs : |a| = -a := abs_of_neg haneg
      have hp := hcoshR (-a)
        (by linarith)
        (by simpa [habs] using hae)
      have heven :
          compactCoshTransform P (-a)
            = compactCoshTransform P a := by
        unfold compactCoshTransform
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => by
          rw [show (-a)*u = -(a*u) by ring, Real.cosh_neg]
      rw [heven] at hp
      exact hp
  rw [quarticFourSignedPoleCombinedHeightDefect_eq_cosh hR]
  nlinarith

end Synthesis
