import Synthesis.RiemannProjectiveQuarticCompletedResidual
import Synthesis.RiemannProjectiveResidualOrthogonalizedQuartic

/-!
# Exact full base+Gamma orthogonalization for two quartic detectors

The quartic high decomposition already defines the complete infinite base+Gamma
scalar

  R_B(W,t) = quarticBaseMuResidual W t.

For two quartic witnesses W1,W2 set

  c1 = R_B(W2,t),
  c2 = -R_B(W1,t).

Then

  c1 R_B(W1,t) + c2 R_B(W2,t) = 0

identically: the complete q-only zero-minus-mu channel is removed before any
estimate.

At normalized physical-profile level define

  P_i = genericProjectivePhysicalProfile(G_i,1).

Each P_i has zeroth and second moments zero and fourth moment 4 J4_i<0.
The same coefficient combination has fourth moment

  4 ( R_B(W2,t) J4_1 - R_B(W1,t) J4_2 ).

Thus the only condition needed to retain a quartic target detector after exact
full base cancellation is the scalar transversality

  R_B(W2,t) J4_1 - R_B(W1,t) J4_2 != 0.

This replaces a global sign demand on one N-mu pairing by a two-test
non-proportionality condition.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def quarticWitnessNormalizedProfile
    (W : QuarticHighWitness) : ℝ -> ℝ :=
  genericProjectivePhysicalProfile
    (quarticThreeWindowProfile W.R W.lam) 1

theorem quarticWitnessNormalizedProfile_continuous
    (W : QuarticHighWitness) :
    Continuous (quarticWitnessNormalizedProfile W) :=
  genericProjectivePhysicalProfile_continuous
    (quarticThreeWindowProfile_continuous W.Rpos) 1

theorem quarticWitnessNormalizedProfile_compact
    (W : QuarticHighWitness) :
    HasCompactSupport (quarticWitnessNormalizedProfile W) :=
  genericProjectivePhysicalProfile_compact
    (quarticThreeWindowProfile_compact W.Rpos) 1

theorem quarticWitnessNormalizedProfile_zeroth_zero
    (W : QuarticHighWitness) :
    profileZerothMoment (quarticWitnessNormalizedProfile W) = 0 := by
  unfold profileZerothMoment quarticWitnessNormalizedProfile
  exact genericProjectivePhysicalProfile_integral_zero
    (quarticThreeWindowProfile_continuous W.Rpos)
    (quarticThreeWindowProfile_compact W.Rpos) 1

theorem quarticWitnessNormalizedProfile_second_zero
    (W : QuarticHighWitness) :
    profileSecondMoment (quarticWitnessNormalizedProfile W) = 0 := by
  unfold profileSecondMoment quarticWitnessNormalizedProfile
  rw [genericProjectivePhysicalProfile_secondMoment 1,
      W.J2zero]
  ring

theorem quarticWitnessNormalizedProfile_fourth
    (W : QuarticHighWitness) :
    profileFourthMoment (quarticWitnessNormalizedProfile W)
      = 4 * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W.R W.lam) 1 := by
  unfold profileFourthMoment quarticWitnessNormalizedProfile
  exact genericProjectivePhysicalProfile_fourthMoment 1

def quarticFullBaseTransversality
    (W1 W2 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBaseMuResidual W2 t
      * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W1.R W1.lam) 1
    -
  quarticBaseMuResidual W1 t
      * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W2.R W2.lam) 1

def quarticFullBaseOrthogonalProfile
    (W1 W2 : QuarticHighWitness) (t : ℝ) : ℝ -> ℝ :=
  profileLinearCombination
    (quarticBaseMuResidual W2 t)
    (-quarticBaseMuResidual W1 t)
    (quarticWitnessNormalizedProfile W1)
    (quarticWitnessNormalizedProfile W2)

theorem quarticFullBaseOrthogonal_scalar_zero
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    quarticBaseMuResidual W2 t * quarticBaseMuResidual W1 t
      + (-quarticBaseMuResidual W1 t) * quarticBaseMuResidual W2 t
      = 0 := by
  ring

theorem quarticFullBaseOrthogonalProfile_zeroth_zero
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    profileZerothMoment
      (quarticFullBaseOrthogonalProfile W1 W2 t) = 0 := by
  unfold quarticFullBaseOrthogonalProfile profileZerothMoment
  rw [profileMoment_linearCombination
      (quarticWitnessNormalizedProfile_continuous W1)
      (quarticWitnessNormalizedProfile_compact W1)
      (quarticWitnessNormalizedProfile_continuous W2)
      (quarticWitnessNormalizedProfile_compact W2)
      (quarticBaseMuResidual W2 t)
      (-quarticBaseMuResidual W1 t) 0]
  simpa [pow_zero,
    quarticWitnessNormalizedProfile_zeroth_zero W1,
    quarticWitnessNormalizedProfile_zeroth_zero W2]

theorem quarticFullBaseOrthogonalProfile_second_zero
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    profileSecondMoment
      (quarticFullBaseOrthogonalProfile W1 W2 t) = 0 := by
  unfold quarticFullBaseOrthogonalProfile profileSecondMoment
  rw [profileMoment_linearCombination
      (quarticWitnessNormalizedProfile_continuous W1)
      (quarticWitnessNormalizedProfile_compact W1)
      (quarticWitnessNormalizedProfile_continuous W2)
      (quarticWitnessNormalizedProfile_compact W2)
      (quarticBaseMuResidual W2 t)
      (-quarticBaseMuResidual W1 t) 2]
  rw [show
      (∫ u : ℝ,quarticWitnessNormalizedProfile W1 u*u^2)=0 by
        exact quarticWitnessNormalizedProfile_second_zero W1,
      show
      (∫ u : ℝ,quarticWitnessNormalizedProfile W2 u*u^2)=0 by
        exact quarticWitnessNormalizedProfile_second_zero W2]
  ring

theorem quarticFullBaseOrthogonalProfile_fourth
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    profileFourthMoment
      (quarticFullBaseOrthogonalProfile W1 W2 t)
      =
    4 * quarticFullBaseTransversality W1 W2 t := by
  unfold quarticFullBaseOrthogonalProfile
    quarticFullBaseTransversality profileFourthMoment
  rw [profileMoment_linearCombination
      (quarticWitnessNormalizedProfile_continuous W1)
      (quarticWitnessNormalizedProfile_compact W1)
      (quarticWitnessNormalizedProfile_continuous W2)
      (quarticWitnessNormalizedProfile_compact W2)
      (quarticBaseMuResidual W2 t)
      (-quarticBaseMuResidual W1 t) 4]
  rw [quarticWitnessNormalizedProfile_fourth W1,
      quarticWitnessNormalizedProfile_fourth W2]
  ring

def orientedQuarticFullBaseOrthogonalProfile
    (W1 W2 : QuarticHighWitness) (t : ℝ) : ℝ -> ℝ :=
  if quarticFullBaseTransversality W1 W2 t < 0
  then quarticFullBaseOrthogonalProfile W1 W2 t
  else fun u => -quarticFullBaseOrthogonalProfile W1 W2 t u

theorem orientedQuarticFullBaseOrthogonalProfile_fourth_neg
    (W1 W2 : QuarticHighWitness) {t : ℝ}
    (htrans : quarticFullBaseTransversality W1 W2 t ≠ 0) :
    profileFourthMoment
      (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) < 0 := by
  unfold orientedQuarticFullBaseOrthogonalProfile
  by_cases hneg : quarticFullBaseTransversality W1 W2 t < 0
  · simp [hneg]
    rw [quarticFullBaseOrthogonalProfile_fourth]
    nlinarith
  · simp [hneg]
    have hpos : 0 < quarticFullBaseTransversality W1 W2 t :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm htrans)
    unfold profileFourthMoment
    rw [show
      (fun u : ℝ => -quarticFullBaseOrthogonalProfile W1 W2 t u*u^4)
        =
      fun u => -(quarticFullBaseOrthogonalProfile W1 W2 t u*u^4) by
        funext u
        ring,
      integral_neg,
      quarticFullBaseOrthogonalProfile_fourth]
    nlinarith


theorem quarticFullBaseOrthogonalProfile_continuous
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    Continuous (quarticFullBaseOrthogonalProfile W1 W2 t) := by
  unfold quarticFullBaseOrthogonalProfile
  exact profileLinearCombination_continuous
    (quarticWitnessNormalizedProfile_continuous W1)
    (quarticWitnessNormalizedProfile_continuous W2)
    _ _

theorem quarticFullBaseOrthogonalProfile_compact
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    HasCompactSupport (quarticFullBaseOrthogonalProfile W1 W2 t) := by
  unfold quarticFullBaseOrthogonalProfile
  exact profileLinearCombination_compact
    (quarticWitnessNormalizedProfile_compact W1)
    (quarticWitnessNormalizedProfile_compact W2)
    _ _

theorem orientedQuarticFullBaseOrthogonalProfile_continuous
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    Continuous (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) := by
  unfold orientedQuarticFullBaseOrthogonalProfile
  split_ifs
  · exact quarticFullBaseOrthogonalProfile_continuous W1 W2 t
  · exact (quarticFullBaseOrthogonalProfile_continuous W1 W2 t).neg

theorem orientedQuarticFullBaseOrthogonalProfile_compact
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    HasCompactSupport
      (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) := by
  unfold orientedQuarticFullBaseOrthogonalProfile
  split_ifs
  · exact quarticFullBaseOrthogonalProfile_compact W1 W2 t
  · exact (quarticFullBaseOrthogonalProfile_compact W1 W2 t).neg

theorem orientedQuarticFullBaseOrthogonalProfile_zeroth_zero
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    profileZerothMoment
      (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) = 0 := by
  unfold orientedQuarticFullBaseOrthogonalProfile
  split_ifs
  · exact quarticFullBaseOrthogonalProfile_zeroth_zero W1 W2 t
  · unfold profileZerothMoment
    rw [integral_neg]
    rw [show
      (∫ u : ℝ, quarticFullBaseOrthogonalProfile W1 W2 t u)
        = 0 by
      exact quarticFullBaseOrthogonalProfile_zeroth_zero W1 W2 t]
    simp

theorem orientedQuarticFullBaseOrthogonalProfile_second_zero
    (W1 W2 : QuarticHighWitness) (t : ℝ) :
    profileSecondMoment
      (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) = 0 := by
  unfold orientedQuarticFullBaseOrthogonalProfile
  split_ifs
  · exact quarticFullBaseOrthogonalProfile_second_zero W1 W2 t
  · unfold profileSecondMoment
    rw [show
      (fun u : ℝ => -quarticFullBaseOrthogonalProfile W1 W2 t u*u^2)
        =
      fun u => -(quarticFullBaseOrthogonalProfile W1 W2 t u*u^2) by
        funext u
        ring,
      integral_neg]
    rw [show
      (∫ u : ℝ,
        quarticFullBaseOrthogonalProfile W1 W2 t u*u^2)=0 by
      exact quarticFullBaseOrthogonalProfile_second_zero W1 W2 t]
    simp

theorem exists_orientedQuarticFullBaseOrthogonalProfile_local_signs
    (W1 W2 : QuarticHighWitness)
    {t : ℝ}
    (htrans : quarticFullBaseTransversality W1 W2 t ≠ 0) :
    (∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < q -> q < eps ->
        compactCosineTransform
          (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) q < 0)
    ∧
    (∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < a -> a < eps ->
        compactCoshTransform
          (orientedQuarticFullBaseOrthogonalProfile W1 W2 t) a < 0) := by
  let P := orientedQuarticFullBaseOrthogonalProfile W1 W2 t
  have hP : Continuous P :=
    orientedQuarticFullBaseOrthogonalProfile_continuous W1 W2 t
  have hPc : HasCompactSupport P :=
    orientedQuarticFullBaseOrthogonalProfile_compact W1 W2 t
  have hP0 : profileZerothMoment P = 0 :=
    orientedQuarticFullBaseOrthogonalProfile_zeroth_zero W1 W2 t
  have hP2 : profileSecondMoment P = 0 :=
    orientedQuarticFullBaseOrthogonalProfile_second_zero W1 W2 t
  have hP4 : profileFourthMoment P < 0 :=
    orientedQuarticFullBaseOrthogonalProfile_fourth_neg W1 W2 htrans
  exact ⟨
    exists_profile_cosine_neg_right_of_quartic_moments
      hP hPc hP0 hP2 hP4,
    exists_profile_cosh_neg_right_of_quartic_moments
      hP hPc hP0 hP2 hP4
  ⟩

end Synthesis
