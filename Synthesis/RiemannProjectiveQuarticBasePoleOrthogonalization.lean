import Synthesis.RiemannProjectiveQuarticFullBaseOrthogonalization

/-!
# Simultaneous exact cancellation of quartic base+Gamma and pole channels

For a quartic witness W at ordinate t define two complete scalar channels

  B(W,t) = quarticBaseMuResidual W t,
  P(W,t) = poleProjectiveDefect(g_W,t,t/16).

Given three witnesses W1,W2,W3, take the cross-product coefficients

  c1 = B2 P3 - B3 P2
  c2 = B3 P1 - B1 P3
  c3 = B1 P2 - B2 P1.

Then, identically,

  sum_i c_i B_i = 0,
  sum_i c_i P_i = 0.

The normalized physical-profile combination has zeroth and second moments zero.
Its fourth moment is four times the 3x3 determinant with rows

  B_i,
  P_i,
  J4_i.

If that determinant is nonzero, orient the profile so its fourth moment is
negative.  The same quartic local cosine/cosh detector then survives while both
base+Gamma and pole have been projected out exactly.

The only external channel left in the corresponding linear combination of the
high identities is the off-ordinate horizontal correction.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

def quarticPoleResidual
    (W : QuarticHighWitness) (t : ℝ) : ℝ :=
  poleProjectiveDefect
    (quarticPhysicalDetector W.R W.lam t)
    t (t/16)

def quarticBasePoleCoeff1
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBaseMuResidual W2 t * quarticPoleResidual W3 t
    - quarticBaseMuResidual W3 t * quarticPoleResidual W2 t

def quarticBasePoleCoeff2
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBaseMuResidual W3 t * quarticPoleResidual W1 t
    - quarticBaseMuResidual W1 t * quarticPoleResidual W3 t

def quarticBasePoleCoeff3
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBaseMuResidual W1 t * quarticPoleResidual W2 t
    - quarticBaseMuResidual W2 t * quarticPoleResidual W1 t

theorem quarticBasePoleCoeffs_cancel_base
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    quarticBasePoleCoeff1 W1 W2 W3 t * quarticBaseMuResidual W1 t
      + quarticBasePoleCoeff2 W1 W2 W3 t * quarticBaseMuResidual W2 t
      + quarticBasePoleCoeff3 W1 W2 W3 t * quarticBaseMuResidual W3 t
      = 0 := by
  unfold quarticBasePoleCoeff1 quarticBasePoleCoeff2
    quarticBasePoleCoeff3
  ring

theorem quarticBasePoleCoeffs_cancel_pole
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    quarticBasePoleCoeff1 W1 W2 W3 t * quarticPoleResidual W1 t
      + quarticBasePoleCoeff2 W1 W2 W3 t * quarticPoleResidual W2 t
      + quarticBasePoleCoeff3 W1 W2 W3 t * quarticPoleResidual W3 t
      = 0 := by
  unfold quarticBasePoleCoeff1 quarticBasePoleCoeff2
    quarticBasePoleCoeff3
  ring

def quarticBasePoleOrthogonalProfile
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ -> ℝ :=
  fun u =>
    quarticBasePoleCoeff1 W1 W2 W3 t
        * quarticWitnessNormalizedProfile W1 u
      + quarticBasePoleCoeff2 W1 W2 W3 t
        * quarticWitnessNormalizedProfile W2 u
      + quarticBasePoleCoeff3 W1 W2 W3 t
        * quarticWitnessNormalizedProfile W3 u

def quarticBasePoleTargetDet
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBasePoleCoeff1 W1 W2 W3 t
      * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W1.R W1.lam) 1
    + quarticBasePoleCoeff2 W1 W2 W3 t
      * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W2.R W2.lam) 1
    + quarticBasePoleCoeff3 W1 W2 W3 t
      * projectiveBracketFourthMoment
          (quarticThreeWindowProfile W3.R W3.lam) 1

theorem quarticBasePoleOrthogonalProfile_continuous
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    Continuous (quarticBasePoleOrthogonalProfile W1 W2 W3 t) := by
  unfold quarticBasePoleOrthogonalProfile
  fun_prop

theorem quarticBasePoleOrthogonalProfile_compact
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    HasCompactSupport (quarticBasePoleOrthogonalProfile W1 W2 W3 t) := by
  unfold quarticBasePoleOrthogonalProfile
  exact
    ((quarticWitnessNormalizedProfile_compact W1).mul_left.add
      (quarticWitnessNormalizedProfile_compact W2).mul_left).add
      (quarticWitnessNormalizedProfile_compact W3).mul_left

theorem quarticBasePoleOrthogonalProfile_zeroth_zero
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileZerothMoment
      (quarticBasePoleOrthogonalProfile W1 W2 W3 t) = 0 := by
  unfold profileZerothMoment quarticBasePoleOrthogonalProfile
  have h1 := quarticWitnessNormalizedProfile_zeroth_zero W1
  have h2 := quarticWitnessNormalizedProfile_zeroth_zero W2
  have h3 := quarticWitnessNormalizedProfile_zeroth_zero W3
  have i1 :
      Integrable (quarticWitnessNormalizedProfile W1) :=
    (quarticWitnessNormalizedProfile_continuous W1)
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W1)
  have i2 :
      Integrable (quarticWitnessNormalizedProfile W2) :=
    (quarticWitnessNormalizedProfile_continuous W2)
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W2)
  have i3 :
      Integrable (quarticWitnessNormalizedProfile W3) :=
    (quarticWitnessNormalizedProfile_continuous W3)
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W3)
  rw [integral_add
      ((i1.const_mul _).add (i2.const_mul _))
      (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul,
      h1,h2,h3]
  ring

theorem quarticBasePoleOrthogonalProfile_second_zero
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileSecondMoment
      (quarticBasePoleOrthogonalProfile W1 W2 W3 t) = 0 := by
  unfold profileSecondMoment quarticBasePoleOrthogonalProfile
  have h1 := quarticWitnessNormalizedProfile_second_zero W1
  have h2 := quarticWitnessNormalizedProfile_second_zero W2
  have h3 := quarticWitnessNormalizedProfile_second_zero W3
  have i1 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W1 u*u^2) :=
    ((quarticWitnessNormalizedProfile_continuous W1).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W1).mul_right
  have i2 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W2 u*u^2) :=
    ((quarticWitnessNormalizedProfile_continuous W2).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W2).mul_right
  have i3 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W3 u*u^2) :=
    ((quarticWitnessNormalizedProfile_continuous W3).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W3).mul_right
  have hpoint :
      (fun u : ℝ =>
        (quarticBasePoleCoeff1 W1 W2 W3 t
            * quarticWitnessNormalizedProfile W1 u
          + quarticBasePoleCoeff2 W1 W2 W3 t
            * quarticWitnessNormalizedProfile W2 u
          + quarticBasePoleCoeff3 W1 W2 W3 t
            * quarticWitnessNormalizedProfile W3 u)*u^2)
        =
      fun u =>
        quarticBasePoleCoeff1 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W1 u*u^2)
        +quarticBasePoleCoeff2 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W2 u*u^2)
        +quarticBasePoleCoeff3 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W3 u*u^2) := by
    funext u
    ring
  rw [hpoint,
      integral_add ((i1.const_mul _).add (i2.const_mul _))
        (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul,
      h1,h2,h3]
  ring

theorem quarticBasePoleOrthogonalProfile_fourth
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileFourthMoment
      (quarticBasePoleOrthogonalProfile W1 W2 W3 t)
      = 4 * quarticBasePoleTargetDet W1 W2 W3 t := by
  unfold profileFourthMoment quarticBasePoleOrthogonalProfile
    quarticBasePoleTargetDet
  have i1 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W1 u*u^4) :=
    ((quarticWitnessNormalizedProfile_continuous W1).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W1).mul_right
  have i2 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W2 u*u^4) :=
    ((quarticWitnessNormalizedProfile_continuous W2).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W2).mul_right
  have i3 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W3 u*u^4) :=
    ((quarticWitnessNormalizedProfile_continuous W3).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W3).mul_right
  have hpoint :
      (fun u : ℝ =>
        (quarticBasePoleCoeff1 W1 W2 W3 t
            *quarticWitnessNormalizedProfile W1 u
          +quarticBasePoleCoeff2 W1 W2 W3 t
            *quarticWitnessNormalizedProfile W2 u
          +quarticBasePoleCoeff3 W1 W2 W3 t
            *quarticWitnessNormalizedProfile W3 u)*u^4)
        =
      fun u =>
        quarticBasePoleCoeff1 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W1 u*u^4)
        +quarticBasePoleCoeff2 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W2 u*u^4)
        +quarticBasePoleCoeff3 W1 W2 W3 t
          *(quarticWitnessNormalizedProfile W3 u*u^4) := by
    funext u
    ring
  rw [hpoint,
      integral_add ((i1.const_mul _).add (i2.const_mul _))
        (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul,
      quarticWitnessNormalizedProfile_fourth W1,
      quarticWitnessNormalizedProfile_fourth W2,
      quarticWitnessNormalizedProfile_fourth W3]
  ring

end Synthesis
