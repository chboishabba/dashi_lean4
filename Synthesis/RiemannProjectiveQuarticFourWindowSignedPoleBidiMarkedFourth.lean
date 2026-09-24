import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds
import RiemannAnalytic.TwistedPrimeMoments

/-!
# Bidi marked fourth-angular bridge for the quartic signed-pole RH lane

This module implements the two Clay-facing algebraic recuts suggested by the
current fourth-harmonic frontier.

1.  Centre the local fourth-angular zero statistic against the literal smooth
    Riemann--von Mangoldt vertical fourth moment.

2.  Reconstruct the fourth angular phase from even marked pair-difference
    moments relative to a target zero and its horizontal reflection.

The second identity is the useful bidi bridge to Montgomery-type machinery.
If the target has horizontal displacement A and a local zero has coordinates

  z = a + i*delta,

then the two pair-difference coordinates are

  z_- = (a-A) + i*delta,
  z_+ = (a+A) + i*delta.

Writing P2(x,y)=Re(x+iy)^2 and P4(x,y)=Re(x+iy)^4,

  P4(a,delta)
    = 1/2 * (P4(a-A,delta) + P4(a+A,delta))
      - 3*A^2 * (P2(a-A,delta) + P2(a+A,delta))
      + 5*A^4.

Thus odd marked moments are not needed: orders 0, 2 and 4 around the target
and its functional-equation reflection reconstruct the exact local fourth
angular coordinate.

No pair-correlation estimate is assumed here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def quarticSignedPoleSecondPhaseReal
    (a delta : ℝ) : ℝ :=
  a^2 - delta^2

def quarticSignedPoleTargetReflectionSecondPairMark
    (t A : ℝ) (rho : Zeros) : ℝ :=
  quarticSignedPoleSecondPhaseReal
      (heightOf rho - A) ((rho : ℂ).im - t)
    +
  quarticSignedPoleSecondPhaseReal
      (heightOf rho + A) ((rho : ℂ).im - t)

def quarticSignedPoleTargetReflectionFourthPairMark
    (t A : ℝ) (rho : Zeros) : ℝ :=
  quarticSignedPoleFourthPhaseReal
      (heightOf rho - A) ((rho : ℂ).im - t)
    +
  quarticSignedPoleFourthPhaseReal
      (heightOf rho + A) ((rho : ℂ).im - t)

/--
Bidi target/reflection reconstruction of the fourth angular phase.

Only the even second and fourth pair-difference marks are required.
-/
theorem quarticSignedPoleFourthPhaseReal_eq_bidi_target_reflection
    (A a delta : ℝ) :
    quarticSignedPoleFourthPhaseReal a delta
      =
    (1/2 : ℝ) *
      (quarticSignedPoleFourthPhaseReal (a-A) delta
        + quarticSignedPoleFourthPhaseReal (a+A) delta)
      -
    3 * A^2 *
      (quarticSignedPoleSecondPhaseReal (a-A) delta
        + quarticSignedPoleSecondPhaseReal (a+A) delta)
      +
    5 * A^4 := by
  unfold quarticSignedPoleFourthPhaseReal
    quarticSignedPoleSecondPhaseReal
  ring

theorem quarticSignedPolePhysicalFourthPhaseReal_eq_bidi_target_reflection
    (t A : ℝ) (rho : Zeros) :
    quarticSignedPolePhysicalFourthPhaseReal t rho
      =
    (1/2 : ℝ) *
      quarticSignedPoleTargetReflectionFourthPairMark t A rho
      -
    3 * A^2 *
      quarticSignedPoleTargetReflectionSecondPairMark t A rho
      +
    5 * A^4 := by
  unfold quarticSignedPolePhysicalFourthPhaseReal
    quarticSignedPoleTargetReflectionFourthPairMark
    quarticSignedPoleTargetReflectionSecondPairMark
    quarticSignedPoleFourthPhaseReal
    quarticSignedPoleSecondPhaseReal
  ring

/--
Multiplicity mass of the literal local off-ordinate zero cloud.
-/
def QuarticFourSignedPolePair.literalLocalMarkedMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalMarkedSecondPairMomentAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * quarticSignedPoleTargetReflectionSecondPairMark t A rho
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalMarkedFourthPairMomentAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * quarticSignedPoleTargetReflectionFourthPairMark t A rho
        else
          0
      else
        0

/--
Finite same-object version of the bidi reconstruction.

The local fourth angular moment is exactly a linear combination of the
0th, 2nd and 4th target/reflection marked pair moments.
-/
theorem QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt_eq_bidi_marked
    {t eta A : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthPhaseMomentAt eta n
      =
    (1/2 : ℝ) *
      W.literalLocalMarkedFourthPairMomentAt eta A n
      -
    3 * A^2 *
      W.literalLocalMarkedSecondPairMomentAt eta A n
      +
    5 * A^4 *
      W.literalLocalMarkedMassAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
    QuarticFourSignedPolePair.literalLocalMarkedFourthPairMomentAt
    QuarticFourSignedPolePair.literalLocalMarkedSecondPairMomentAt
    QuarticFourSignedPolePair.literalLocalMarkedMassAt
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl, hoff]
      rw [quarticSignedPolePhysicalFourthPhaseReal_eq_bidi_target_reflection
        t A rho]
      ring
    · simp [hl, hoff]
  · simp [hl]

/-!
## Smooth-mu centering of the fourth angular statistic
-/

def quarticSignedPoleLocalMuVerticalFourthMoment
    (t eta : ℝ) : ℝ :=
  ∫ x in
      Set.Icc (t - eta * (t/16)) (t + eta * (t/16)),
    (x-t)^4 * Zeta23.mu x

def QuarticFourSignedPolePair.literalLocalVerticalFourthZeroMomentAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * ((rho : ℂ).im-t)^4
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * heightOf rho^2
            * (heightOf rho^2 - 6 * ((rho : ℂ).im-t)^2)
        else
          0
      else
        0

theorem quarticSignedPolePhysicalFourthPhaseReal_eq_vertical_add_horizontal
    (t : ℝ) (rho : Zeros) :
    quarticSignedPolePhysicalFourthPhaseReal t rho
      =
    ((rho : ℂ).im-t)^4
      +
    heightOf rho^2
      * (heightOf rho^2 - 6 * ((rho : ℂ).im-t)^2) := by
  unfold quarticSignedPolePhysicalFourthPhaseReal
  ring

theorem QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt_eq_vertical_add_horizontal
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthPhaseMomentAt eta n
      =
    W.literalLocalVerticalFourthZeroMomentAt eta n
      +
    W.literalLocalHorizontalFourthCorrectionAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
    QuarticFourSignedPolePair.literalLocalVerticalFourthZeroMomentAt
    QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl, hoff]
      rw [quarticSignedPolePhysicalFourthPhaseReal_eq_vertical_add_horizontal]
      ring
    · simp [hl, hoff]
  · simp [hl]

def QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalLocalFourthPhaseMomentAt eta n
    - quarticSignedPoleLocalMuVerticalFourthMoment t eta

theorem QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt_eq
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalCenteredFourthAngularAt eta n
      =
    (W.literalLocalVerticalFourthZeroMomentAt eta n
      - quarticSignedPoleLocalMuVerticalFourthMoment t eta)
      +
    W.literalLocalHorizontalFourthCorrectionAt eta n := by
  unfold QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt
  rw [W.literalLocalFourthPhaseMomentAt_eq_vertical_add_horizontal]
  ring


/-!
## The universal 0/2/4 bidi angular operator
-/

def quarticSignedPoleBidiAngularOperator
    (A M0 M2 M4 : ℝ) : ℝ :=
  (1/2 : ℝ) * M4 - 3 * A^2 * M2 + 5 * A^4 * M0

theorem quarticSignedPoleFourthPhaseReal_eq_bidi_operator
    (A a delta : ℝ) :
    quarticSignedPoleFourthPhaseReal a delta
      =
    quarticSignedPoleBidiAngularOperator A 1
      (quarticSignedPoleSecondPhaseReal (a-A) delta
        + quarticSignedPoleSecondPhaseReal (a+A) delta)
      (quarticSignedPoleFourthPhaseReal (a-A) delta
        + quarticSignedPoleFourthPhaseReal (a+A) delta) := by
  rw [quarticSignedPoleFourthPhaseReal_eq_bidi_target_reflection]
  rfl

/--
The smooth critical-line background is governed by exactly the same bidi
operator: put a=0 and the physical fourth phase is delta^4.
-/
theorem quarticSignedPoleVerticalFourth_eq_bidi_operator
    (A delta : ℝ) :
    delta^4
      =
    quarticSignedPoleBidiAngularOperator A 1
      (quarticSignedPoleSecondPhaseReal (-A) delta
        + quarticSignedPoleSecondPhaseReal A delta)
      (quarticSignedPoleFourthPhaseReal (-A) delta
        + quarticSignedPoleFourthPhaseReal A delta) := by
  have h :=
    quarticSignedPoleFourthPhaseReal_eq_bidi_operator A 0 delta
  simpa [quarticSignedPoleFourthPhaseReal] using h

theorem QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt_eq_bidi_operator
    {t eta A : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalFourthPhaseMomentAt eta n
      =
    quarticSignedPoleBidiAngularOperator A
      (W.literalLocalMarkedMassAt eta n)
      (W.literalLocalMarkedSecondPairMomentAt eta A n)
      (W.literalLocalMarkedFourthPairMomentAt eta A n) := by
  rw [W.literalLocalFourthPhaseMomentAt_eq_bidi_marked]
  rfl


/-!
## Localized bidi 0/2/4 discrepancy jet

The fourth-angular statistic factors through three even marked coordinates.
Package the zero and smooth-mu sides separately so the next analytic theorem
has an exact producer/consumer boundary.

No prime-side estimate is assumed in this section.
-/

def quarticSignedPoleLocalMuMarkedMass
    (t eta : ℝ) : ℝ :=
  ∫ x in
      Set.Icc (t - eta * (t/16)) (t + eta * (t/16)),
    Zeta23.mu x

def quarticSignedPoleLocalMuMarkedSecondPairMoment
    (t eta A : ℝ) : ℝ :=
  ∫ x in
      Set.Icc (t - eta * (t/16)) (t + eta * (t/16)),
    (quarticSignedPoleSecondPhaseReal (-A) (x-t)
      + quarticSignedPoleSecondPhaseReal A (x-t))
      * Zeta23.mu x

def quarticSignedPoleLocalMuMarkedFourthPairMoment
    (t eta A : ℝ) : ℝ :=
  ∫ x in
      Set.Icc (t - eta * (t/16)) (t + eta * (t/16)),
    (quarticSignedPoleFourthPhaseReal (-A) (x-t)
      + quarticSignedPoleFourthPhaseReal A (x-t))
      * Zeta23.mu x

structure QuarticSignedPoleBidiMarkedJet where
  m0 : ℝ
  m2 : ℝ
  m4 : ℝ

def QuarticFourSignedPolePair.literalLocalZeroBidiMarkedJetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) (n : ℕ) : QuarticSignedPoleBidiMarkedJet where
  m0 := W.literalLocalMarkedMassAt eta n
  m2 := W.literalLocalMarkedSecondPairMomentAt eta A n
  m4 := W.literalLocalMarkedFourthPairMomentAt eta A n

def quarticSignedPoleLocalMuBidiMarkedJet
    (t eta A : ℝ) : QuarticSignedPoleBidiMarkedJet where
  m0 := quarticSignedPoleLocalMuMarkedMass t eta
  m2 := quarticSignedPoleLocalMuMarkedSecondPairMoment t eta A
  m4 := quarticSignedPoleLocalMuMarkedFourthPairMoment t eta A

def QuarticSignedPoleBidiMarkedJet.sub
    (X Y : QuarticSignedPoleBidiMarkedJet) :
    QuarticSignedPoleBidiMarkedJet where
  m0 := X.m0 - Y.m0
  m2 := X.m2 - Y.m2
  m4 := X.m4 - Y.m4

def QuarticSignedPoleBidiMarkedJet.angular
    (A : ℝ) (J : QuarticSignedPoleBidiMarkedJet) : ℝ :=
  quarticSignedPoleBidiAngularOperator A J.m0 J.m2 J.m4

def QuarticFourSignedPolePair.literalLocalCenteredBidiMarkedJetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) (n : ℕ) : QuarticSignedPoleBidiMarkedJet :=
  (W.literalLocalZeroBidiMarkedJetAt eta A n).sub
    (quarticSignedPoleLocalMuBidiMarkedJet t eta A)

theorem quarticSignedPoleLocalMuVerticalFourthMoment_eq_bidi_operator
    (t eta A : ℝ) :
    quarticSignedPoleLocalMuVerticalFourthMoment t eta
      =
    quarticSignedPoleBidiAngularOperator A
      (quarticSignedPoleLocalMuMarkedMass t eta)
      (quarticSignedPoleLocalMuMarkedSecondPairMoment t eta A)
      (quarticSignedPoleLocalMuMarkedFourthPairMoment t eta A) := by
  let K : Set ℝ :=
    Set.Icc (t - eta * (t/16)) (t + eta * (t/16))
  let f0 : ℝ → ℝ := fun x => Zeta23.mu x
  let f2 : ℝ → ℝ := fun x =>
    (quarticSignedPoleSecondPhaseReal (-A) (x-t)
      + quarticSignedPoleSecondPhaseReal A (x-t))
      * Zeta23.mu x
  let f4 : ℝ → ℝ := fun x =>
    (quarticSignedPoleFourthPhaseReal (-A) (x-t)
      + quarticSignedPoleFourthPhaseReal A (x-t))
      * Zeta23.mu x
  have hmu : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  have h0 : IntegrableOn f0 K := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      hmu.continuousOn
  have h2 : IntegrableOn f2 K := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc (by
      dsimp [f2]
      fun_prop)
  have h4 : IntegrableOn f4 K := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc (by
      dsimp [f4]
      fun_prop)
  have hpoint :
      (fun x : ℝ => (x-t)^4 * Zeta23.mu x)
        =
      fun x =>
        ((1/2 : ℝ) * f4 x
          - 3 * A^2 * f2 x
          + 5 * A^4 * f0 x) := by
    funext x
    have h :=
      quarticSignedPoleVerticalFourth_eq_bidi_operator A (x-t)
    unfold quarticSignedPoleBidiAngularOperator at h
    dsimp [f0, f2, f4]
    rw [h]
    ring
  unfold quarticSignedPoleLocalMuVerticalFourthMoment
    quarticSignedPoleLocalMuMarkedMass
    quarticSignedPoleLocalMuMarkedSecondPairMoment
    quarticSignedPoleLocalMuMarkedFourthPairMoment
    quarticSignedPoleBidiAngularOperator
  change (∫ x in K, (x-t)^4 * Zeta23.mu x)
      =
    (1/2 : ℝ) * (∫ x in K, f4 x)
      - 3 * A^2 * (∫ x in K, f2 x)
      + 5 * A^4 * (∫ x in K, f0 x)
  rw [hpoint]
  rw [integral_add
      ((h4.const_mul (1/2 : ℝ)).sub (h2.const_mul (3*A^2)))
      (h0.const_mul (5*A^4))]
  rw [integral_sub
      (h4.const_mul (1/2 : ℝ))
      (h2.const_mul (3*A^2))]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]

/--
The centred fourth-angular statistic is exactly the universal bidi operator
applied to the localized zero-minus-mu 0/2/4 discrepancy jet.
-/
theorem QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt_eq_bidi_discrepancy
    {t eta A : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalCenteredFourthAngularAt eta n
      =
    (W.literalLocalCenteredBidiMarkedJetAt eta A n).angular A := by
  unfold QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt
    QuarticFourSignedPolePair.literalLocalCenteredBidiMarkedJetAt
    QuarticSignedPoleBidiMarkedJet.angular
    QuarticSignedPoleBidiMarkedJet.sub
    QuarticFourSignedPolePair.literalLocalZeroBidiMarkedJetAt
    quarticSignedPoleLocalMuBidiMarkedJet
  rw [W.literalLocalFourthPhaseMomentAt_eq_bidi_operator]
  rw [quarticSignedPoleLocalMuVerticalFourthMoment_eq_bidi_operator]
  unfold quarticSignedPoleBidiAngularOperator
  ring

/-!
## Producer boundary

Any localized explicit-formula / prime theorem only needs to control this
three-coordinate discrepancy jet.  The RH consumer does not require odd
marked moments.
-/

def QuarticFourSignedPolePair.LocalizedBidiMarkedProducer
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) : Prop :=
  ∃ J : ℕ → QuarticSignedPoleBidiMarkedJet,
    ∀ n : ℕ,
      J n = W.literalLocalCenteredBidiMarkedJetAt eta A n

theorem QuarticFourSignedPolePair.localizedBidiMarkedProducer_exact
    {t eta A : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.LocalizedBidiMarkedProducer eta A := by
  refine ⟨fun n => W.literalLocalCenteredBidiMarkedJetAt eta A n, ?_⟩
  intro n
  rfl

/--
A prospective prime-side theorem may supply bounds coordinatewise; the only
combination consumed by the RH lane is the angular operator.
-/
theorem QuarticSignedPoleBidiMarkedJet.angular_sub
    (A : ℝ) (X Y : QuarticSignedPoleBidiMarkedJet) :
    (X.sub Y).angular A
      =
    X.angular A - Y.angular A := by
  unfold QuarticSignedPoleBidiMarkedJet.sub
    QuarticSignedPoleBidiMarkedJet.angular
    quarticSignedPoleBidiAngularOperator
  ring


/-!
## Arithmetic bidi jet from the literal cosh-twisted von Mangoldt moments

The target/reflection symmetrization on the prime side naturally produces the
cosh twist already owned by RiemannAnalytic.TwistedPrimeMoments.  Package its
even 0/2/4 moments in the same jet carrier used by the local zero-minus-mu
consumer.
-/

def quarticSignedPolePrimeBidiMarkedJet
    (N : ℕ) (A : ℝ) : QuarticSignedPoleBidiMarkedJet where
  m0 := RiemannAnalytic.twistedMoment N A 0
  m2 := RiemannAnalytic.twistedMoment N A 2
  m4 := RiemannAnalytic.twistedMoment N A 4

def quarticSignedPolePrimeAngularPolynomial
    (A x : ℝ) : ℝ :=
  (1/2 : ℝ) * x^4 - 3 * A^2 * x^2 + 5 * A^4

theorem quarticSignedPolePrimeAngularPolynomial_sq
    (A x : ℝ) :
    quarticSignedPolePrimeAngularPolynomial A x
      =
    (1/2 : ℝ) * (x^2 - 3*A^2)^2
      + (1/2 : ℝ) * A^4 := by
  unfold quarticSignedPolePrimeAngularPolynomial
  ring

theorem quarticSignedPolePrimeAngularPolynomial_nonneg
    (A x : ℝ) :
    0 <= quarticSignedPolePrimeAngularPolynomial A x := by
  rw [quarticSignedPolePrimeAngularPolynomial_sq]
  positivity

theorem quarticSignedPolePrimeAngularPolynomial_pos_of_A_ne_zero
    {A x : ℝ}
    (hA : A ≠ 0) :
    0 < quarticSignedPolePrimeAngularPolynomial A x := by
  rw [quarticSignedPolePrimeAngularPolynomial_sq]
  have hA4 : 0 < A^4 := by positivity
  nlinarith [sq_nonneg (x^2 - 3*A^2)]

theorem quarticSignedPolePrimeBidiAngular_eq_sum
    (N : ℕ) (A : ℝ) :
    (quarticSignedPolePrimeBidiMarkedJet N A).angular A
      =
    ∑ n ∈ Finset.Icc 1 N,
      RiemannAnalytic.coshVonMangoldt A n
        * quarticSignedPolePrimeAngularPolynomial A (Real.log n) := by
  unfold quarticSignedPolePrimeBidiMarkedJet
    QuarticSignedPoleBidiMarkedJet.angular
    quarticSignedPoleBidiAngularOperator
    RiemannAnalytic.twistedMoment
    quarticSignedPolePrimeAngularPolynomial
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem quarticSignedPolePrimeBidiAngular_nonneg
    (N : ℕ) (A : ℝ) :
    0 <= (quarticSignedPolePrimeBidiMarkedJet N A).angular A := by
  rw [quarticSignedPolePrimeBidiAngular_eq_sum]
  exact Finset.sum_nonneg fun n hn => by
    exact mul_nonneg
      (RiemannAnalytic.coshVonMangoldt_nonneg A n)
      (quarticSignedPolePrimeAngularPolynomial_nonneg A (Real.log n))

/--
A useful exact coercive lower bound: the angular prime polynomial retains the
pure A^4 floor pointwise.
-/
theorem quarticSignedPolePrimeAngularPolynomial_ge_half_A4
    (A x : ℝ) :
    (1/2 : ℝ) * A^4
      <= quarticSignedPolePrimeAngularPolynomial A x := by
  rw [quarticSignedPolePrimeAngularPolynomial_sq]
  nlinarith [sq_nonneg (x^2 - 3*A^2)]

theorem quarticSignedPolePrimeBidiAngular_ge_half_A4_mass
    (N : ℕ) (A : ℝ) :
    (1/2 : ℝ) * A^4 * RiemannAnalytic.twistedMoment N A 0
      <=
    (quarticSignedPolePrimeBidiMarkedJet N A).angular A := by
  rw [quarticSignedPolePrimeBidiAngular_eq_sum]
  rw [RiemannAnalytic.twistedMoment_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hw := RiemannAnalytic.coshVonMangoldt_nonneg A n
  have hp :=
    quarticSignedPolePrimeAngularPolynomial_ge_half_A4
      A (Real.log n)
  nlinarith

/-!
## Explicit-formula normalization seam

At this point the arithmetic sign is no longer open: the literal cosh-twisted
prime 0/2/4 angular combination is nonnegative and in fact carries an A^4
mass floor.  The remaining analytic seam is the same-object localized explicit
formula identifying the centred zero-minus-mu bidi jet with the correctly
normalized prime bidi jet plus the already-explicit archimedean/boundary terms.
-/

def QuarticFourSignedPolePair.LocalizedBidiPrimeRepresentation
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta A : ℝ) : Prop :=
  ∃ cPrime : ℝ, ∃ primeCutoff : ℕ,
    ∀ n : ℕ,
      n >= primeCutoff ->
      (W.literalLocalCenteredBidiMarkedJetAt eta A n).angular A
        =
      cPrime * (quarticSignedPolePrimeBidiMarkedJet n A).angular A

/--
If the eventual localized explicit-formula representation has a nonpositive
prime coefficient, the arithmetic positivity immediately forces a favorable
(nonpositive) centred fourth-angular contribution.
-/
theorem QuarticFourSignedPolePair.centeredBidiAngular_nonpos_of_primeRepresentation
    {t eta A cPrime : ℝ}
    (W : QuarticFourSignedPolePair t)
    {N : ℕ}
    (hrep :
      (W.literalLocalCenteredBidiMarkedJetAt eta A N).angular A
        =
      cPrime * (quarticSignedPolePrimeBidiMarkedJet N A).angular A)
    (hc : cPrime <= 0) :
    (W.literalLocalCenteredBidiMarkedJetAt eta A N).angular A <= 0 := by
  rw [hrep]
  exact mul_nonpos_of_nonpos_of_nonneg
    hc (quarticSignedPolePrimeBidiAngular_nonneg N A)


/-!
## Literal Weil-normalized bidi prime jet

The actual zeta explicit formula carries a square-root denominator and the
target/reflection pair carries the hyperbolic twist at parameter A, not 2A.
Reuse the existing cosh von-Mangoldt carrier at half-parameter and keep the
n^(-1/2) factor explicit.
-/

noncomputable def quarticSignedPoleLiteralWeilPrimeWeight
    (A : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^(-(1/2 : ℝ))
    * RiemannAnalytic.coshVonMangoldt (A/2) n

noncomputable def quarticSignedPoleLiteralWeilPrimeMoment
    (N : ℕ) (A : ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    quarticSignedPoleLiteralWeilPrimeWeight A n
      * (Real.log n)^r

def quarticSignedPoleLiteralWeilPrimeBidiJet
    (N : ℕ) (A : ℝ) : QuarticSignedPoleBidiMarkedJet where
  m0 := quarticSignedPoleLiteralWeilPrimeMoment N A 0
  m2 := quarticSignedPoleLiteralWeilPrimeMoment N A 2
  m4 := quarticSignedPoleLiteralWeilPrimeMoment N A 4

theorem quarticSignedPoleLiteralWeilPrimeWeight_nonneg
    (A : ℝ) (n : ℕ) :
    0 <= quarticSignedPoleLiteralWeilPrimeWeight A n := by
  unfold quarticSignedPoleLiteralWeilPrimeWeight
  exact mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (RiemannAnalytic.coshVonMangoldt_nonneg (A/2) n)

theorem quarticSignedPoleLiteralWeilPrimeBidiAngular_eq_sum
    (N : ℕ) (A : ℝ) :
    (quarticSignedPoleLiteralWeilPrimeBidiJet N A).angular A
      =
    ∑ n ∈ Finset.Icc 1 N,
      quarticSignedPoleLiteralWeilPrimeWeight A n
        * quarticSignedPolePrimeAngularPolynomial A (Real.log n) := by
  unfold quarticSignedPoleLiteralWeilPrimeBidiJet
    quarticSignedPoleLiteralWeilPrimeMoment
    QuarticSignedPoleBidiMarkedJet.angular
    quarticSignedPoleBidiAngularOperator
    quarticSignedPolePrimeAngularPolynomial
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem quarticSignedPoleLiteralWeilPrimeBidiAngular_nonneg
    (N : ℕ) (A : ℝ) :
    0 <= (quarticSignedPoleLiteralWeilPrimeBidiJet N A).angular A := by
  rw [quarticSignedPoleLiteralWeilPrimeBidiAngular_eq_sum]
  exact Finset.sum_nonneg fun n hn => by
    exact mul_nonneg
      (quarticSignedPoleLiteralWeilPrimeWeight_nonneg A n)
      (quarticSignedPolePrimeAngularPolynomial_nonneg A (Real.log n))

theorem quarticSignedPoleLiteralWeilPrimeBidiAngular_ge_half_A4_mass
    (N : ℕ) (A : ℝ) :
    (1/2 : ℝ) * A^4
        * quarticSignedPoleLiteralWeilPrimeMoment N A 0
      <=
    (quarticSignedPoleLiteralWeilPrimeBidiJet N A).angular A := by
  rw [quarticSignedPoleLiteralWeilPrimeBidiAngular_eq_sum]
  unfold quarticSignedPoleLiteralWeilPrimeMoment
  simp only [pow_zero, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hw := quarticSignedPoleLiteralWeilPrimeWeight_nonneg A n
  have hp :=
    quarticSignedPolePrimeAngularPolynomial_ge_half_A4
      A (Real.log n)
  nlinarith

/--
Exact functional-equation tilt split of the literal square-root-normalized
prime weight.  This is the analytic domain split that the old unnormalized
twisted-moment theorem does not see.
-/
theorem quarticSignedPoleLiteralWeilPrimeWeight_eq_two_tilts
    {A : ℝ} {n : ℕ} (hn : 1 <= n) :
    quarticSignedPoleLiteralWeilPrimeWeight A n
      =
    (1/2 : ℝ) *
      ((n : ℝ)^(-(1/2 : ℝ))
        * (RiemannAnalytic.coshVonMangoldt (A/2) n * 2)) := by
  ring

/--
At the exponent level the literal target/reflection weight consists of the two
branches A-1/2 and -A-1/2.  The equality is stated after dividing out the
nonnegative von-Mangoldt coefficient so it can be reused by prime-moment
estimates independently of notation for Lambda.
-/
theorem quarticSignedPoleLiteralCoshRpow_split
    {A : ℝ} {n : ℕ} (hn : 1 <= n) :
    (n : ℝ)^(-(1/2 : ℝ)) * Real.cosh (A * Real.log n)
      =
    (1/2 : ℝ) *
      ((n : ℝ)^(A-(1/2 : ℝ))
        + (n : ℝ)^(-A-(1/2 : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.cosh_eq]
  have hA :
      Real.exp (A * Real.log n) = (n : ℝ)^A := by
    rw [Real.rpow_def_of_pos hn0]
  have hnA :
      Real.exp (-(A * Real.log n)) = (n : ℝ)^(-A) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [hA, hnA]
  have h1 :
      (n : ℝ)^(-(1/2 : ℝ)) * (n : ℝ)^A
        = (n : ℝ)^(A-(1/2 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have h2 :
      (n : ℝ)^(-(1/2 : ℝ)) * (n : ℝ)^(-A)
        = (n : ℝ)^(-A-(1/2 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [← h1, ← h2]
  ring

theorem quarticSignedPoleLiteralWeilPrimeWeight_eq_tilt_pair
    {A : ℝ} {n : ℕ} (hn : 1 <= n) :
    quarticSignedPoleLiteralWeilPrimeWeight A n
      =
    (1/2 : ℝ) *
      (
        RiemannAnalytic.coshVonMangoldt 0 n
          * (n : ℝ)^(A-(1/2 : ℝ))
        +
        RiemannAnalytic.coshVonMangoldt 0 n
          * (n : ℝ)^(-A-(1/2 : ℝ))
      ) := by
  unfold quarticSignedPoleLiteralWeilPrimeWeight
  rw [RiemannAnalytic.coshVonMangoldt]
  have hcosh0 : Real.cosh (2 * 0 * Real.log n) = 1 := by simp
  rw [hcosh0, mul_one]
  unfold RiemannAnalytic.coshVonMangoldt
  rw [show 2 * (A/2) * Real.log n = A * Real.log n by ring]
  rw [quarticSignedPoleLiteralCoshRpow_split hn]
  ring

/--
The existing positive-tilt block estimate applies directly to the first branch
for A>=0, while the reflected branch lies strictly below the old v=-1/2
endpoint as soon as A>0.
-/
theorem quarticSignedPoleLiteralTiltDomains
    {A : ℝ} (hA0 : 0 <= A) :
    (-(1/2 : ℝ) <= A-(1/2 : ℝ))
      ∧
    (-A-(1/2 : ℝ) <= -(1/2 : ℝ)) := by
  constructor <;> linarith

theorem quarticSignedPoleLiteralReflectedTilt_below_old_endpoint
    {A : ℝ} (hA : 0 < A) :
    -A-(1/2 : ℝ) < -(1/2 : ℝ) := by
  linarith

end Synthesis
