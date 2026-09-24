import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds
import Synthesis.RiemannProjectiveQuarticFourWindowHighWitness
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
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


/-!
## Literal prime mass scale

The square-root-normalized cosh mass is exactly the average of the two
functional-equation tilts.  A lower bound only needs the forward branch; the
reflected branch is nonnegative.
-/

theorem quarticSignedPoleLiteralWeilPrimeMass_eq_tilt_pair
    (N : ℕ) (A : ℝ) :
    quarticSignedPoleLiteralWeilPrimeMoment N A 0
      =
    (RiemannAnalytic.tiltedMass N (A-(1/2 : ℝ))
      + RiemannAnalytic.tiltedMass N (-A-(1/2 : ℝ))) / 2 := by
  unfold quarticSignedPoleLiteralWeilPrimeMoment
    RiemannAnalytic.tiltedMass
  simp only [pow_zero, mul_one]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 <= n := (Finset.mem_Icc.mp hn).1
  have hsplit :=
    quarticSignedPoleLiteralWeilPrimeWeight_eq_tilt_pair
      (A:=A) hn1
  simpa [RiemannAnalytic.coshVonMangoldt] using hsplit

theorem quarticSignedPoleLiteralWeilPrimeMass_lower
    {N : ℕ} (hN : (10 : ℝ)^8 <= (N : ℝ))
    {A : ℝ} (hA0 : 0 <= A) (hAhalf : A < 1/2) :
    (N : ℝ)^((1/2 : ℝ)+A) / 32
      <= quarticSignedPoleLiteralWeilPrimeMoment N A 0 := by
  rw [quarticSignedPoleLiteralWeilPrimeMass_eq_tilt_pair]
  have hvabs : |A-(1/2 : ℝ)| <= 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hf :=
    RiemannAnalytic.tiltedMass_lower
      (N:=N) hN (v:=A-(1/2 : ℝ)) hvabs
  have hr :
      0 <= RiemannAnalytic.tiltedMass N (-A-(1/2 : ℝ)) :=
    RiemannAnalytic.tiltedMass_nonneg _ _
  have hexp :
      (1 + (A-(1/2 : ℝ)) : ℝ) = (1/2 : ℝ) + A := by
    ring
  rw [hexp] at hf
  linarith

theorem quarticSignedPoleLiteralWeilPrimeBidiAngular_coercive
    {N : ℕ} (hN : (10 : ℝ)^8 <= (N : ℝ))
    {A : ℝ} (hA0 : 0 <= A) (hAhalf : A < 1/2) :
    A^4 * (N : ℝ)^((1/2 : ℝ)+A) / 64
      <=
    (quarticSignedPoleLiteralWeilPrimeBidiJet N A).angular A := by
  have hmass :=
    quarticSignedPoleLiteralWeilPrimeMass_lower
      (N:=N) hN hA0 hAhalf
  have hang :=
    quarticSignedPoleLiteralWeilPrimeBidiAngular_ge_half_A4_mass
      N A
  have hfac : 0 <= (1/2 : ℝ) * A^4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmass hfac
  calc
    A^4 * (N : ℝ)^((1/2 : ℝ)+A) / 64
        <=
      (1/2 : ℝ) * A^4
        * quarticSignedPoleLiteralWeilPrimeMoment N A 0 := by
          nlinarith [hscaled]
    _ <=
      (quarticSignedPoleLiteralWeilPrimeBidiJet N A).angular A := hang


/-!
## Bidi cosh-marking of the actual short four-window detector

Horizontal target/reflection marking is multiplication by cosh(Au) in the
physical test variable.  It preserves support exactly, hence preserves literal
prime invisibility.
-/

def quarticSignedPoleCoshMarkedDetector
    (g : ℝ → ℝ) (A : ℝ) : ℝ → ℝ :=
  fun u => g u * Real.cosh (A*u)

theorem quarticSignedPoleCoshMarkedDetector_zero
    (g : ℝ → ℝ) :
    quarticSignedPoleCoshMarkedDetector g 0 = g := by
  funext u
  simp [quarticSignedPoleCoshMarkedDetector]

theorem quarticSignedPoleCoshMarkedDetector_neg
    (g : ℝ → ℝ) (A : ℝ) :
    quarticSignedPoleCoshMarkedDetector g (-A)
      = quarticSignedPoleCoshMarkedDetector g A := by
  funext u
  simp [quarticSignedPoleCoshMarkedDetector]

theorem quarticSignedPoleCoshMarkedDetector_short
    {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2)
    (A : ℝ) :
    ∀ u, quarticSignedPoleCoshMarkedDetector g A u ≠ 0 ->
      |u| < Real.log 2 := by
  intro u hu
  apply hshort u
  intro hg
  simp [quarticSignedPoleCoshMarkedDetector, hg] at hu

theorem quarticSignedPoleCoshMarkedDetector_even
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (A u : ℝ) :
    quarticSignedPoleCoshMarkedDetector g A (-u)
      = quarticSignedPoleCoshMarkedDetector g A u := by
  simp [quarticSignedPoleCoshMarkedDetector, heven,
    Real.cosh_neg]

theorem quarticSignedPoleCoshMarkedDetector_contDiff
    {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (A : ℝ) :
    ContDiff ℝ 2 (quarticSignedPoleCoshMarkedDetector g A) := by
  unfold quarticSignedPoleCoshMarkedDetector
  fun_prop

theorem quarticSignedPoleCoshMarkedDetector_compact
    {g : ℝ → ℝ}
    (hg : HasCompactSupport g)
    (A : ℝ) :
    HasCompactSupport (quarticSignedPoleCoshMarkedDetector g A) := by
  unfold quarticSignedPoleCoshMarkedDetector
  exact hg.mul_right

def quarticFourBidiMarkedPhysicalDetector
    (R lam mu t A : ℝ) : ℝ → ℝ :=
  quarticSignedPoleCoshMarkedDetector
    (quarticFourPhysicalDetector R lam mu t) A

theorem quarticFourBidiMarkedPhysicalDetector_short
    {R lam mu t A : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 200 <= t) :
    ∀ u, quarticFourBidiMarkedPhysicalDetector R lam mu t A u ≠ 0 ->
      |u| < Real.log 2 := by
  unfold quarticFourBidiMarkedPhysicalDetector
  exact quarticSignedPoleCoshMarkedDetector_short
    (quarticFourPhysicalDetector_short_of_twoHundred
      hR hRone ht) A

theorem quarticFourBidiMarkedPhysicalDetector_primeProjectiveDefect_eq_zero
    {R lam mu t A : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 200 <= t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourBidiMarkedPhysicalDetector R lam mu t A)
      t (t/16)
      = 0 := by
  exact
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect_eq_zero
      (quarticFourBidiMarkedPhysicalDetector_short
        hR hRone ht)
      t (t/16)

/--
The signed two-endpoint pole channel after horizontal bidi marking.
-/
def QuarticFourSignedPolePair.bidiMarkedPoleCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A : ℝ) : ℝ :=
  W.poleTwo *
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourBidiMarkedPhysicalDetector
        W.R (1/2) W.muHalf t A)
      t (t/16)
  +
  (-W.poleHalf) *
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourBidiMarkedPhysicalDetector
        W.R (2/3) W.muTwo t A)
      t (t/16)

theorem QuarticFourSignedPolePair.bidiMarkedPrimeHalf_eq_zero
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (A : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourBidiMarkedPhysicalDetector
        W.R (1/2) W.muHalf t A)
      t (t/16)
      = 0 := by
  exact
    quarticFourBidiMarkedPhysicalDetector_primeProjectiveDefect_eq_zero
      W.Rpos W.RltOne ht

theorem QuarticFourSignedPolePair.bidiMarkedPrimeTwo_eq_zero
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (A : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourBidiMarkedPhysicalDetector
        W.R (2/3) W.muTwo t A)
      t (t/16)
      = 0 := by
  exact
    quarticFourBidiMarkedPhysicalDetector_primeProjectiveDefect_eq_zero
      W.Rpos W.RltOne ht

theorem QuarticFourSignedPolePair.bidiMarkedPoleCombination_even
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (A : ℝ) :
    W.bidiMarkedPoleCombination (-A)
      = W.bidiMarkedPoleCombination A := by
  unfold QuarticFourSignedPolePair.bidiMarkedPoleCombination
  rw [show
      quarticFourBidiMarkedPhysicalDetector
          W.R (1/2) W.muHalf t (-A)
        =
      quarticFourBidiMarkedPhysicalDetector
          W.R (1/2) W.muHalf t A by
        unfold quarticFourBidiMarkedPhysicalDetector
        exact quarticSignedPoleCoshMarkedDetector_neg _ _]
  rw [show
      quarticFourBidiMarkedPhysicalDetector
          W.R (2/3) W.muTwo t (-A)
        =
      quarticFourBidiMarkedPhysicalDetector
          W.R (2/3) W.muTwo t A by
        unfold quarticFourBidiMarkedPhysicalDetector
        exact quarticSignedPoleCoshMarkedDetector_neg _ _]

theorem QuarticFourSignedPolePair.bidiMarkedPoleCombination_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.bidiMarkedPoleCombination 0 = 0 := by
  unfold QuarticFourSignedPolePair.bidiMarkedPoleCombination
    quarticFourBidiMarkedPhysicalDetector
  simp only [quarticSignedPoleCoshMarkedDetector_zero]
  exact W.literalPole_cancel ht


/-!
## Marked-pole quadratic carrier

For the normalized mark m_A(v)=cosh(16*A*v/t), the A^2 Taylor carrier inserts
v^2 into each pole/on-line response.  Factor out the universal positive scalar
(16/t)^2/2 and retain the determinant carrier below.
-/

def quarticFourNormalizedPoleSecondWeight
    (t c v : ℝ) : ℝ :=
  v^2 * quarticFourNormalizedPoleWeight t c v

def quarticFourNormalizedOnLineSecondWeight
    (c v : ℝ) : ℝ :=
  v^2 * quarticFourNormalizedOnLineWeight c v

def quarticFourSmoothMarkedPoleQuadraticCarrier
    (R lam mu t : ℝ) : ℝ :=
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleSecondWeight t 1)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 2)
  +
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 1)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineSecondWeight 2)
  -
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleSecondWeight t 2)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineWeight 1)
  -
  quarticFourWindowPairing R lam mu
      (quarticFourNormalizedPoleWeight t 2)
    * quarticFourWindowPairing R lam mu
      (quarticFourNormalizedOnLineSecondWeight 1)

def quarticFourAtomicMarkedPoleQuadraticCarrier
    (t lam mu : ℝ) : ℝ :=
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleSecondWeight t 1)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 2)
  +
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 1)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineSecondWeight 2)
  -
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleSecondWeight t 2)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineWeight 1)
  -
  quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleWeight t 2)
    * quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineSecondWeight 1)

private theorem bidi_cos_two_pi_div_three :
    Real.cos (2*Real.pi/3) = -1/2 := by
  have harg : 2*Real.pi/3 = Real.pi - Real.pi/3 := by ring
  rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

private theorem bidi_cos_sixteen_pi_div_three :
    Real.cos (16*(Real.pi/3)) = -1/2 := by
  have harg :
      16*(Real.pi/3)
        = (-2*Real.pi/3) + (3:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_neg]
  exact bidi_cos_two_pi_div_three

private theorem bidi_cos_eight_pi :
    Real.cos (16*(Real.pi/2)) = 1 := by
  have harg : 16*(Real.pi/2) = (4:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_nat_mul_two_pi]

private theorem bidi_cos_sixteen_pi :
    Real.cos (16*Real.pi) = 1 := by
  have harg : 16*Real.pi = (8:ℕ) * (2*Real.pi) := by ring
  rw [harg, Real.cos_nat_mul_two_pi]

theorem quarticFourAtomicOnLineSecondPairing_one
    (lam mu : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineSecondWeight 1)
      =
    -(Real.pi^2 * (18*mu + 1) / 18) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedOnLineSecondWeight
    quarticFourNormalizedOnLineWeight
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    one_mul, Real.cos_zero, Real.cos_pi_div_three,
    Real.cos_pi_div_two, Real.cos_pi]
  ring

theorem quarticFourAtomicOnLineSecondPairing_two
    (lam mu : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedOnLineSecondWeight 2)
      =
    -(Real.pi^2 * (9*lam - 36*mu - 2) / 36) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedOnLineSecondWeight
    quarticFourNormalizedOnLineWeight
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    mul_zero, Real.cos_zero]
  rw [show 2*(Real.pi/3)=2*Real.pi/3 by ring,
      bidi_cos_two_pi_div_three,
      show 2*(Real.pi/2)=Real.pi by ring,
      Real.cos_pi,
      Real.cos_two_pi]
  ring

theorem quarticFourAtomicPoleSecondPairing_one
    {t lam mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleSecondWeight t 1)
      =
    -(Real.pi^2 *
      (36*mu*Real.cosh (8*Real.pi/t)
        - Real.cosh (8*Real.pi/(3*t))) / 36) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedPoleSecondWeight
    quarticFourNormalizedPoleWeight
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    mul_zero, zero_div, Real.cosh_zero, Real.cos_zero,
    one_mul, Real.cos_pi_div_three, Real.cos_pi_div_two,
    Real.cos_pi]
  rw [show 8*(Real.pi/3)/t = 8*Real.pi/(3*t) by
        field_simp [ht]; ring,
      bidi_cos_sixteen_pi_div_three,
      bidi_cos_eight_pi,
      bidi_cos_sixteen_pi]
  ring

theorem quarticFourAtomicPoleSecondPairing_two
    {t lam mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicPairingAt lam mu
      (quarticFourNormalizedPoleSecondWeight t 2)
      =
    -(Real.pi^2 *
      (9*lam*Real.cosh (4*Real.pi/t)
        - 36*mu*Real.cosh (8*Real.pi/t)
        + Real.cosh (8*Real.pi/(3*t))) / 36) := by
  unfold quarticFourAtomicPairingAt
    quarticFourNormalizedPoleSecondWeight
    quarticFourNormalizedPoleWeight
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    mul_zero, zero_div, Real.cosh_zero, Real.cos_zero, one_mul]
  rw [show 8*(Real.pi/3)/t = 8*Real.pi/(3*t) by
        field_simp [ht]; ring,
      bidi_cos_sixteen_pi_div_three,
      show 2*(Real.pi/3)=2*Real.pi/3 by ring,
      bidi_cos_two_pi_div_three,
      show 8*(Real.pi/2)/t = 4*Real.pi/t by
        field_simp [ht]; ring,
      bidi_cos_eight_pi,
      show 2*(Real.pi/2)=Real.pi by ring,
      Real.cos_pi,
      bidi_cos_sixteen_pi,
      Real.cos_two_pi]
  ring

theorem quarticFourAtomicMu_half :
    quarticFourAtomicMu (1/2 : ℝ) = -(1/78 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomicMu_twoThird :
    quarticFourAtomicMu (2/3 : ℝ) = (1/162 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_formula
    {t : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (1/2) (quarticFourAtomicMu (1/2))
      =
    Real.pi^2 *
      (39*Real.cosh (8*Real.pi/(3*t))
        + 160*Real.cosh (4*Real.pi/t)
        + 66*Real.cosh (8*Real.pi/t)
        - 148) / 3744 := by
  unfold quarticFourAtomicMarkedPoleQuadraticCarrier
  rw [quarticFourAtomicPoleSecondPairing_one ht,
      quarticFourAtomicPoleSecondPairing_two ht,
      quarticFourAtomicOnLineSecondPairing_one,
      quarticFourAtomicOnLineSecondPairing_two,
      quarticFourAtomicPolePairing_one ht,
      quarticFourAtomicPolePairing_two ht,
      quarticFourAtomicOnLinePairing_one,
      quarticFourAtomicOnLinePairing_two,
      quarticFourAtomicMu_half]
  ring

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_formula
    {t : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (2/3) (quarticFourAtomicMu (2/3))
      =
    Real.pi^2 *
      (-9*Real.cosh (8*Real.pi/(3*t))
        + 80*Real.cosh (4*Real.pi/t)
        - 14*Real.cosh (8*Real.pi/t)
        - 84) / 1944 := by
  unfold quarticFourAtomicMarkedPoleQuadraticCarrier
  rw [quarticFourAtomicPoleSecondPairing_one ht,
      quarticFourAtomicPoleSecondPairing_two ht,
      quarticFourAtomicOnLineSecondPairing_one,
      quarticFourAtomicOnLineSecondPairing_two,
      quarticFourAtomicPolePairing_one ht,
      quarticFourAtomicPolePairing_two ht,
      quarticFourAtomicOnLinePairing_one,
      quarticFourAtomicOnLinePairing_two,
      quarticFourAtomicMu_twoThird]
  ring

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_pos
    {t : ℝ} (ht : t ≠ 0) :
    0 <
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (1/2) (quarticFourAtomicMu (1/2)) := by
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_half_formula ht]
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have h4 := Real.one_le_cosh (4*Real.pi/t)
  have h8 := Real.one_le_cosh (8*Real.pi/t)
  have hp : 0 < Real.pi^2 := by positivity
  positivity
  nlinarith

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_neg
    {t : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (2/3) (quarticFourAtomicMu (2/3)) < 0 := by
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_formula ht]
  let C : ℝ := Real.cosh (4*Real.pi/t)
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have hdouble :
      Real.cosh (8*Real.pi/t) = 2*C^2 - 1 := by
    have harg : 8*Real.pi/t = 2*(4*Real.pi/t) := by ring
    rw [harg, Real.cosh_two_mul, Real.cosh_sq]
    dsimp [C]
    ring
  have hquad :
      -28*C^2 + 80*C - 79 < 0 := by
    have hs : 0 <= (C - 10/7)^2 := sq_nonneg _
    nlinarith
  have hnum :
      -9*Real.cosh (8*Real.pi/(3*t))
        + 80*Real.cosh (4*Real.pi/t)
        - 14*Real.cosh (8*Real.pi/t)
        - 84 < 0 := by
    rw [hdouble]
    dsimp [C] at hquad ⊢
    nlinarith
  have hp : 0 < Real.pi^2 := by positivity
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hp hnum)
    (by norm_num)

def quarticFourAtomicSignedMarkedPoleQuadraticCarrier
    (t : ℝ) : ℝ :=
  quarticFourAtomicFinitePoleResidual
      t (2/3) (quarticFourAtomicMu (2/3))
    *
  quarticFourAtomicMarkedPoleQuadraticCarrier
      t (1/2) (quarticFourAtomicMu (1/2))
  -
  quarticFourAtomicFinitePoleResidual
      t (1/2) (quarticFourAtomicMu (1/2))
    *
  quarticFourAtomicMarkedPoleQuadraticCarrier
      t (2/3) (quarticFourAtomicMu (2/3))

theorem quarticFourAtomicSignedMarkedPoleQuadraticCarrier_pos
    {t : ℝ} (ht : 200 <= t) :
    0 < quarticFourAtomicSignedMarkedPoleQuadraticCarrier t := by
  have hhalfD :=
    quarticFourAtomicFinitePoleResidual_pos_of_twoHundred
      ht (by constructor <;> norm_num)
      (by
        have h :=
          quarticFourAtomicMu_small_on_half_twoThirds
            (by norm_num : (1/2 : ℝ) <= 1/2)
            (by norm_num : (1/2 : ℝ) <= 2/3)
        exact h.trans (by norm_num))
  have htwoD :=
    quarticFourAtomicFinitePoleResidual_pos_of_twoHundred
      ht (by constructor <;> norm_num)
      (by
        have h :=
          quarticFourAtomicMu_small_on_half_twoThirds
            (by norm_num : (1/2 : ℝ) <= 2/3)
            (by norm_num : (2/3 : ℝ) <= 2/3)
        exact h.trans (by norm_num))
  have hhalfQ :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_half_pos
      (by linarith : t ≠ 0)
  have htwoQ :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_neg
      (by linarith : t ≠ 0)
  unfold quarticFourAtomicSignedMarkedPoleQuadraticCarrier
  have h1 :
      0 <
      quarticFourAtomicFinitePoleResidual
          t (2/3) (quarticFourAtomicMu (2/3))
        *
      quarticFourAtomicMarkedPoleQuadraticCarrier
          t (1/2) (quarticFourAtomicMu (1/2)) :=
    mul_pos htwoD hhalfQ
  have h2 :
      quarticFourAtomicFinitePoleResidual
          t (1/2) (quarticFourAtomicMu (1/2))
        *
      quarticFourAtomicMarkedPoleQuadraticCarrier
          t (2/3) (quarticFourAtomicMu (2/3)) < 0 :=
    mul_neg_of_pos_of_neg hhalfD htwoQ
  linarith


/-!
## Uniform atomic marked-pole quadratic signs on the existing mu corridor

The smooth J2 witness only guarantees a small fixed corridor around the atomic
root.  Fortunately the new marked-pole quadratic carrier is affine in mu, with
a uniformly tiny corridor perturbation compared with its endpoint sign
margins.  Thus no stronger mu-selection hypothesis is needed for the bidi
lane.
-/

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_general_formula
    {t mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu
      =
    Real.pi^2 *
      (3*Real.cosh (8*Real.pi/(3*t))
        + 10*Real.cosh (4*Real.pi/t)
        - 4
        + mu *
          (576
            - 180*Real.cosh (4*Real.pi/t)
            - 396*Real.cosh (8*Real.pi/t)))
      / 288 := by
  unfold quarticFourAtomicMarkedPoleQuadraticCarrier
  rw [quarticFourAtomicPoleSecondPairing_one ht,
      quarticFourAtomicPoleSecondPairing_two ht,
      quarticFourAtomicOnLineSecondPairing_one,
      quarticFourAtomicOnLineSecondPairing_two,
      quarticFourAtomicPolePairing_one ht,
      quarticFourAtomicPolePairing_two ht,
      quarticFourAtomicOnLinePairing_one,
      quarticFourAtomicOnLinePairing_two]
  ring

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_general_formula
    {t mu : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu
      =
    Real.pi^2 *
      (-Real.cosh (8*Real.pi/(3*t))
        + 10*Real.cosh (4*Real.pi/t)
        - 12
        + mu *
          (432
            - 180*Real.cosh (4*Real.pi/t)
            - 252*Real.cosh (8*Real.pi/t)))
      / 216 := by
  unfold quarticFourAtomicMarkedPoleQuadraticCarrier
  rw [quarticFourAtomicPoleSecondPairing_one ht,
      quarticFourAtomicPoleSecondPairing_two ht,
      quarticFourAtomicOnLineSecondPairing_one,
      quarticFourAtomicOnLineSecondPairing_two,
      quarticFourAtomicPolePairing_one ht,
      quarticFourAtomicPolePairing_two ht,
      quarticFourAtomicOnLinePairing_one,
      quarticFourAtomicOnLinePairing_two]
  ring

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_root_ge
    {t : ℝ} (ht : t ≠ 0) :
    Real.pi^2 / 32
      <=
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (1/2) (quarticFourAtomicMu (1/2)) := by
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_half_formula ht]
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have h4 := Real.one_le_cosh (4*Real.pi/t)
  have h8 := Real.one_le_cosh (8*Real.pi/t)
  have hp : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_root_le
    {t : ℝ} (ht : 200 <= t) :
    quarticFourAtomicMarkedPoleQuadraticCarrier
      t (2/3) (quarticFourAtomicMu (2/3))
      <= -(Real.pi^2/100) := by
  have ht0 : t ≠ 0 := by linarith
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_formula ht0]
  let C : ℝ := Real.cosh (4*Real.pi/t)
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have hdouble :
      Real.cosh (8*Real.pi/t) = 2*C^2 - 1 := by
    have harg : 8*Real.pi/t = 2*(4*Real.pi/t) := by ring
    rw [harg, Real.cosh_two_mul, Real.cosh_sq]
    dsimp [C]
    ring
  have hs : 0 <= (C - 10/7)^2 := sq_nonneg _
  have hquad :
      -28*C^2 + 80*C - 79 <= -(153/7 : ℝ) := by
    nlinarith
  have hnum :
      -9*Real.cosh (8*Real.pi/(3*t))
        + 80*Real.cosh (4*Real.pi/t)
        - 14*Real.cosh (8*Real.pi/t)
        - 84
      <= -(153/7 : ℝ) := by
    rw [hdouble]
    dsimp [C] at hquad ⊢
    nlinarith
  have hp : 0 < Real.pi^2 := by positivity
  have hscale :
      Real.pi^2 * (-(153/7 : ℝ)) / 1944
        <= -(Real.pi^2/100) := by
    nlinarith
  exact
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnum hp.le)
      (by norm_num : (0:ℝ) <= 1944)).trans hscale

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_mu_difference
    {t mu1 mu2 : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu1
      -
    quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu2
      =
    Real.pi^2 *
      (576
        - 180*Real.cosh (4*Real.pi/t)
        - 396*Real.cosh (8*Real.pi/t))
      / 288 * (mu1-mu2) := by
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_half_general_formula ht,
      quarticFourAtomicMarkedPoleQuadraticCarrier_half_general_formula ht]
  ring

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_mu_difference
    {t mu1 mu2 : ℝ} (ht : t ≠ 0) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu1
      -
    quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu2
      =
    Real.pi^2 *
      (432
        - 180*Real.cosh (4*Real.pi/t)
        - 252*Real.cosh (8*Real.pi/t))
      / 216 * (mu1-mu2) := by
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_general_formula ht,
      quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_general_formula ht]
  ring

private theorem bidi_marked_pole_cosh_four_le_two
    {t : ℝ} (ht : 200 <= t) :
    Real.cosh (4*Real.pi/t) <= 2 := by
  have htpos : 0 < t := by linarith
  have h8ex := quarticFour_cosh_excess_le_one_of_twoHundred ht
  have h8hi : Real.cosh (8*Real.pi/t) <= 2 := by
    linarith
  have hx4 : |4*Real.pi/t| <= |8*Real.pi/t| := by
    have h4 : 0 <= 4*Real.pi/t := by positivity
    have h8 : 0 <= 8*Real.pi/t := by positivity
    rw [abs_of_nonneg h4, abs_of_nonneg h8]
    field_simp [ne_of_gt htpos]
    nlinarith [Real.pi_pos]
  exact ((Real.cosh_le_cosh).2 hx4).trans h8hi

private theorem bidi_marked_pole_cosh_eight_le_two
    {t : ℝ} (ht : 200 <= t) :
    Real.cosh (8*Real.pi/t) <= 2 := by
  have h := quarticFour_cosh_excess_le_one_of_twoHundred ht
  linarith

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_corridor_pos
    {t mu : ℝ} (ht : 200 <= t)
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    0 <
    quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu := by
  have ht0 : t ≠ 0 := by linarith
  have h4lo := Real.one_le_cosh (4*Real.pi/t)
  have h8lo := Real.one_le_cosh (8*Real.pi/t)
  have h4hi := bidi_marked_pole_cosh_four_le_two ht
  have h8hi := bidi_marked_pole_cosh_eight_le_two ht
  have hcoef :
      |576
        - 180*Real.cosh (4*Real.pi/t)
        - 396*Real.cosh (8*Real.pi/t)|
      <= 1728 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdiff :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_half_mu_difference
      (t:=t) (mu1:=mu) (mu2:=quarticFourAtomicMu (1/2)) ht0
  have hp : 0 < Real.pi^2 := by positivity
  have hmu' :
      |mu-quarticFourAtomicMu (1/2)| <= (1/10000 : ℝ) := by
    simpa [quarticFourAtomicMuRadius] using hmu
  have herr :
      |quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu
        -
       quarticFourAtomicMarkedPoleQuadraticCarrier
          t (1/2) (quarticFourAtomicMu (1/2))|
      <= 6*Real.pi^2/10000 := by
    rw [hdiff, abs_mul, abs_mul, abs_div,
      abs_of_pos hp, abs_of_nonneg (by norm_num : (0:ℝ) <= 288)]
    have hc :
        Real.pi^2 * |576
          - 180*Real.cosh (4*Real.pi/t)
          - 396*Real.cosh (8*Real.pi/t)|
          / 288
          <= 6*Real.pi^2 := by
      have := mul_le_mul_of_nonneg_left hcoef hp.le
      nlinarith
    exact (mul_le_mul hc hmu' (abs_nonneg _) (by positivity)).trans_eq
      (by ring)
  have hroot :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_half_root_ge ht0
  have hlo := (abs_le.mp herr).1
  nlinarith [hp]

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_corridor_neg
    {t mu : ℝ} (ht : 200 <= t)
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu < 0 := by
  have ht0 : t ≠ 0 := by linarith
  have h4lo := Real.one_le_cosh (4*Real.pi/t)
  have h8lo := Real.one_le_cosh (8*Real.pi/t)
  have h4hi := bidi_marked_pole_cosh_four_le_two ht
  have h8hi := bidi_marked_pole_cosh_eight_le_two ht
  have hcoef :
      |432
        - 180*Real.cosh (4*Real.pi/t)
        - 252*Real.cosh (8*Real.pi/t)|
      <= 1296 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdiff :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_mu_difference
      (t:=t) (mu1:=mu) (mu2:=quarticFourAtomicMu (2/3)) ht0
  have hp : 0 < Real.pi^2 := by positivity
  have hmu' :
      |mu-quarticFourAtomicMu (2/3)| <= (1/10000 : ℝ) := by
    simpa [quarticFourAtomicMuRadius] using hmu
  have herr :
      |quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu
        -
       quarticFourAtomicMarkedPoleQuadraticCarrier
          t (2/3) (quarticFourAtomicMu (2/3))|
      <= 6*Real.pi^2/10000 := by
    rw [hdiff, abs_mul, abs_mul, abs_div,
      abs_of_pos hp, abs_of_nonneg (by norm_num : (0:ℝ) <= 216)]
    have hc :
        Real.pi^2 * |432
          - 180*Real.cosh (4*Real.pi/t)
          - 252*Real.cosh (8*Real.pi/t)|
          / 216
          <= 6*Real.pi^2 := by
      have := mul_le_mul_of_nonneg_left hcoef hp.le
      nlinarith
    exact (mul_le_mul hc hmu' (abs_nonneg _) (by positivity)).trans_eq
      (by ring)
  have hroot :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_root_le ht
  have hhi := (abs_le.mp herr).2
  nlinarith [hp]

/--
The smooth signed marked-pole quadratic carrier.  Positivity follows from
positive smooth pole coordinates at both endpoints together with the
half-positive / two-thirds-negative marked quadratic endpoint signs.
-/
def quarticFourSmoothSignedMarkedPoleQuadraticCarrier
    (R muHalf muTwo t : ℝ) : ℝ :=
  quarticFourSmoothFinitePoleResidual R (2/3) muTwo t
    * quarticFourSmoothMarkedPoleQuadraticCarrier
        R (1/2) muHalf t
  -
  quarticFourSmoothFinitePoleResidual R (1/2) muHalf t
    * quarticFourSmoothMarkedPoleQuadraticCarrier
        R (2/3) muTwo t

theorem quarticFourSmoothSignedMarkedPoleQuadraticCarrier_pos_of_endpoint_signs
    {R muHalf muTwo t : ℝ}
    (hPoleHalf :
      0 < quarticFourSmoothFinitePoleResidual R (1/2) muHalf t)
    (hPoleTwo :
      0 < quarticFourSmoothFinitePoleResidual R (2/3) muTwo t)
    (hQHalf :
      0 < quarticFourSmoothMarkedPoleQuadraticCarrier
        R (1/2) muHalf t)
    (hQTwo :
      quarticFourSmoothMarkedPoleQuadraticCarrier
        R (2/3) muTwo t < 0) :
    0 <
    quarticFourSmoothSignedMarkedPoleQuadraticCarrier
      R muHalf muTwo t := by
  unfold quarticFourSmoothSignedMarkedPoleQuadraticCarrier
  have h1 := mul_pos hPoleTwo hQHalf
  have h2 := mul_neg_of_pos_of_neg hPoleHalf hQTwo
  linarith


/-!
## Quantitative corridor margins and smooth localization of the marked-pole jet
-/

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_half_corridor_ge
    {t mu : ℝ} (ht : 200 <= t)
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    Real.pi^2 / 32
      <=
    quarticFourAtomicMarkedPoleQuadraticCarrier t (1/2) mu := by
  have ht0 : t ≠ 0 := by linarith
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_half_general_formula ht0]
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have h4 := Real.one_le_cosh (4*Real.pi/t)
  have h8 := Real.one_le_cosh (8*Real.pi/t)
  have hmuHi :
      mu <= -(1/78 : ℝ) + 1/10000 := by
    have h := (abs_le.mp hmu).2
    rw [quarticFourAtomicMu_half] at h
    simpa [quarticFourAtomicMuRadius] using h
  have hmuNonpos : mu <= 0 := by
    nlinarith
  have hcoef :
      576
        - 180*Real.cosh (4*Real.pi/t)
        - 396*Real.cosh (8*Real.pi/t)
      <= 0 := by
    nlinarith
  have hmuprod :
      0 <=
      mu *
        (576
          - 180*Real.cosh (4*Real.pi/t)
          - 396*Real.cosh (8*Real.pi/t)) :=
    mul_nonneg_of_nonpos_of_nonpos hmuNonpos hcoef
  have hp : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_corridor_le
    {t mu : ℝ} (ht : 200 <= t)
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicMarkedPoleQuadraticCarrier t (2/3) mu
      <= -(Real.pi^2/432) := by
  have ht0 : t ≠ 0 := by linarith
  rw [quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_general_formula ht0]
  have h3 := Real.one_le_cosh (8*Real.pi/(3*t))
  have h4 := Real.one_le_cosh (4*Real.pi/t)
  have h8hi := bidi_marked_pole_cosh_eight_le_two ht
  let C : ℝ := Real.cosh (4*Real.pi/t)
  have hdouble :
      Real.cosh (8*Real.pi/t) = 2*C^2 - 1 := by
    have harg : 8*Real.pi/t = 2*(4*Real.pi/t) := by ring
    rw [harg, Real.cosh_two_mul, Real.cosh_sq]
    dsimp [C]
    ring
  have hClo : 1 <= C := by
    dsimp [C]
    exact h4
  have hChi : C <= 5/4 := by
    rw [hdouble] at h8hi
    dsimp [C] at h8hi
    nlinarith [sq_nonneg (C-5/4)]
  have hmuLo :
      (1/162 : ℝ) - 1/10000 <= mu := by
    have h := (abs_le.mp hmu).1
    rw [quarticFourAtomicMu_twoThird] at h
    simpa [quarticFourAtomicMuRadius] using h
  have hmuNonneg : 0 <= mu := by
    nlinarith
  have hcoef :
      432
        - 180*Real.cosh (4*Real.pi/t)
        - 252*Real.cosh (8*Real.pi/t)
      <= 0 := by
    have h8lo := Real.one_le_cosh (8*Real.pi/t)
    nlinarith
  have hmuprod :
      mu *
        (432
          - 180*Real.cosh (4*Real.pi/t)
          - 252*Real.cosh (8*Real.pi/t))
      <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hmuNonneg hcoef
  have hp : 0 < Real.pi^2 := by positivity
  dsimp [C] at hChi
  nlinarith

theorem quarticFourNormalizedPoleSecondWeight_continuous
    (t c : ℝ) :
    Continuous (quarticFourNormalizedPoleSecondWeight t c) := by
  unfold quarticFourNormalizedPoleSecondWeight
  fun_prop

theorem quarticFourNormalizedPoleSecondWeight_even
    (t c v : ℝ) :
    quarticFourNormalizedPoleSecondWeight t c (-v)
      = quarticFourNormalizedPoleSecondWeight t c v := by
  unfold quarticFourNormalizedPoleSecondWeight
  rw [neg_sq, quarticFourNormalizedPoleWeight_even]

theorem quarticFourNormalizedOnLineSecondWeight_continuous
    (c : ℝ) :
    Continuous (quarticFourNormalizedOnLineSecondWeight c) := by
  unfold quarticFourNormalizedOnLineSecondWeight
  fun_prop

theorem quarticFourNormalizedOnLineSecondWeight_even
    (c v : ℝ) :
    quarticFourNormalizedOnLineSecondWeight c (-v)
      = quarticFourNormalizedOnLineSecondWeight c v := by
  unfold quarticFourNormalizedOnLineSecondWeight
  rw [neg_sq, quarticFourNormalizedOnLineWeight_even]

def quarticFourAtomicPairingEnvelope
    (w : ℝ -> ℝ) : ℝ :=
  |w 0|
    + |w (Real.pi/3)|
    + (2/3 : ℝ) * |w (Real.pi/2)|
    + (1/10 : ℝ) * |w Real.pi|

theorem quarticFourAtomicPairingEnvelope_nonneg
    (w : ℝ -> ℝ) :
    0 <= quarticFourAtomicPairingEnvelope w := by
  unfold quarticFourAtomicPairingEnvelope
  positivity

theorem quarticFourAtomicPairing_abs_le_envelope
    {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    (w : ℝ -> ℝ) :
    |quarticFourAtomicPairingAt lam mu w|
      <= quarticFourAtomicPairingEnvelope w := by
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2
  unfold quarticFourAtomicPairingAt quarticFourAtomicPairingEnvelope
  calc
    |w 0 - w (Real.pi/3) + lam*w (Real.pi/2) + mu*w Real.pi|
      <=
    |w 0 - w (Real.pi/3) + lam*w (Real.pi/2)|
      + |mu*w Real.pi| := abs_add _ _
    _ <=
    (|w 0 - w (Real.pi/3)| + |lam*w (Real.pi/2)|)
      + |mu|*|w Real.pi| := by
        gcongr
        · exact abs_add _ _
        · rw [abs_mul]
    _ <=
    (|w 0| + |w (Real.pi/3)|)
      + |lam|*|w (Real.pi/2)|
      + |mu|*|w Real.pi| := by
        gcongr
        · exact abs_sub _ _
        · rw [abs_mul]
    _ <=
    |w 0| + |w (Real.pi/3)|
      + (2/3 : ℝ)*|w (Real.pi/2)|
      + (1/10 : ℝ)*|w Real.pi| := by
        gcongr

def quarticFourMarkedPoleAtomicEnvelope
    (t : ℝ) : ℝ :=
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedPoleWeight t 1)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedPoleWeight t 2)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedOnLineWeight 1)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedOnLineWeight 2)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedPoleSecondWeight t 1)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedPoleSecondWeight t 2)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedOnLineSecondWeight 1)
    +
  quarticFourAtomicPairingEnvelope
      (quarticFourNormalizedOnLineSecondWeight 2)

theorem quarticFourMarkedPoleAtomicEnvelope_nonneg
    (t : ℝ) :
    0 <= quarticFourMarkedPoleAtomicEnvelope t := by
  unfold quarticFourMarkedPoleAtomicEnvelope
  positivity

private theorem quarticFourAtomicPairing_abs_le_markedPoleEnvelope
    {t lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
    (hmu : |mu| <= 1/10)
    {w : ℝ -> ℝ}
    (hw :
      w = quarticFourNormalizedPoleWeight t 1
      ∨ w = quarticFourNormalizedPoleWeight t 2
      ∨ w = quarticFourNormalizedOnLineWeight 1
      ∨ w = quarticFourNormalizedOnLineWeight 2
      ∨ w = quarticFourNormalizedPoleSecondWeight t 1
      ∨ w = quarticFourNormalizedPoleSecondWeight t 2
      ∨ w = quarticFourNormalizedOnLineSecondWeight 1
      ∨ w = quarticFourNormalizedOnLineSecondWeight 2) :
    |quarticFourAtomicPairingAt lam mu w|
      <= quarticFourMarkedPoleAtomicEnvelope t := by
  have h :=
    quarticFourAtomicPairing_abs_le_envelope hlam hmu w
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact h.trans (by
      unfold quarticFourMarkedPoleAtomicEnvelope
      positivity)

/--
Uniform smooth localization of the two endpoint marked-pole quadratic signs.

The theorem is uniform over the existing atomic mu corridor; no stronger
witness-selection hypothesis is introduced.
-/
theorem exists_radius_quarticFourSmoothMarkedPoleQuadraticCarrier_endpoint_signs
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwo : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwo-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        0 <
          quarticFourSmoothMarkedPoleQuadraticCarrier
            R (1/2) muHalf t
        ∧
        quarticFourSmoothMarkedPoleQuadraticCarrier
            R (2/3) muTwo t < 0 := by
  let margin : ℝ := Real.pi^2 / 500
  let M : ℝ := quarticFourMarkedPoleAtomicEnvelope t
  let eta : ℝ := min 1 (margin / (4*(4*M+2)))
  have hmargin : 0 < margin := by
    dsimp [margin]
    positivity
  have hM : 0 <= M := by
    dsimp [M]
    exact quarticFourMarkedPoleAtomicEnvelope_nonneg t
  have hden : 0 < 4*(4*M+2) := by positivity
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hmargin hden)
  have heta1 : eta <= 1 := min_le_left _ _

  obtain ⟨dP1,hdP1,hP1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleWeight_continuous t 1)
      (quarticFourNormalizedPoleWeight_even t 1) heta
  obtain ⟨dP2,hdP2,hP2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleWeight_continuous t 2)
      (quarticFourNormalizedPoleWeight_even t 2) heta
  obtain ⟨dO1,hdO1,hO1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineWeight_continuous 1)
      (quarticFourNormalizedOnLineWeight_even 1) heta
  obtain ⟨dO2,hdO2,hO2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineWeight_continuous 2)
      (quarticFourNormalizedOnLineWeight_even 2) heta
  obtain ⟨dPS1,hdPS1,hPS1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleSecondWeight_continuous t 1)
      (quarticFourNormalizedPoleSecondWeight_even t 1) heta
  obtain ⟨dPS2,hdPS2,hPS2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedPoleSecondWeight_continuous t 2)
      (quarticFourNormalizedPoleSecondWeight_even t 2) heta
  obtain ⟨dOS1,hdOS1,hOS1⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineSecondWeight_continuous 1)
      (quarticFourNormalizedOnLineSecondWeight_even 1) heta
  obtain ⟨dOS2,hdOS2,hOS2⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticFourNormalizedOnLineSecondWeight_continuous 2)
      (quarticFourNormalizedOnLineSecondWeight_even 2) heta

  let delta :=
    min dP1 (min dP2 (min dO1 (min dO2
      (min dPS1 (min dPS2 (min dOS1 dOS2))))))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdP1
      (lt_min hdP2
        (lt_min hdO1
          (lt_min hdO2
            (lt_min hdPS1
              (lt_min hdPS2
                (lt_min hdOS1 hdOS2))))))
  refine ⟨delta,hdelta,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo

  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩

  have hRdP1 : R < dP1 := hRd.trans_le (min_le_left _ _)
  have hrestP2 :=
    hRd.trans_le (min_le_right dP1
      (min dP2 (min dO1 (min dO2
        (min dPS1 (min dPS2 (min dOS1 dOS2)))))))
  have hRdP2 : R < dP2 := hrestP2.trans_le (min_le_left _ _)
  have hrestO1 := hrestP2.trans_le (min_le_right _ _)
  have hRdO1 : R < dO1 := hrestO1.trans_le (min_le_left _ _)
  have hrestO2 := hrestO1.trans_le (min_le_right _ _)
  have hRdO2 : R < dO2 := hrestO2.trans_le (min_le_left _ _)
  have hrestPS1 := hrestO2.trans_le (min_le_right _ _)
  have hRdPS1 : R < dPS1 := hrestPS1.trans_le (min_le_left _ _)
  have hrestPS2 := hrestPS1.trans_le (min_le_right _ _)
  have hRdPS2 : R < dPS2 := hrestPS2.trans_le (min_le_left _ _)
  have hrestOS1 := hrestPS2.trans_le (min_le_right _ _)
  have hRdOS1 : R < dOS1 := hrestOS1.trans_le (min_le_left _ _)
  have hRdOS2 : R < dOS2 := hrestOS1.trans_le (min_le_right _ _)

  have pairError
      (lam mu : ℝ)
      (hlam : lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ))
      (hmu : |mu| <= 1/10) :
      |quarticFourSmoothMarkedPoleQuadraticCarrier R lam mu t
        - quarticFourAtomicMarkedPoleQuadraticCarrier t lam mu|
        <= 2*(4*M+2)*eta := by
    have eP1 := hP1 R lam mu hR hRdP1 hlam hmu
    have eP2 := hP2 R lam mu hR hRdP2 hlam hmu
    have eO1 := hO1 R lam mu hR hRdO1 hlam hmu
    have eO2 := hO2 R lam mu hR hRdO2 hlam hmu
    have ePS1 := hPS1 R lam mu hR hRdPS1 hlam hmu
    have ePS2 := hPS2 R lam mu hR hRdPS2 hlam hmu
    have eOS1 := hOS1 R lam mu hR hRdOS1 hlam hmu
    have eOS2 := hOS2 R lam mu hR hRdOS2 hlam hmu

    have aPS1 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedPoleSecondWeight t 1)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have bO2 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedOnLineWeight 2)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have cPS2 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedPoleSecondWeight t 2)
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl rfl))))))
    have dO1 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedOnLineWeight 1)
        (Or.inr (Or.inr (Or.inl rfl)))
    have hdet1 :=
      abs_det_sub_det_le hM heta.le heta1
        aPS1 bO2 cPS2 dO1
        ePS1 eO2 ePS2 eO1

    have aP1 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedPoleWeight t 1)
        (Or.inl rfl)
    have bOS2 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedOnLineSecondWeight 2)
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr rfl)))))))
    have cP2 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedPoleWeight t 2)
        (Or.inr (Or.inl rfl))
    have dOS1 :=
      quarticFourAtomicPairing_abs_le_markedPoleEnvelope
        (t:=t) hlam hmu
        (w:=quarticFourNormalizedOnLineSecondWeight 1)
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl rfl)))))))
    have hdet2 :=
      abs_det_sub_det_le hM heta.le heta1
        aP1 bOS2 cP2 dOS1
        eP1 eOS2 eP2 eOS1

    unfold quarticFourSmoothMarkedPoleQuadraticCarrier
      quarticFourAtomicMarkedPoleQuadraticCarrier
    have htri :=
      abs_add
        ((quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleSecondWeight t 1)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineWeight 2)
          -
          quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleSecondWeight t 2)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineWeight 1))
        -
        (quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleSecondWeight t 1)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineWeight 2)
          -
          quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleSecondWeight t 2)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineWeight 1)))
        ((quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleWeight t 1)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineSecondWeight 2)
          -
          quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleWeight t 2)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineSecondWeight 1))
        -
        (quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleWeight t 1)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineSecondWeight 2)
          -
          quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleWeight t 2)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineSecondWeight 1)))
    have hrearr :
        quarticFourSmoothMarkedPoleQuadraticCarrier R lam mu t
          - quarticFourAtomicMarkedPoleQuadraticCarrier t lam mu
        =
        ((quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleSecondWeight t 1)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineWeight 2)
          -
          quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleSecondWeight t 2)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineWeight 1))
        -
        (quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleSecondWeight t 1)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineWeight 2)
          -
          quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleSecondWeight t 2)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineWeight 1)))
        +
        ((quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleWeight t 1)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineSecondWeight 2)
          -
          quarticFourWindowPairing R lam mu
            (quarticFourNormalizedPoleWeight t 2)
          * quarticFourWindowPairing R lam mu
            (quarticFourNormalizedOnLineSecondWeight 1))
        -
        (quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleWeight t 1)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineSecondWeight 2)
          -
          quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedPoleWeight t 2)
          * quarticFourAtomicPairingAt lam mu
            (quarticFourNormalizedOnLineSecondWeight 1))) := by
      ring
    rw [hrearr]
    exact htri.trans (by linarith [hdet1,hdet2])

  have hErrBound :
      2*(4*M+2)*eta <= margin/2 := by
    have hetaRight :
        eta <= margin/(4*(4*M+2)) := min_le_right _ _
    have hcoef : 0 <= 2*(4*M+2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hetaRight hcoef
    field_simp [ne_of_gt (by positivity : 0 < 4*M+2)] at hmul ⊢
    nlinarith

  have eHalf :=
    pairError (1/2) muHalf hlamHalf hmuHalfAbs.le
  have eTwo :=
    pairError (2/3) muTwo hlamTwo hmuTwoAbs.le
  have hHalfAtomic :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_half_corridor_ge
      ht hmuHalf
  have hTwoAtomic :=
    quarticFourAtomicMarkedPoleQuadraticCarrier_twoThird_corridor_le
      ht hmuTwo
  have eHalf' := eHalf.trans hErrBound
  have eTwo' := eTwo.trans hErrBound
  have hHalfLo := (abs_le.mp eHalf').1
  have hTwoHi := (abs_le.mp eTwo').2
  dsimp [margin] at hHalfLo hTwoHi
  constructor <;> nlinarith [Real.pi_pos]


/-!
## Strengthened bidi witness existence

The original witness constructor remains unchanged.  The bidi lane uses a
stronger existential theorem choosing the same common radius below two
additional robustness thresholds: positive individual pole coordinates and
the marked-pole quadratic endpoint signs.
-/

theorem exists_quarticFourSignedPolePair_with_strength_floor_and_markedPoleQuadratic
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 <= W.targetStrength
      ∧
      0 <
      quarticFourSmoothSignedMarkedPoleQuadraticCarrier
        W.R W.muHalf W.muTwo t := by
  obtain ⟨R0,hR0,hfamily⟩ :=
    exists_uniform_smooth_quarticFourWindow_family
  obtain ⟨dTarget,hdTarget,hTarget⟩ :=
    exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin ht
  obtain ⟨dQ,hdQ,hQ⟩ :=
    exists_radius_quarticFourSmoothMarkedPoleQuadraticCarrier_endpoint_signs ht
  obtain ⟨dPole,hdPole,hPole⟩ :=
    exists_radius_quarticFourSmoothPole_pos ht

  let R : ℝ :=
    min 1 (min R0 (min dTarget (min dQ dPole))) / 2
  have hinner :
      0 < min R0 (min dTarget (min dQ dPole)) :=
    lt_min hR0 (lt_min hdTarget (lt_min hdQ hdPole))
  have hmin :
      0 < min 1 (min R0 (min dTarget (min dQ dPole))) :=
    lt_min (by norm_num) hinner
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hle :=
      min_le_left 1 (min R0 (min dTarget (min dQ dPole)))
    linarith
  have hRinner :
      R < min R0 (min dTarget (min dQ dPole)) := by
    dsimp [R]
    have hle :=
      min_le_right 1 (min R0 (min dTarget (min dQ dPole)))
    linarith
  have hRR0 : R < R0 :=
    hRinner.trans_le
      (min_le_left R0 (min dTarget (min dQ dPole)))
  have hRest :
      R < min dTarget (min dQ dPole) :=
    hRinner.trans_le
      (min_le_right R0 (min dTarget (min dQ dPole)))
  have hRTarget : R < dTarget :=
    hRest.trans_le (min_le_left dTarget (min dQ dPole))
  have hRestQP : R < min dQ dPole :=
    hRest.trans_le (min_le_right dTarget (min dQ dPole))
  have hRQ : R < dQ :=
    hRestQP.trans_le (min_le_left dQ dPole)
  have hRPole : R < dPole :=
    hRestQP.trans_le (min_le_right dQ dPole)

  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩

  obtain ⟨S1⟩ := hfamily R (1/2) hR hRR0 hlamHalf
  obtain ⟨S2⟩ := hfamily R (2/3) hR hRR0 hlamTwo

  have hfloor :
      7 * Real.pi^4 / 1600 <=
        quarticFourSmoothPoleCancelledTarget
          R S1.mu S2.mu t :=
    hTarget R S1.mu S2.mu hR hRTarget
      S1.muNear S2.muNear

  have htransPos :
      0 < quarticFourSmoothPoleCancelledTarget
        R S1.mu S2.mu t := by
    have hp4 : 0 < Real.pi^4 := by positivity
    nlinarith

  obtain ⟨eps,heps,hband⟩ :=
    exists_quarticFourSignedPoleCombinedHeightDefect_pos_punctured
      hR S1.J2zero S2.J2zero htransPos

  let W : QuarticFourSignedPolePair t := {
    R := R
    muHalf := S1.mu
    muTwo := S2.mu
    eps := eps
    Rpos := hR
    RltOne := hRone
    muHalfNear := S1.muNear
    muTwoNear := S2.muNear
    J2Half := S1.J2zero
    J2Two := S2.J2zero
    signedTargetStrength := htransPos
    epsPos := heps
    combinedTargetBand := hband
  }

  have hQsigns :=
    hQ R S1.mu S2.mu hR hRQ S1.muNear S2.muNear
  have hPoleHalf :=
    hPole R (1/2) S1.mu hR hRPole
      hlamHalf S1.muAbs.le
  have hPoleTwo :=
    hPole R (2/3) S2.mu hR hRPole
      hlamTwo S2.muAbs.le
  have hMarked :
      0 <
      quarticFourSmoothSignedMarkedPoleQuadraticCarrier
        R S1.mu S2.mu t :=
    quarticFourSmoothSignedMarkedPoleQuadraticCarrier_pos_of_endpoint_signs
      hPoleHalf hPoleTwo hQsigns.1 hQsigns.2

  refine ⟨W,?_,?_⟩
  · simpa [W, QuarticFourSignedPolePair.targetStrength] using hfloor
  · simpa [W] using hMarked


/-!
## Exact normalized form of the cosh-marked pole channel
-/

def quarticFourBidiNormalizedMark
    (t A v : ℝ) : ℝ :=
  Real.cosh ((16*A/t) * v)

def quarticFourBidiMarkedNormalizedPoleWeight
    (t A c v : ℝ) : ℝ :=
  quarticFourBidiNormalizedMark t A v
    * quarticFourNormalizedPoleWeight t c v

def quarticFourBidiMarkedNormalizedOnLineWeight
    (t A c v : ℝ) : ℝ :=
  quarticFourBidiNormalizedMark t A v
    * quarticFourNormalizedOnLineWeight c v

def quarticFourSmoothBidiMarkedPoleResidual
    (R lam mu t A : ℝ) : ℝ :=
  quarticFourWindowPairing R lam mu
      (quarticFourBidiMarkedNormalizedPoleWeight t A 1)
    * quarticFourWindowPairing R lam mu
      (quarticFourBidiMarkedNormalizedOnLineWeight t A 2)
  -
  quarticFourWindowPairing R lam mu
      (quarticFourBidiMarkedNormalizedPoleWeight t A 2)
    * quarticFourWindowPairing R lam mu
      (quarticFourBidiMarkedNormalizedOnLineWeight t A 1)

theorem quarticFourBidiMarkedNormalizedPoleWeight_continuous
    (t A c : ℝ) :
    Continuous (quarticFourBidiMarkedNormalizedPoleWeight t A c) := by
  unfold quarticFourBidiMarkedNormalizedPoleWeight
    quarticFourBidiNormalizedMark
  fun_prop

theorem quarticFourBidiMarkedNormalizedOnLineWeight_continuous
    (t A c : ℝ) :
    Continuous (quarticFourBidiMarkedNormalizedOnLineWeight t A c) := by
  unfold quarticFourBidiMarkedNormalizedOnLineWeight
    quarticFourBidiNormalizedMark
  fun_prop

theorem poleEvenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing
    {R lam mu t A : ℝ}
    (hR : 0 < R) (ht : 0 < t)
    (c : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.poleEvenResp
        (quarticFourBidiMarkedPhysicalDetector R lam mu t A)
        t (c*(t/16))
      =
    (16/t) *
      quarticFourWindowPairing R lam mu
        (quarticFourBidiMarkedNormalizedPoleWeight t A c) := by
  let r : ℝ := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let G : ℝ -> ℝ := quarticFourWindowProfile R lam mu
  let F : ℝ -> ℝ := fun v =>
    G v * quarticFourBidiMarkedNormalizedPoleWeight t A c v
  have hpoint :
      (fun u : ℝ =>
        quarticFourBidiMarkedPhysicalDetector R lam mu t A u *
          (Real.cosh (u/2) * Real.cos (t*u) * Real.cos ((c*(t/16))*u)))
        =
      fun u => F (r*u) := by
    funext u
    dsimp [F,G,r]
    unfold quarticFourBidiMarkedPhysicalDetector
      quarticSignedPoleCoshMarkedDetector
      quarticFourPhysicalDetector
      projectiveRescaleProfile
      quarticFourBidiMarkedNormalizedPoleWeight
      quarticFourBidiNormalizedMark
      quarticFourNormalizedPoleWeight
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hmark :
        A*u = (16*A/t) * ((t/16)*u) := by
      field_simp [ht0]
      ring
    have h1 : 8*((t/16)*u)/t = u/2 := by
      field_simp [ht0]
      ring
    have h2 : 16*((t/16)*u) = t*u := by ring
    have h3 : c*((t/16)*u) = (c*(t/16))*u := by ring
    rw [hmark,h1,h2,h3]
    ring
  unfold Zeta23Bridge.LiteralWeilParityBalance.poleEvenResp
  rw [hpoint]
  have hscale := Measure.integral_comp_mul_left F r
  have habs : |r⁻¹| = 1/r := by
    rw [abs_of_pos (inv_pos.mpr hr)]
    rfl
  have hscale' :
      (∫ u : ℝ, F (r*u))
        = (1/r) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hscale']
  have hpair :
      (∫ v : ℝ, F v)
        =
      quarticFourWindowPairing R lam mu
        (quarticFourBidiMarkedNormalizedPoleWeight t A c) := by
    dsimp [F,G]
    exact quarticFourWindowProfile_pairing_eq
      hR (quarticFourBidiMarkedNormalizedPoleWeight_continuous t A c)
  rw [hpair]
  dsimp [r]
  field_simp [ne_of_gt ht]
  ring

theorem evenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing
    {R lam mu t A : ℝ}
    (hR : 0 < R) (ht : 0 < t)
    (c : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
        (quarticFourBidiMarkedPhysicalDetector R lam mu t A)
        0 (c*(t/16))
      =
    (16/t) *
      quarticFourWindowPairing R lam mu
        (quarticFourBidiMarkedNormalizedOnLineWeight t A c) := by
  let r : ℝ := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let G : ℝ -> ℝ := quarticFourWindowProfile R lam mu
  let F : ℝ -> ℝ := fun v =>
    G v * quarticFourBidiMarkedNormalizedOnLineWeight t A c v
  have hpoint :
      (fun u : ℝ =>
        quarticFourBidiMarkedPhysicalDetector R lam mu t A u *
          (Real.cosh (0*u) * Real.cos ((c*(t/16))*u)))
        =
      fun u => F (r*u) := by
    funext u
    dsimp [F,G,r]
    unfold quarticFourBidiMarkedPhysicalDetector
      quarticSignedPoleCoshMarkedDetector
      quarticFourPhysicalDetector
      projectiveRescaleProfile
      quarticFourBidiMarkedNormalizedOnLineWeight
      quarticFourBidiNormalizedMark
      quarticFourNormalizedOnLineWeight
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hmark :
        A*u = (16*A/t) * ((t/16)*u) := by
      field_simp [ht0]
      ring
    have h3 : c*((t/16)*u) = (c*(t/16))*u := by ring
    rw [hmark,h3]
    simp
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
  rw [hpoint]
  have hscale := Measure.integral_comp_mul_left F r
  have habs : |r⁻¹| = 1/r := by
    rw [abs_of_pos (inv_pos.mpr hr)]
    rfl
  have hscale' :
      (∫ u : ℝ, F (r*u))
        = (1/r) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hscale']
  have hpair :
      (∫ v : ℝ, F v)
        =
      quarticFourWindowPairing R lam mu
        (quarticFourBidiMarkedNormalizedOnLineWeight t A c) := by
    dsimp [F,G]
    exact quarticFourWindowProfile_pairing_eq
      hR (quarticFourBidiMarkedNormalizedOnLineWeight_continuous t A c)
  rw [hpair]
  dsimp [r]
  field_simp [ne_of_gt ht]
  ring

theorem poleProjectiveDefect_quarticFourBidiMarkedPhysicalDetector_eq
    {R lam mu t A : ℝ}
    (hR : 0 < R) (ht : 0 < t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
        (quarticFourBidiMarkedPhysicalDetector R lam mu t A)
        t (t/16)
      =
    4 * (16/t)^2 *
      quarticFourSmoothBidiMarkedPoleResidual R lam mu t A := by
  have hc :=
    quarticSignedPoleCoshMarkedDetector_contDiff
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=lam) (mu:=mu) hR) A
  have hk :=
    quarticSignedPoleCoshMarkedDetector_compact
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=lam) (mu:=mu) hR ht) A
  have he :
      ∀ u,
        quarticFourBidiMarkedPhysicalDetector R lam mu t A (-u)
          =
        quarticFourBidiMarkedPhysicalDetector R lam mu t A u := by
    intro u
    unfold quarticFourBidiMarkedPhysicalDetector
    exact quarticSignedPoleCoshMarkedDetector_even
      (quarticFourPhysicalDetector_even R lam mu t) A u
  rw [Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect_eq
      hc.continuous hk he t (t/16)]
  rw [show 2*(t/16) = (2:ℝ)*(t/16) by ring,
      show t/16 = (1:ℝ)*(t/16) by ring,
      poleEvenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing hR ht 2,
      poleEvenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing hR ht 1,
      evenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing hR ht 1,
      evenResp_quarticFourBidiMarkedPhysicalDetector_eq_pairing hR ht 2]
  unfold quarticFourSmoothBidiMarkedPoleResidual
  ring

theorem QuarticFourSignedPolePair.bidiMarkedPoleCombination_eq_normalized
    {t A : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.bidiMarkedPoleCombination A
      =
    4 * (16/t)^2 *
      (
        W.poleTwo *
          quarticFourSmoothBidiMarkedPoleResidual
            W.R (1/2) W.muHalf t A
        -
        W.poleHalf *
          quarticFourSmoothBidiMarkedPoleResidual
            W.R (2/3) W.muTwo t A
      ) := by
  unfold QuarticFourSignedPolePair.bidiMarkedPoleCombination
  rw [poleProjectiveDefect_quarticFourBidiMarkedPhysicalDetector_eq
        W.Rpos ht,
      poleProjectiveDefect_quarticFourBidiMarkedPhysicalDetector_eq
        W.Rpos ht]
  ring

end Synthesis
