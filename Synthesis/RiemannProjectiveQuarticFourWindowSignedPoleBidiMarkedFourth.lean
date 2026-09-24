import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds

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

end Synthesis
