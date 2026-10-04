import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleSmooth
import Synthesis.RiemannProjectiveQuarticFourWindowSmoothFamily

/-!
# Uniform high-t pole localization -> fixed-width signed-pole core

The existing smooth-family/J2/J4 construction already has a radius independent
of the physical ordinate t.  The only t-dependent radius enters through the
smooth finite-pole localization theorem.

This file isolates exactly that missing quantifier swap.  A uniform high-t pole
localization estimate at one fixed tolerance immediately yields one fixed
positive radius R and one fixed pair of smooth endpoint coefficients muHalf,
muTwo such that the signed pole/target determinant retains the same positive
floor for every t>=200.

Thus no further compactness or choice issue remains in the witness width once
the elementary equicontinuity estimate for the pole weights is supplied.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real

/-- Uniform-in-t version of the existing smooth-pole localization theorem. -/
def UniformQuarticFourSmoothPoleLocalization (eta : ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ t R lam mu : ℝ,
      200 <= t ->
      0 < R -> R < delta ->
      lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
      |mu| <= 1/10 ->
      |quarticFourSmoothFinitePoleResidual R lam mu t
        - quarticFourAtomicFinitePoleResidual t lam mu| <= eta

/-- Fixed smooth endpoint data that work simultaneously for all high t. -/
structure UniformQuarticFourSignedPoleCore where
  R : ℝ
  muHalf : ℝ
  muTwo : ℝ
  Rpos : 0 < R
  RltOne : R < 1
  muHalfNear :
    |muHalf-quarticFourAtomicMu (1/2)| <= quarticFourAtomicMuRadius
  muTwoNear :
    |muTwo-quarticFourAtomicMu (2/3)| <= quarticFourAtomicMuRadius
  J2Half :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R (1/2) muHalf) 1 = 0
  J2Two :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R (2/3) muTwo) 1 = 0
  signedTargetFloor :
    ∀ t : ℝ, 200 <= t ->
      7 * Real.pi^4 / 1600 <=
        quarticFourSmoothPoleCancelledTarget R muHalf muTwo t

/-- The exact tolerance used by the existing determinant robustness proof. -/
def quarticFourUniformPoleLocalizationTolerance : ℝ :=
  let margin : ℝ := 7 * Real.pi^4 / 800
  let M : ℝ := 10 + Real.pi^4
  min 1 (margin / (2*(4*M+2)))

theorem quarticFourUniformPoleLocalizationTolerance_pos :
    0 < quarticFourUniformPoleLocalizationTolerance := by
  unfold quarticFourUniformPoleLocalizationTolerance
  apply lt_min
  · norm_num
  · positivity

/-- Uniform pole localization at the robustness tolerance produces a single
fixed-width J2-null endpoint pair valid for every t>=200. -/
theorem exists_uniformQuarticFourSignedPoleCore_of_uniformPoleLocalization
    (hPole : UniformQuarticFourSmoothPoleLocalization
      quarticFourUniformPoleLocalizationTolerance) :
    Nonempty UniformQuarticFourSignedPoleCore := by
  let eta := quarticFourUniformPoleLocalizationTolerance
  obtain ⟨dPole,hdPole,hPoleClose⟩ := hPole
  obtain ⟨dJ4,hdJ4,hJ4⟩ :=
    exists_radius_quarticFourWindowJ4_close_atomic
      quarticFourUniformPoleLocalizationTolerance_pos
  obtain ⟨R0,hR0,hfamily⟩ := exists_uniform_smooth_quarticFourWindow_family
  let R : ℝ := min 1 (min R0 (min dPole dJ4)) / 2
  have hinner : 0 < min R0 (min dPole dJ4) :=
    lt_min hR0 (lt_min hdPole hdJ4)
  have hmin : 0 < min 1 (min R0 (min dPole dJ4)) :=
    lt_min (by norm_num) hinner
  have hR : 0 < R := by dsimp [R]; linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hle := min_le_left 1 (min R0 (min dPole dJ4))
    linarith
  have hRrest : R < min R0 (min dPole dJ4) := by
    dsimp [R]
    have hle := min_le_right 1 (min R0 (min dPole dJ4))
    linarith
  have hRR0 : R < R0 := hRrest.trans_le (min_le_left _ _)
  have hRpd4 : R < min dPole dJ4 := hRrest.trans_le (min_le_right _ _)
  have hRPole : R < dPole := hRpd4.trans_le (min_le_left _ _)
  have hRJ4 : R < dJ4 := hRpd4.trans_le (min_le_right _ _)
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  obtain ⟨S1⟩ := hfamily R (1/2) hR hRR0 hlamHalf
  obtain ⟨S2⟩ := hfamily R (2/3) hR hRR0 hlamTwo
  refine ⟨{
    R := R
    muHalf := S1.mu
    muTwo := S2.mu
    Rpos := hR
    RltOne := hRone
    muHalfNear := S1.muNear
    muTwoNear := S2.muNear
    J2Half := S1.J2zero
    J2Two := S2.J2zero
    signedTargetFloor := ?_
  }⟩
  intro t ht
  let margin : ℝ := 7 * Real.pi^4 / 800
  let M : ℝ := 10 + Real.pi^4
  have hM : 0 <= M := by dsimp [M]; positivity
  have heta1 : eta <= 1 := by
    dsimp [eta, quarticFourUniformPoleLocalizationTolerance]
    exact min_le_left _ _
  have eP2 := hPoleClose t R (2/3) S2.mu ht hR hRPole hlamTwo S2.muAbs.le
  have eP1 := hPoleClose t R (1/2) S1.mu ht hR hRPole hlamHalf S1.muAbs.le
  have eJ1 := hJ4 R (1/2) S1.mu hR hRJ4 hlamHalf S1.muAbs.le
  have eJ2 := hJ4 R (2/3) S2.mu hR hRJ4 hlamTwo S2.muAbs.le
  have eS1 :
      |quarticFourSmoothTargetStrength R (1/2) S1.mu
        - quarticFourAtomicTargetStrengthAt (1/2) S1.mu| <= eta := by
    unfold eta quarticFourUniformPoleLocalizationTolerance at eJ1 ⊢
    unfold quarticFourSmoothTargetStrength quarticFourAtomicTargetStrengthAt
    simpa [abs_neg] using eJ1
  have eS2 :
      |quarticFourSmoothTargetStrength R (2/3) S2.mu
        - quarticFourAtomicTargetStrengthAt (2/3) S2.mu| <= eta := by
    unfold eta quarticFourUniformPoleLocalizationTolerance at eJ2 ⊢
    unfold quarticFourSmoothTargetStrength quarticFourAtomicTargetStrengthAt
    simpa [abs_neg] using eJ2
  have hP1lo :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamHalf S1.muAbs.le
  have hP2lo :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamTwo S2.muAbs.le
  have hP1hi := quarticFourAtomicFinitePole_half_le_five_halves ht S1.muAbs.le
  have hP2hi := quarticFourAtomicFinitePole_twoThirds_le_five_halves ht S2.muAbs.le
  have hS1lo := quarticFourAtomicTargetStrengthAt_half_ge S1.muNear
  have hS1hi := quarticFourAtomicTargetStrengthAt_half_le S1.muNear
  have hS2lo := quarticFourAtomicTargetStrengthAt_twoThirds_pos S2.muNear
  have hS2hi := quarticFourAtomicTargetStrengthAt_twoThirds_le S2.muNear
  have a0 : |quarticFourAtomicFinitePoleResidual t (2/3) S2.mu| <= M := by
    rw [abs_of_nonneg (by linarith)]
    dsimp [M]
    linarith
  have b0 : |quarticFourAtomicTargetStrengthAt (1/2) S1.mu| <= M := by
    rw [abs_of_nonneg (by linarith)]
    dsimp [M]
    nlinarith [Real.pi_pos]
  have c0 : |quarticFourAtomicFinitePoleResidual t (1/2) S1.mu| <= M := by
    rw [abs_of_nonneg (by linarith)]
    dsimp [M]
    linarith
  have d0 : |quarticFourAtomicTargetStrengthAt (2/3) S2.mu| <= M := by
    rw [abs_of_pos hS2lo]
    dsimp [M]
    nlinarith [Real.pi_pos]
  have hdetErr := abs_det_sub_det_le hM eta.le heta1
    a0 b0 c0 d0 eP2 eS1 eP1 eS2
  have hatom := quarticFourAtomicFinitePoleCancelledTarget_ge_margin
    ht S1.muNear S2.muNear
  have hetaRight : eta <= margin/(2*(4*M+2)) := by
    dsimp [eta, quarticFourUniformPoleLocalizationTolerance, margin, M]
    exact min_le_right _ _
  have hcoef : 0 <= 4*M+2 := by positivity
  have herrScale := mul_le_mul_of_nonneg_left hetaRight hcoef
  have herr :
      |quarticFourSmoothPoleCancelledTarget R S1.mu S2.mu t
        - quarticFourAtomicFinitePoleCancelledTarget t S1.mu S2.mu|
        <= margin/2 := by
    unfold quarticFourSmoothPoleCancelledTarget
      quarticFourAtomicFinitePoleCancelledTarget at hdetErr ⊢
    calc
      _ <= (4*M+2)*eta := hdetErr
      _ <= margin/2 := by
        have hden : 0 < 4*M+2 := by positivity
        rw [div_eq_mul_inv] at hetaRight
        field_simp [ne_of_gt hden] at herrScale ⊢
        nlinarith
  have hlo := (abs_le.mp herr).1
  dsimp [margin] at hatom hlo ⊢
  nlinarith [Real.pi_pos]

end Synthesis
