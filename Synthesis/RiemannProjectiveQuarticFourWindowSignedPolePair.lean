import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleTarget
import Synthesis.RiemannProjectiveQuarticFourWindowSmoothFamily
import Synthesis.RiemannProjectiveQuarticFourWindowPoleSameObject
import Synthesis.RiemannProjectiveQuarticHighCluster

/-!
# A smooth signed pole-cancelled endpoint witness pair

For each fixed t>=200 choose one sufficiently small common window radius R.
The smooth four-window family then supplies exact J2-null endpoint profiles at

  lambda = 1/2,  2/3.

The signed pole/target transversality survives smoothing, so the coefficients

  c_half = P_{2/3},
  c_two  = -P_{1/2}

cancel the literal pole channel and leave a positive quartic target profile.

This file packages those facts into one witness.  Once the normalized strip
width 8/t lies in the witness's combined positive band, every same-ordinate zero
has nonnegative signed combined defect, and every off-line one has strictly
positive combined defect.

This is the signed replacement for the earlier positive-cone construction.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

structure QuarticFourSignedPolePair (t : ℝ) where
  R : ℝ
  muHalf : ℝ
  muTwo : ℝ
  eps : ℝ

  Rpos : 0 < R
  RltOne : R < 1
  muHalfNear :
    |muHalf-quarticFourAtomicMu (1/2)|
      <= quarticFourAtomicMuRadius
  muTwoNear :
    |muTwo-quarticFourAtomicMu (2/3)|
      <= quarticFourAtomicMuRadius

  J2Half :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R (1/2) muHalf) 1 = 0
  J2Two :
    projectiveBracketSecondMoment
      (quarticFourWindowProfile R (2/3) muTwo) 1 = 0

  signedTargetStrength :
    0 < quarticFourSmoothPoleCancelledTarget
      R muHalf muTwo t

  epsPos : 0 < eps
  combinedTargetBand :
    ∀ a : ℝ, 0 < |a| -> |a| < eps ->
      0 <
      quarticFourSignedPoleCombinedHeightDefect
        R muHalf muTwo t a

/--
The scalar signed quartic target strength carried by a witness.

The pre-existing `signedTargetStrength` structure field is deliberately kept
as the positivity proof for compatibility. Quantitative consumers should use
this scalar definition.
-/
def QuarticFourSignedPolePair.targetStrength
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticFourSmoothPoleCancelledTarget
    W.R W.muHalf W.muTwo t

theorem QuarticFourSignedPolePair.targetStrength_pos
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 < W.targetStrength := by
  exact W.signedTargetStrength


/--
For every t >= 200 there exists a signed-pole pair selected from the narrow
smooth robustness corridor whose scalar target strength retains the explicit
7*pi^4/1600 floor.

This is the quantitative witness needed by G1.  The quantifier is existential:
no claim is made that every arbitrary inhabitant of
`QuarticFourSignedPolePair t` satisfies the floor.
-/
theorem exists_quarticFourSignedPolePair_with_strength_floor
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 <= W.targetStrength := by
  obtain ⟨R0,hR0,hfamily⟩ :=
    exists_uniform_smooth_quarticFourWindow_family
  obtain ⟨d,hd,htrans⟩ :=
    exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin ht
  let R : ℝ := min 1 (min R0 d) / 2
  have hinner : 0 < min R0 d := lt_min hR0 hd
  have hmin : 0 < min 1 (min R0 d) :=
    lt_min (by norm_num) hinner
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hle := min_le_left 1 (min R0 d)
    linarith
  have hRinner : R < min R0 d := by
    dsimp [R]
    have hle := min_le_right 1 (min R0 d)
    linarith
  have hRR0 : R < R0 :=
    hRinner.trans_le (min_le_left R0 d)
  have hRd : R < d :=
    hRinner.trans_le (min_le_right R0 d)

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
    htrans R S1.mu S2.mu hR hRd S1.muNear S2.muNear

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
  refine ⟨W, ?_⟩
  simpa [W, QuarticFourSignedPolePair.targetStrength] using hfloor

/--
Compatibility constructor retained for older consumers.
-/
theorem exists_quarticFourSignedPolePair
    {t : ℝ} (ht : 200 <= t) :
    Nonempty (QuarticFourSignedPolePair t) := by
  obtain ⟨W, _⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor ht
  exact ⟨W⟩

def QuarticFourSignedPolePair.poleHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticFourSmoothFinitePoleResidual W.R (1/2) W.muHalf t

def QuarticFourSignedPolePair.poleTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticFourSmoothFinitePoleResidual W.R (2/3) W.muTwo t

theorem QuarticFourSignedPolePair.normalizedPole_cancel
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.poleTwo * W.poleHalf + (-W.poleHalf) * W.poleTwo = 0 := by
  ring

theorem QuarticFourSignedPolePair.literalPole_cancel
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.poleTwo *
        poleProjectiveDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          t (t/16)
      +
      (-W.poleHalf) *
        poleProjectiveDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          t (t/16)
      = 0 := by
  rw [poleProjectiveDefect_quarticFourPhysicalDetector_eq
      W.Rpos ht,
      poleProjectiveDefect_quarticFourPhysicalDetector_eq
      W.Rpos ht]
  unfold QuarticFourSignedPolePair.poleHalf
    QuarticFourSignedPolePair.poleTwo
  ring

def QuarticFourSignedPolePair.physicalCombinedHeightDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (a : ℝ) : ℝ :=
  W.poleTwo *
      heightDefect
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        (t/16) a 0
    +
  (-W.poleHalf) *
      heightDefect
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        (t/16) a 0

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_scaled
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (a : ℝ) :
    W.physicalCombinedHeightDefect a
      =
    (1/(t/16)^2) *
      quarticFourSignedPoleCombinedHeightDefect
        W.R W.muHalf W.muTwo t (a/(t/16)) := by
  have hr : 0 < t/16 := by positivity
  unfold QuarticFourSignedPolePair.physicalCombinedHeightDefect
    quarticFourSignedPoleCombinedHeightDefect
    quarticFourPhysicalDetector
  rw [heightDefect_projectiveRescale_zero hr a,
      heightDefect_projectiveRescale_zero hr a]
  unfold QuarticFourSignedPolePair.poleHalf
    QuarticFourSignedPolePair.poleTwo
  ring

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_nonneg
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    0 <= W.physicalCombinedHeightDefect (heightOf rho) := by
  by_cases ha : heightOf rho = 0
  · rw [ha]
    unfold QuarticFourSignedPolePair.physicalCombinedHeightDefect
    simp [heightDefect_self]
  · have hr : 0 < t/16 := by positivity
    have hstrip := zetaZero_height_abs_le_half rho
    have hnorm0 : 0 < |heightOf rho/(t/16)| := by
      rw [abs_pos]
      exact div_ne_zero ha hr.ne'
    have hnorm :
        |heightOf rho/(t/16)| <= 8/t := by
      rw [abs_div, abs_of_pos hr]
      rw [div_le_div_iff₀ hr ht]
      nlinarith
    have hband :=
      W.combinedTargetBand
        (heightOf rho/(t/16)) hnorm0
        (hnorm.trans_lt hhigh)
    rw [W.physicalCombinedHeightDefect_scaled ht]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    exact (mul_pos hfac hband).le

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_pos
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.physicalCombinedHeightDefect (heightOf rho) := by
  have hr : 0 < t/16 := by positivity
  have hstrip := zetaZero_height_abs_le_half rho
  have hnorm0 : 0 < |heightOf rho/(t/16)| := by
    rw [abs_pos]
    exact div_ne_zero hoff hr.ne'
  have hnorm :
      |heightOf rho/(t/16)| <= 8/t := by
    rw [abs_div, abs_of_pos hr]
    rw [div_le_div_iff₀ hr ht]
    nlinarith
  have hband :=
    W.combinedTargetBand
      (heightOf rho/(t/16)) hnorm0
      (hnorm.trans_lt hhigh)
  rw [W.physicalCombinedHeightDefect_scaled ht]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  exact mul_pos hfac hband

def QuarticFourSignedPolePair.combinedZeroHeightDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) *
    W.physicalCombinedHeightDefect (heightOf rho)

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_nonneg
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros) :
    0 <= W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_nonneg (by positivity)
    (W.physicalCombinedHeightDefect_nonneg ht hhigh rho)

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_pos
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_pos (by positivity)
    (W.physicalCombinedHeightDefect_pos ht hhigh rho hoff)

end Synthesis
