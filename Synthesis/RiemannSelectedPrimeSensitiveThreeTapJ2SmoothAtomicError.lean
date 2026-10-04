import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2AtomicRobustness
import Synthesis.RiemannProjectiveQuarticFourWindowPoleLocalization

/-!
# Exact smooth-to-atomic error decomposition for transformed J2 coefficients

The transformed normalized J2 coefficients depend on four scalar coordinates

  A1 = evenResp g 0 1,  A2 = evenResp g 0 2,
  U1 = integral g(u) u sin u,  U2 = integral g(u) u sin(2u),

and on the finite-t pole weights selecting the two endpoint detectors.

The preceding robustness file proves uniform smooth-to-atomic convergence of
all four phase coordinates.  The existing pole-localization file proves the
same for the finite-t pole coordinates.  This file supplies the exact algebraic
compiler between those two inputs and the actual selected coefficients.

No phase sign is assumed: B=(t/16)log 2 is oscillatory.  Instead we expose the
complete error identity.  Any atomic sign margin larger than the displayed
smooth error therefore transfers to the literal selected smooth witness.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real

def j2PhaseLinearFromCoordinates
    (B A1 A2 U1 U2 : ℝ) : ℝ :=
  2 * B^2 * A1 * A2 * (Real.cos (2*B) - Real.cos B)
    +
  4 * B *
    (A2 * Real.sin B * U1
      - A1 * Real.sin (2*B) * U2)

def j2PhaseQuadraticFromCoordinates
    (B A1 A2 U1 U2 : ℝ) : ℝ :=
  8 * B *
    (Real.cos (2*B) * A2 * Real.sin B * U1
      - Real.cos B * A1 * Real.sin (2*B) * U2)

theorem normalizedJ2LinearPhase_eq_coordinates
    (g : ℝ → ℝ) (B : ℝ) :
    normalizedJ2LinearPhase g B
      =
    j2PhaseLinearFromCoordinates B
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 1)
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 2)
      (projectiveSinFirstResp g 1)
      (projectiveSinFirstResp g 2) := by
  unfold normalizedJ2LinearPhase j2PhaseLinearFromCoordinates
  rfl

theorem normalizedJ2QuadraticPhase_eq_coordinates
    (g : ℝ → ℝ) (B : ℝ) :
    normalizedJ2QuadraticPhase g B
      =
    j2PhaseQuadraticFromCoordinates B
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 1)
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 2)
      (projectiveSinFirstResp g 1)
      (projectiveSinFirstResp g 2) := by
  unfold normalizedJ2QuadraticPhase j2PhaseQuadraticFromCoordinates
  rfl

theorem quarticFourAtomicThreeTapJ2LinearPhase_eq_coordinates
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2LinearPhase lam mu B
      =
    j2PhaseLinearFromCoordinates B
      (quarticFourAtomicRespAt lam mu 1)
      (quarticFourAtomicRespAt lam mu 2)
      (quarticFourAtomicSinFirstRespAt lam mu 1)
      (quarticFourAtomicSinFirstRespAt lam mu 2) := by
  unfold quarticFourAtomicThreeTapJ2LinearPhase
    j2PhaseLinearFromCoordinates
  rfl

theorem quarticFourAtomicThreeTapJ2QuadraticPhase_eq_coordinates
    (lam mu B : ℝ) :
    quarticFourAtomicThreeTapJ2QuadraticPhase lam mu B
      =
    j2PhaseQuadraticFromCoordinates B
      (quarticFourAtomicRespAt lam mu 1)
      (quarticFourAtomicRespAt lam mu 2)
      (quarticFourAtomicSinFirstRespAt lam mu 1)
      (quarticFourAtomicSinFirstRespAt lam mu 2) := by
  unfold quarticFourAtomicThreeTapJ2QuadraticPhase
    j2PhaseQuadraticFromCoordinates
  rfl

/-- Exact perturbation identity for the epsilon-linear J2 phase coordinate. -/
theorem j2PhaseLinearFromCoordinates_sub
    (B A1 A2 U1 U2 a1 a2 u1 u2 : ℝ) :
    j2PhaseLinearFromCoordinates B A1 A2 U1 U2
      - j2PhaseLinearFromCoordinates B a1 a2 u1 u2
    =
    2 * B^2 * (Real.cos (2*B) - Real.cos B)
      * ((A1-a1)*A2 + a1*(A2-a2))
    +
    4 * B *
      (
        Real.sin B * ((A2-a2)*U1 + a2*(U1-u1))
        -
        Real.sin (2*B) * ((A1-a1)*U2 + a1*(U2-u2))
      ) := by
  unfold j2PhaseLinearFromCoordinates
  ring

/-- Exact perturbation identity for the epsilon-quadratic J2 phase coordinate. -/
theorem j2PhaseQuadraticFromCoordinates_sub
    (B A1 A2 U1 U2 a1 a2 u1 u2 : ℝ) :
    j2PhaseQuadraticFromCoordinates B A1 A2 U1 U2
      - j2PhaseQuadraticFromCoordinates B a1 a2 u1 u2
    =
    8 * B *
      (
        Real.cos (2*B) * Real.sin B
          * ((A2-a2)*U1 + a2*(U1-u1))
        -
        Real.cos B * Real.sin (2*B)
          * ((A1-a1)*U2 + a1*(U2-u2))
      ) := by
  unfold j2PhaseQuadraticFromCoordinates
  ring

def QuarticFourSignedPolePair.threeTapAtomicJ2LinearCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let B := threeTapNormalizedShift t (Real.log 2)
  quarticFourAtomicFinitePoleResidual t (2/3) W.muTwo
      * quarticFourAtomicThreeTapJ2LinearPhase
          (1/2) W.muHalf B
    -
  quarticFourAtomicFinitePoleResidual t (1/2) W.muHalf
      * quarticFourAtomicThreeTapJ2LinearPhase
          (2/3) W.muTwo B

def QuarticFourSignedPolePair.threeTapAtomicJ2QuadraticCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let B := threeTapNormalizedShift t (Real.log 2)
  quarticFourAtomicFinitePoleResidual t (2/3) W.muTwo
      * quarticFourAtomicThreeTapJ2QuadraticPhase
          (1/2) W.muHalf B
    -
  quarticFourAtomicFinitePoleResidual t (1/2) W.muHalf
      * quarticFourAtomicThreeTapJ2QuadraticPhase
          (2/3) W.muTwo B

/-- Exact determinant-style error split for the selected epsilon-linear
coefficient.  The four differences are precisely the already-owned smooth
pole and phase localization targets. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2LinearCoeff_sub_atomic
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedJ2LinearCoeff
      - W.threeTapAtomicJ2LinearCoeff
    =
    let B := threeTapNormalizedShift t (Real.log 2)
    let P2 :=
      quarticFourSmoothFinitePoleResidual W.R (2/3) W.muTwo t
    let p2 :=
      quarticFourAtomicFinitePoleResidual t (2/3) W.muTwo
    let P1 :=
      quarticFourSmoothFinitePoleResidual W.R (1/2) W.muHalf t
    let p1 :=
      quarticFourAtomicFinitePoleResidual t (1/2) W.muHalf
    let F1 :=
      normalizedJ2LinearPhase
        (quarticFourWindowProfile W.R (1/2) W.muHalf) B
    let f1 :=
      quarticFourAtomicThreeTapJ2LinearPhase
        (1/2) W.muHalf B
    let F2 :=
      normalizedJ2LinearPhase
        (quarticFourWindowProfile W.R (2/3) W.muTwo) B
    let f2 :=
      quarticFourAtomicThreeTapJ2LinearPhase
        (2/3) W.muTwo B
    (P2-p2)*F1 + p2*(F1-f1)
      - ((P1-p1)*F2 + p1*(F2-f2)) := by
  rw [W.threeTapNormalizedJ2LinearCoeff_eq_phase]
  unfold QuarticFourSignedPolePair.threeTapAtomicJ2LinearCoeff
    QuarticFourSignedPolePair.poleHalf
    QuarticFourSignedPolePair.poleTwo
  dsimp
  ring

/-- Exact determinant-style error split for the selected epsilon-quadratic
coefficient. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2QuadraticCoeff_sub_atomic
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedJ2QuadraticCoeff
      - W.threeTapAtomicJ2QuadraticCoeff
    =
    let B := threeTapNormalizedShift t (Real.log 2)
    let P2 :=
      quarticFourSmoothFinitePoleResidual W.R (2/3) W.muTwo t
    let p2 :=
      quarticFourAtomicFinitePoleResidual t (2/3) W.muTwo
    let P1 :=
      quarticFourSmoothFinitePoleResidual W.R (1/2) W.muHalf t
    let p1 :=
      quarticFourAtomicFinitePoleResidual t (1/2) W.muHalf
    let F1 :=
      normalizedJ2QuadraticPhase
        (quarticFourWindowProfile W.R (1/2) W.muHalf) B
    let f1 :=
      quarticFourAtomicThreeTapJ2QuadraticPhase
        (1/2) W.muHalf B
    let F2 :=
      normalizedJ2QuadraticPhase
        (quarticFourWindowProfile W.R (2/3) W.muTwo) B
    let f2 :=
      quarticFourAtomicThreeTapJ2QuadraticPhase
        (2/3) W.muTwo B
    (P2-p2)*F1 + p2*(F1-f1)
      - ((P1-p1)*F2 + p1*(F2-f2)) := by
  rw [W.threeTapNormalizedJ2QuadraticCoeff_eq_phase]
  unfold QuarticFourSignedPolePair.threeTapAtomicJ2QuadraticCoeff
    QuarticFourSignedPolePair.poleHalf
    QuarticFourSignedPolePair.poleTwo
  dsimp
  ring

/-- A negative atomic linear coefficient transfers as soon as the exact smooth
error is smaller than its atomic sign margin. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2LinearCoeff_neg_of_atomic_margin
    {t delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : W.threeTapAtomicJ2LinearCoeff <= -delta)
    (herr :
      |W.threeTapNormalizedJ2LinearCoeff
        - W.threeTapAtomicJ2LinearCoeff| < delta) :
    W.threeTapNormalizedJ2LinearCoeff < 0 := by
  have hlo := (abs_lt.mp herr).2
  linarith

/-- A positive atomic linear coefficient transfers under the symmetric margin
condition. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2LinearCoeff_pos_of_atomic_margin
    {t delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : delta <= W.threeTapAtomicJ2LinearCoeff)
    (herr :
      |W.threeTapNormalizedJ2LinearCoeff
        - W.threeTapAtomicJ2LinearCoeff| < delta) :
    0 < W.threeTapNormalizedJ2LinearCoeff := by
  have hlo := (abs_lt.mp herr).1
  linarith

/-- The same transfer principle for the quadratic coefficient. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2QuadraticCoeff_neg_of_atomic_margin
    {t delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : W.threeTapAtomicJ2QuadraticCoeff <= -delta)
    (herr :
      |W.threeTapNormalizedJ2QuadraticCoeff
        - W.threeTapAtomicJ2QuadraticCoeff| < delta) :
    W.threeTapNormalizedJ2QuadraticCoeff < 0 := by
  have hlo := (abs_lt.mp herr).2
  linarith

theorem QuarticFourSignedPolePair.threeTapNormalizedJ2QuadraticCoeff_pos_of_atomic_margin
    {t delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : delta <= W.threeTapAtomicJ2QuadraticCoeff)
    (herr :
      |W.threeTapNormalizedJ2QuadraticCoeff
        - W.threeTapAtomicJ2QuadraticCoeff| < delta) :
    0 < W.threeTapNormalizedJ2QuadraticCoeff := by
  have hlo := (abs_lt.mp herr).1
  linarith

end Synthesis
