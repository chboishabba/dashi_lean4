import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareCarrierAudit
import Synthesis.RiemannSelectedSignedFifthCorrelationGapAudit

/-!
# RH post-merge analytic max-cut

This file is deliberately post-merge and analytic-facing.  It does not add a
new terminal certificate.  It records the exact primitive content of the A2
threshold, splits the remaining positive local A2 debt into its four literal
coordinates, and states Route B with the independently required boundary/limit
obligations visible.

The live research leaves remain analytic:

* A2: local positive debt + signed FarExact < explicit compensation + mu gain;
* A1: literal chart-to-shell summation, then curvature and compensation;
* B: eventual signed-cap gap, together with boundary decay and outer-terminal
  convergence.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- The A2 target contains only the selected zero-height defect and the exact
smooth `mu` integral.  No abstract high-ordinate contradiction proposition is
hidden in this definition. -/
theorem QuarticFourSignedPolePair.compensationTargetThreshold_eq_explicit
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.compensationTargetThreshold rho
      = 4 * W.combinedZeroHeightDefect rho
        + ∫ tau : ℝ, W.signedOrdinateTest tau * Zeta23.mu tau := by
  rfl

/-- Vertical RvM-discrepancy part of the positive A2 local debt. -/
def QuarticFourSignedPolePair.postSixthTerminalVerticalDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) : ℝ :=
  W.targetStrength / (6 * (t/16)^6) * EV

/-- Expanded-window count part of the positive quartic A2 local debt. -/
def QuarticFourSignedPolePair.postSixthTerminalCountDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  W.targetStrength / (6 * (t/16)^6)
    * ((3/2 : ℝ) * r^2 * NZ)

/-- Selected-M6 sixth-order positive cap inside the terminal A2 local debt. -/
def QuarticFourSignedPolePair.postSixthTerminalSixthDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8)) * NZ

/-- Eighth-and-higher positive cap, cross-welded to the selected G1
`fourthLipschitz` constant. -/
def QuarticFourSignedPolePair.postSixthTerminalEighthDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10) * NZ

/-- Exact decomposition of the remaining non-favorable local A2 quantity.
This is an identity, not a new analytic hypothesis. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLocalPositiveDebt_eq_four_debts
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLocalPositiveDebt EV
      = W.postSixthTerminalVerticalDebt EV
        + W.postSixthTerminalCountDebt
        + W.postSixthTerminalSixthDebt
        + W.postSixthTerminalEighthDebt := by
  unfold QuarticFourSignedPolePair.postSixthTerminalLocalPositiveDebt
    QuarticFourSignedPolePair.postSixthTerminalVerticalDebt
    QuarticFourSignedPolePair.postSixthTerminalCountDebt
    QuarticFourSignedPolePair.postSixthTerminalSixthDebt
    QuarticFourSignedPolePair.postSixthTerminalEighthDebt
  dsimp
  ring

/-- The dominant selected-sixth coefficient leaves genuine positive headroom
against every strength-floor witness. -/
def QuarticFourSignedPolePair.postSixthTerminalDominantHeadroom
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.targetStrength - quarticSignedPoleTerminalM6DominantAllowance

theorem QuarticFourSignedPolePair.postSixthTerminalDominantHeadroom_pos
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hfloor : quarticSignedPoleStrengthFloor <= W.targetStrength) :
    0 < W.postSixthTerminalDominantHeadroom := by
  unfold QuarticFourSignedPolePair.postSixthTerminalDominantHeadroom
  have h := W.terminalM6DominantAllowance_lt_targetStrength hfloor
  linarith

/-- Route B is not closed by the eventual signed-cap theorem alone: boundary
decay and outer-terminal convergence are independent obligations.  Once those
are paid, eventual direct gap nonnegativity supplies the packaged analytic
input with no credit/debt split. -/
theorem QuarticFourSignedPolePair.signedFifthAnalyticInput_of_eventual_direct_gap
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (heps : 0 < eps)
    (hboundary :
      ∀ᶠ n : ℕ in atTop,
        |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hlarge :
      ∀ᶠ n : ℕ in atTop,
        quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        0 <= W.signedFifthCorrelationGapAt rho EV eps n)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.SignedFifthAnalyticInput rho EV eps := by
  have hinterior : W.SignedFifthInteriorTarget rho EV eps := by
    filter_upwards [hlarge, hgap] with n hn hg
    exact (W.signedFifthCorrelationGapAt_nonneg_iff_cap
      ht rho n hn).mp hg
  exact W.signedFifthAnalyticInput_of_interiorTarget
    rho heps hboundary hinterior hlim

/-- Same Route-B cut stated directly on the signed physical cap. -/
theorem QuarticFourSignedPolePair.signedFifthAnalyticInput_of_eventual_cap
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (heps : 0 < eps)
    (hboundary :
      ∀ᶠ n : ℕ in atTop,
        |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hcap : W.SignedFifthInteriorTarget rho EV eps)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.SignedFifthAnalyticInput rho EV eps := by
  exact W.signedFifthAnalyticInput_of_interiorTarget
    rho heps hboundary hcap hlim

end Synthesis
