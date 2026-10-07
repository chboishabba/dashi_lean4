import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareCarrierAudit
import Synthesis.RiemannSelectedSignedFifthCorrelationGapAudit

/-!
# RH post-merge analytic max-cut

This file is deliberately post-merge and analytic-facing.  It does not add a
new terminal certificate.  It records the exact primitive content of the A2
threshold, splits the remaining positive local A2 debt into its literal
coordinates, and states Route B with the independently required boundary/limit
obligations visible.

The live research leaves remain analytic:

* A2: local positive debt + signed FarExact < explicit compensation + mu gain;
* A1: literal chart-to-shell summation, then curvature and compensation;
* B: eventual signed-cap gap, together with boundary decay and outer-terminal
  convergence.

## Fail-closed audit classes

The accounting convention for this file is documentary, not a new proposition
layer:

* `K`: kernel/source theorem already present in the proof graph;
* `U`: standard unconditional analytic input, once instantiated on the literal
  carrier used here;
* `O`: genuinely open scalar/limit estimate;
* `C`: circular, RH-equivalent, or logically inert as an RH producer.

For the live A2 route: correct polarity, the selected terminal M6 interval,
dominant M6 headroom, the positive canonical mu gain, the exact four-debt split,
and the exact far base/horizontal carrier decompositions are `K`.  Concrete RvM
and local-zero-count bounds are `K/U` only where the repository has already
instantiated them on the same literal windows.  The residual sixth/eighth
constant comparison, a selected-witness horizontal far-curvature bound, and the
completed compensation lower bound remain `O`.  Any pole-quotient/high-zero
hypothesis equivalent to RH is `C` and contributes no proof-distance reduction.

The exact envelope algebra below corrects one tempting but false asymptotic
shortcut: both the selected-M6 sixth cap and the G1-welded eighth cap have a
leading term proportional to `NZ / (t/16)^2`.  Thus neither may be dismissed as
lower order relative to the smooth-mu gain merely from its nominal Taylor
order.  Their coefficients must be compared on the selected witness.
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

/-- The two coordinates that survive at the leading local
`expanded-count / scale^2` level. -/
def QuarticFourSignedPolePair.postSixthTerminalLeadingLocalDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.postSixthTerminalSixthDebt + W.postSixthTerminalEighthDebt

/-- The RvM discrepancy and elementary quartic count coordinates. -/
def QuarticFourSignedPolePair.postSixthTerminalLowerOrderLocalDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) : ℝ :=
  W.postSixthTerminalVerticalDebt EV + W.postSixthTerminalCountDebt

/-- Pure reassociation: the A2 local debt is lower-order coordinates plus the
two leading-scale sixth/eighth coordinates. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLocalPositiveDebt_eq_lower_add_leading
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLocalPositiveDebt EV
      = W.postSixthTerminalLowerOrderLocalDebt EV
        + W.postSixthTerminalLeadingLocalDebt := by
  rw [W.postSixthTerminalLocalPositiveDebt_eq_four_debts]
  unfold QuarticFourSignedPolePair.postSixthTerminalLowerOrderLocalDebt
    QuarticFourSignedPolePair.postSixthTerminalLeadingLocalDebt
  ring

/-- Exact canonical-radius expansion of the selected-sixth phase envelope.
The final term is `eta0^6 * (t/16)^6`; after the terminal `/(t/16)^8`
normalization it contributes at the `1/(t/16)^2` level. -/
theorem quarticSignedPoleLocalSixthPhaseEnvelope_canonical_eq
    (t : ℝ) :
    quarticSignedPoleLocalSixthPhaseEnvelope
        t quarticSignedPoleCanonicalLocalRadius
      =
    (1/2 : ℝ)^6
      + 15 * (1/2 : ℝ)^4
          * quarticSignedPoleCanonicalLocalRadius^2 * (t/16)^2
      + 15 * (1/2 : ℝ)^2
          * quarticSignedPoleCanonicalLocalRadius^4 * (t/16)^4
      + quarticSignedPoleCanonicalLocalRadius^6 * (t/16)^6 := by
  unfold quarticSignedPoleLocalSixthPhaseEnvelope
    quarticSignedPoleLocalHalfWidth
  ring

/-- Exact canonical-radius expansion of the eighth remainder envelope.
Its `r^8/17000` term likewise becomes a `1/(t/16)^2` contribution after the
terminal `/(t/16)^10` normalization.  The remaining mixed terms carry extra
inverse powers of the high-ordinate scale. -/
theorem quarticSignedPoleLocalEighthPhysicalEnvelope_canonical_eq
    (t : ℝ) :
    quarticSignedPoleLocalEighthPhysicalEnvelope
        t quarticSignedPoleCanonicalLocalRadius
      =
    (1/30000 : ℝ) * (1/2 : ℝ)^8
      + (1/17000 : ℝ)
          * quarticSignedPoleCanonicalLocalRadius^8 * (t/16)^8
      + (1/300 : ℝ)
          * ((1/2 : ℝ)^2
                * quarticSignedPoleCanonicalLocalRadius^6 * (t/16)^6
            + (1/2 : ℝ)^4
                * quarticSignedPoleCanonicalLocalRadius^4 * (t/16)^4
            + (1/2 : ℝ)^6
                * quarticSignedPoleCanonicalLocalRadius^2 * (t/16)^2) := by
  unfold quarticSignedPoleLocalEighthPhysicalEnvelope
    quarticSignedPoleLocalHalfWidth
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
