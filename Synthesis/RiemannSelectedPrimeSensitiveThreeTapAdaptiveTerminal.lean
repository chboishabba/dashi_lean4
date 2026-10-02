import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveOffOrdWeld
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTerminalized

/-!
# Paid finite adaptive local budget and terminal scalar

The transformed local source is now same-object:
  1/2 * finite adaptive reflection-pair sum.

Its exact degree-six decomposition and eighth-order debt give the finite upper
budget
  1/2 * (jet + abs-remainder-debt).

The resulting slack is definitionally tied to the transformed detector and is
nonnegative. Substituting it into the selected terminal margin removes the
free localSlack parameter at finite cutoff.

What remains after this file is:
* stabilization/exhaustion of the finite adaptive-local set into the exact
  global local/far split;
* sign control of the live degree-two/degree-four/degree-six jet;
* completed resonance / near-line sign.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

def QuarticFourSignedPolePair.threeTapAdaptiveLocalExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ :=
  (1/2 : ℝ) * W.threeTapAdaptiveLocalPairAt eps n

def QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ :=
  (1/2 : ℝ) *
    (W.threeTapAdaptiveLocalJetAt eps n
      + W.threeTapAdaptiveLocalRemainderDebtAt eps n)

def QuarticFourSignedPolePair.threeTapAdaptiveLocalSlackAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ :=
  W.threeTapAdaptiveLocalBudgetAt eps n
    - W.threeTapAdaptiveLocalExactAt eps n

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalExactAt_le_budget
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalExactAt eps n
      <= W.threeTapAdaptiveLocalBudgetAt eps n := by
  rw [show
      W.threeTapAdaptiveLocalExactAt eps n
        =
      (1/2 : ℝ) *
        (W.threeTapAdaptiveLocalJetAt eps n
          + W.threeTapAdaptiveLocalRemainderAt eps n) by
      unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalExactAt
      rw [W.threeTapAdaptiveLocalPairAt_eq_jet_add_remainder]]
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt
  have h :=
    W.threeTapAdaptiveLocalRemainderAt_le_debt (eps:=eps) n
  nlinarith

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalSlackAt_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.threeTapAdaptiveLocalSlackAt eps n := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalSlackAt
  exact sub_nonneg.mpr W.threeTapAdaptiveLocalExactAt_le_budget

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt_le_jet_add_expandedDebt
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalBudgetAt eps n
      <=
    (1/2 : ℝ) *
      (
        W.threeTapAdaptiveLocalJetAt eps n
        +
        ((W.threeTapAdaptiveMixedEnvelope
            * W.threeTapNormalizedProjectiveAbsMomentEight eps)
          / (t/16)^2)
          *
        (zetaZeroConfig.N
          (t - quarticSignedPoleLocalHalfWidth
            t W.threeTapAdaptiveLocalRadius - 1)
          (t + quarticSignedPoleLocalHalfWidth
            t W.threeTapAdaptiveLocalRadius) : ℝ)
      ) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt
  have h :=
    W.threeTapAdaptiveLocalRemainderDebtAt_le_expandedWindowN ht (eps:=eps) n
  nlinarith

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) (n : ℕ) : ℝ :=
  W.threeTapSelectedTerminalMargin eps rho
    (W.threeTapAdaptiveLocalSlackAt eps n)

/-- Exact finite-cut terminal increment with no free transformed local slack. -/
theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt_sub_canonical
    {t eps EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ) :
    W.threeTapAdaptiveTerminalMarginAt eps rho n
      - W.canonicalTerminalMargin rho EV
    =
    2*eps * W.threeTapCombinedTargetLinearCoeff rho
      + 2*eps^2 * W.threeTapCombinedTargetQuadraticCoeff rho
      - (W.threeTapCompletedExternal eps - W.completedSignedResidual)
      - (1/2 : ℝ) *
          (W.threeTapAdaptiveLocalSlackAt eps n
            - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt
  exact W.threeTapSelectedTerminalMargin_sub_canonical ht rho

/-- Resonance specialization of the now-local-budget-paid finite terminal
margin. The prime channel is absent exactly. -/
theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt_sub_canonical_at_resonance
    {t eps EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapAdaptiveTerminalMarginAt eps rho n
      - W.canonicalTerminalMargin rho EV
    =
    2*eps * W.threeTapCombinedTargetLinearCoeff rho
      + 2*eps^2 * W.threeTapCombinedTargetQuadraticCoeff rho
      -
      (
        W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        + W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
        + W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
        - W.completedSignedResidual
      )
      - (1/2 : ℝ) *
          (W.threeTapAdaptiveLocalSlackAt eps n
            - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt
  exact
    W.threeTapSelectedTerminalMargin_sub_canonical_at_resonance
      ht rho hphase

def QuarticFourSignedPolePair.ThreeTapAdaptiveTerminalPositiveAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) (n : ℕ) : Prop :=
  0 < W.threeTapAdaptiveTerminalMarginAt eps rho n

end Synthesis
