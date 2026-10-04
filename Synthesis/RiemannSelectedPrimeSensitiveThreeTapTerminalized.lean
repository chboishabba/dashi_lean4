import Synthesis.RiemannSelectedPrimeSensitiveThreeTapLocalBudget

/-!
# Fully target-terminalized three-tap margin

The transformed selected-zero target is now source-native and exactly quadratic.
This file removes the remaining target placeholder from the terminal test.

The transformed local slack remains an explicit argument because its absolute
M6/M8 estimate is still the analytic debt.  All other terms are same-object.
-/

noncomputable section
namespace Synthesis

open scoped Real

def QuarticFourSignedPolePair.threeTapSelectedTerminalMargin
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) (localSlack : ℝ) : ℝ :=
  2 * W.threeTapCombinedZeroHeightDefect eps rho
    - (W.threeTapCompletedExternal eps
        + (1/2 : ℝ) * localSlack)

theorem QuarticFourSignedPolePair.threeTapCompletedExternal_zero
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCompletedExternal 0
      = W.completedSignedResidual := by
  rw [W.threeTapCompletedExternal_eq_cluster ht]
  rw [W.completedSignedResidual_eq_combinedCluster ht]
  unfold QuarticFourSignedPolePair.threeTapChannelCombination
    QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapTwo
    QuarticFourSignedPolePair.combinedCluster
    detectorThreeTap
  simp

theorem QuarticFourSignedPolePair.threeTapSelectedTerminalMargin_zero
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapSelectedTerminalMargin
        0 rho (W.canonicalLocalBudgetSlack EV)
      =
    W.canonicalTerminalMargin rho EV := by
  unfold QuarticFourSignedPolePair.threeTapSelectedTerminalMargin
    QuarticFourSignedPolePair.canonicalTerminalMargin
  rw [W.threeTapCombinedZeroHeightDefect_zero rho,
      W.threeTapCompletedExternal_zero ht]

/-- Exact requested terminal increment after substituting the transformed
selected-zero target. -/
theorem QuarticFourSignedPolePair.threeTapSelectedTerminalMargin_sub_canonical
    {t eps localSlack EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapSelectedTerminalMargin eps rho localSlack
      - W.canonicalTerminalMargin rho EV
    =
    2*eps * W.threeTapCombinedTargetLinearCoeff rho
      + 2*eps^2 * W.threeTapCombinedTargetQuadraticCoeff rho
      - (W.threeTapCompletedExternal eps - W.completedSignedResidual)
      - (1/2 : ℝ) *
          (localSlack - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapSelectedTerminalMargin
    QuarticFourSignedPolePair.canonicalTerminalMargin
  rw [W.threeTapCombinedZeroHeightDefect_quadratic ht rho]
  ring

/-- Prime resonance leaves the target polynomial, off/Gamma/pole increment,
and transformed local slack. -/
theorem QuarticFourSignedPolePair.threeTapSelectedTerminalMargin_sub_canonical_at_resonance
    {t eps localSlack EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapSelectedTerminalMargin eps rho localSlack
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
          (localSlack - W.canonicalLocalBudgetSlack EV) := by
  rw [W.threeTapSelectedTerminalMargin_sub_canonical ht rho]
  rw [W.threeTapCompletedExternal_at_resonance ht hphase]

theorem QuarticFourSignedPolePair.threeTapSelectedTerminalMargin_target_zero_at_line
    {t eps localSlack : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hline : heightOf rho = 0) :
    W.threeTapSelectedTerminalMargin eps rho localSlack
      =
    -(W.threeTapCompletedExternal eps
        + (1/2 : ℝ) * localSlack) := by
  unfold QuarticFourSignedPolePair.threeTapSelectedTerminalMargin
  rw [W.threeTapCombinedZeroHeightDefect_at_line rho hline]
  ring

end Synthesis
