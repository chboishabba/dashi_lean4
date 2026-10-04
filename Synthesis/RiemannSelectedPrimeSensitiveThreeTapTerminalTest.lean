import Synthesis.RiemannSelectedPrimeSensitiveThreeTapIncrementAudit
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal

/-!
# RH three-tap terminal-margin decision surface

This file makes the Clay-facing test explicit. The canonical selected witness
already has a single exact positive-margin scalar. For a translated detector
we keep the changed same-ordinate target and changed local budget visible
instead of silently reusing the unperturbed ones.

No RH estimate is assumed or proved here.
-/

noncomputable section
namespace Synthesis
open scoped Real

def QuarticFourSignedPolePair.canonicalTerminalMargin
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : ℝ :=
  2 * W.combinedZeroHeightDefect rho
    - (W.completedSignedResidual
        + (1/2 : ℝ) * W.canonicalLocalBudgetSlack EV)

theorem QuarticFourSignedPolePair.canonicalTerminalMargin_pos_iff_highCut
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 < W.canonicalTerminalMargin rho EV
      ↔ W.PostSixthCanonicalSignedHighCut rho EV := by
  rw [W.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack ht rho]
  unfold QuarticFourSignedPolePair.canonicalTerminalMargin
  constructor <;> intro h <;> linarith

def QuarticFourSignedPolePair.threeTapCompletedExternal
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    + W.threeTapSignedPrimeCombination eps
    + W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    + W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect

theorem QuarticFourSignedPolePair.threeTapCompletedExternal_eq_cluster
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCompletedExternal eps
      =
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect := by
  have h := W.threeTapCompletedCluster_eq_off_add_arithmetic ht (eps := eps)
  unfold QuarticFourSignedPolePair.threeTapCompletedExternal
    QuarticFourSignedPolePair.threeTapCompletedArithmetic at h ⊢
  linarith

theorem QuarticFourSignedPolePair.threeTapCompletedExternal_at_resonance
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapCompletedExternal eps
      =
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    + W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    + W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect := by
  unfold QuarticFourSignedPolePair.threeTapCompletedExternal
  rw [W.threeTapSignedPrime_eq_zero_at_resonance ht hphase]
  ring

def QuarticFourSignedPolePair.threeTapTerminalMargin
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps target localSlack : ℝ) : ℝ :=
  2 * target
    - (W.threeTapCompletedExternal eps
        + (1/2 : ℝ) * localSlack)

theorem QuarticFourSignedPolePair.threeTapTerminalMargin_sub_canonical
    {t eps target localSlack EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapTerminalMargin eps target localSlack
      - W.canonicalTerminalMargin rho EV
    =
    2 * (target - W.combinedZeroHeightDefect rho)
      - (W.threeTapCompletedExternal eps - W.completedSignedResidual)
      - (1/2 : ℝ) * (localSlack - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapTerminalMargin
    QuarticFourSignedPolePair.canonicalTerminalMargin
  ring

theorem QuarticFourSignedPolePair.threeTapTerminalMargin_sub_canonical_at_resonance
    {t eps target localSlack EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapTerminalMargin eps target localSlack
      - W.canonicalTerminalMargin rho EV
    =
    2 * (target - W.combinedZeroHeightDefect rho)
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
      - (1/2 : ℝ) * (localSlack - W.canonicalLocalBudgetSlack EV) := by
  rw [W.threeTapTerminalMargin_sub_canonical rho]
  rw [W.threeTapCompletedExternal_at_resonance ht hphase]

theorem heightDefect_at_zero_height
    (g : ℝ -> ℝ) (r : ℝ) :
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
      g r 0 0 = 0 := by
  unfold Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
  ring

theorem no_positive_floor_from_heightDefect_at_zero
    (g : ℝ -> ℝ) (r delta : ℝ)
    (hdelta : 0 < delta) :
    ¬ delta <=
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
        g r 0 0 := by
  rw [heightDefect_at_zero_height]
  linarith

end Synthesis
