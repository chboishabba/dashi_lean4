import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleA2LeadingConstantCut

/-!
# A2 selected-witness fourth-Lipschitz max-cut

The leading sixth/eighth comparison is already equivalent to a bound on the
same selected witness's G1 `fourthLipschitz`.  This file removes the remaining
witness-dependent threshold bookkeeping.

For every strength-floor witness the admissible fourth-Lipschitz threshold is
at least the single explicit scalar

  (strengthFloor - selectedSixthAllowance)
    / ((3/1700) * eta0^2).

Numerically this scalar is about 737.365.  The numerical value is diagnostic
only; the kernel-facing cut below keeps the exact real expression.

Consequently the current positive-eighth-cap A2 lane has one exact selected
witness task: construct the already-required strength-floor witness with
`fourthLipschitz` strictly below this floor threshold.  The old generic
support/L1 constant is deliberately not substituted here: it is a much coarser
upper bound and cannot decide the selected witness.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- Uniform headroom available even at the minimum selected target strength. -/
def quarticSignedPoleFloorDominantHeadroom : ℝ :=
  quarticSignedPoleStrengthFloor
    - quarticSignedPoleTerminalM6DominantAllowance

/-- Exact witness-independent fourth-Lipschitz ceiling sufficient for every
strength-floor selected witness. -/
def quarticSignedPoleFloorFourthLipschitzThreshold : ℝ :=
  quarticSignedPoleFloorDominantHeadroom /
    ((3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2)

theorem quarticSignedPoleFloorDominantHeadroom_pos :
    0 < quarticSignedPoleFloorDominantHeadroom := by
  unfold quarticSignedPoleFloorDominantHeadroom
  exact sub_pos.mpr
    quarticSignedPoleTerminalM6DominantAllowance_lt_strengthFloor

theorem quarticSignedPoleFloorFourthLipschitzThreshold_pos :
    0 < quarticSignedPoleFloorFourthLipschitzThreshold := by
  have hc :
      0 < (3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2 := by
    unfold quarticSignedPoleCanonicalLocalRadius
    positivity
  unfold quarticSignedPoleFloorFourthLipschitzThreshold
  exact div_pos quarticSignedPoleFloorDominantHeadroom_pos hc

/-- Any floor-certified witness has at least the floor-level fourth-Lipschitz
headroom. -/
theorem QuarticFourSignedPolePair.floorFourthLipschitzThreshold_le_selected
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hfloor : quarticSignedPoleStrengthFloor <= W.targetStrength) :
    quarticSignedPoleFloorFourthLipschitzThreshold
      <= W.postSixthTerminalFourthLipschitzThreshold := by
  have hc :
      0 <= (3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2 := by
    unfold quarticSignedPoleCanonicalLocalRadius
    positivity
  unfold quarticSignedPoleFloorFourthLipschitzThreshold
    quarticSignedPoleFloorDominantHeadroom
    QuarticFourSignedPolePair.postSixthTerminalFourthLipschitzThreshold
    QuarticFourSignedPolePair.postSixthTerminalDominantHeadroom
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right hfloor quarticSignedPoleTerminalM6DominantAllowance)
    hc

/-- This is the exact sufficient selected-witness producer for the present A2
positive-eighth-cap lane.  No asymptotic or external certificate remains in
the leading comparison once these two same-witness inequalities are supplied. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_lt_target_of_floor_K
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hfloor : quarticSignedPoleStrengthFloor <= W.targetStrength)
    (hK : W.fourthLipschitz
      < quarticSignedPoleFloorFourthLipschitzThreshold) :
    W.postSixthTerminalLeadingAllowance < W.targetStrength := by
  have hthreshold := W.floorFourthLipschitzThreshold_le_selected hfloor
  have hKselected :
      W.fourthLipschitz < W.postSixthTerminalFourthLipschitzThreshold :=
    hK.trans_le hthreshold
  exact
    (W.postSixthTerminalLeadingAllowance_lt_target_iff_fourthLipschitz).2
      hKselected

end Synthesis
