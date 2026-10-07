import Synthesis.RiemannPostMergeAnalyticMaxCut

/-!
# A2 leading sixth/eighth constant cut

The canonical-radius envelope audit shows that the selected-M6 sixth cap and
the G1-welded eighth cap share the same leading local
`expandedZeroCount / (t/16)^2` scale.  The meaningful comparison is therefore
at coefficient level.

For eta0 = 1/(pi+1), the sixth coefficient normalized against the leading
smooth-mu gain is exactly the already-paid dominant allowance

  A6 = pi^6 * eta0^2 / 160,

stored in the repository as `quarticSignedPoleTerminalM6DominantAllowance`.

The leading eighth coefficient contributes

  A8(W) = (3/1700) * eta0^2 * W.fourthLipschitz.

Thus the leading local A2 comparison is exactly

  A6 + A8(W) < W.targetStrength.

This file exposes that scalar directly.  It does not claim a numerical bound on
`W.fourthLipschitz`; that remains the selected-witness producer to be checked
against the existing G1 corridor.  Nor does this statement pay the lower-order,
far, or completed-compensation coordinates.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- Leading eighth-order allowance after normalizing the `r^8/17000` envelope
term against the canonical smooth-mu leading coefficient. -/
def QuarticFourSignedPolePair.postSixthTerminalEighthLeadingAllowance
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (3/1700 : ℝ)
    * quarticSignedPoleCanonicalLocalRadius^2
    * W.fourthLipschitz

/-- Total leading local allowance: paid selected-sixth allowance plus the
selected G1-welded eighth allowance. -/
def QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticSignedPoleTerminalM6DominantAllowance
    + W.postSixthTerminalEighthLeadingAllowance

/-- The existing dominant headroom is exactly what is left for the eighth
leading allowance. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_lt_target_iff
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLeadingAllowance < W.targetStrength
      ↔
    W.postSixthTerminalEighthLeadingAllowance
      < W.postSixthTerminalDominantHeadroom := by
  unfold QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance
    QuarticFourSignedPolePair.postSixthTerminalDominantHeadroom
  constructor <;> intro h <;> linarith

/-- A concrete selected-witness eighth allowance below the already-paid sixth
headroom closes the leading local coefficient comparison. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_lt_target_of_eighth
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (h8 :
      W.postSixthTerminalEighthLeadingAllowance
        < W.postSixthTerminalDominantHeadroom) :
    W.postSixthTerminalLeadingAllowance < W.targetStrength := by
  exact
    (W.postSixthTerminalLeadingAllowance_lt_target_iff).2 h8

/-- Conversely, failure of the eighth allowance to fit inside the sixth
headroom is an exact leading-coefficient no-go for this positive-cap route.
This is not a no-go for A2 as a whole if a sharper signed eighth treatment
replaces the current positive cap. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_not_lt_target_of_headroom_le_eighth
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (h8 :
      W.postSixthTerminalDominantHeadroom
        <= W.postSixthTerminalEighthLeadingAllowance) :
    ¬ W.postSixthTerminalLeadingAllowance < W.targetStrength := by
  intro h
  have := (W.postSixthTerminalLeadingAllowance_lt_target_iff).1 h
  linarith

/-- The selected eighth leading allowance is nonnegative. -/
theorem QuarticFourSignedPolePair.postSixthTerminalEighthLeadingAllowance_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.postSixthTerminalEighthLeadingAllowance := by
  unfold QuarticFourSignedPolePair.postSixthTerminalEighthLeadingAllowance
  have heta : 0 <= quarticSignedPoleCanonicalLocalRadius^2 := sq_nonneg _
  have hK : 0 <= W.fourthLipschitz := by
    unfold QuarticFourSignedPolePair.fourthLipschitz
      compactCoshFourthLipschitzConstant
    positivity
  positivity

end Synthesis
