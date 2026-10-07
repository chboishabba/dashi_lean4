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

/-- Exact selected-witness ceiling forced by the current positive eighth-order
cap.  This is the quantity that should be compared against the same-object G1
`fourthLipschitz`; no asymptotic order argument can replace this comparison. -/
def QuarticFourSignedPolePair.postSixthTerminalFourthLipschitzThreshold
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.postSixthTerminalDominantHeadroom /
    ((3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2)

/-- The current positive-cap leading A2 comparison is *exactly* an upper bound
on the selected witness's G1 fourth-Lipschitz constant. -/
theorem QuarticFourSignedPolePair.postSixthTerminalEighthLeadingAllowance_lt_headroom_iff_fourthLipschitz
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalEighthLeadingAllowance
        < W.postSixthTerminalDominantHeadroom
      ↔
    W.fourthLipschitz
        < W.postSixthTerminalFourthLipschitzThreshold := by
  have heta : 0 < quarticSignedPoleCanonicalLocalRadius := by
    unfold quarticSignedPoleCanonicalLocalRadius
    positivity
  have hc :
      0 < (3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2 := by
    positivity
  unfold QuarticFourSignedPolePair.postSixthTerminalFourthLipschitzThreshold
  rw [lt_div_iff₀ hc]
  unfold QuarticFourSignedPolePair.postSixthTerminalEighthLeadingAllowance
  ring_nf

/-- Hence the whole leading sixth-plus-eighth positive-cap lane closes iff the
same selected witness lies below the explicit fourth-Lipschitz ceiling. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_lt_target_iff_fourthLipschitz
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLeadingAllowance < W.targetStrength
      ↔
    W.fourthLipschitz
        < W.postSixthTerminalFourthLipschitzThreshold := by
  rw [W.postSixthTerminalLeadingAllowance_lt_target_iff]
  exact W.postSixthTerminalEighthLeadingAllowance_lt_headroom_iff_fourthLipschitz

/-- Under the already-used strength floor, the admissible selected-witness
fourth-Lipschitz interval is genuinely nonempty. -/
theorem QuarticFourSignedPolePair.postSixthTerminalFourthLipschitzThreshold_pos
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hfloor : quarticSignedPoleStrengthFloor <= W.targetStrength) :
    0 < W.postSixthTerminalFourthLipschitzThreshold := by
  have hhead : 0 < W.postSixthTerminalDominantHeadroom :=
    W.postSixthTerminalDominantHeadroom_pos hfloor
  have hc :
      0 < (3/1700 : ℝ) * quarticSignedPoleCanonicalLocalRadius^2 := by
    unfold quarticSignedPoleCanonicalLocalRadius
    positivity
  unfold QuarticFourSignedPolePair.postSixthTerminalFourthLipschitzThreshold
  exact div_pos hhead hc

/-- Exact positive-cap no-go certificate at the selected-witness level.  A
witness at or above the explicit ceiling cannot satisfy the present leading A2
cap; progress would then require a sharper signed eighth-order treatment rather
than more transport or asymptotic bookkeeping. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingAllowance_not_lt_target_of_threshold_le_fourthLipschitz
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hK :
      W.postSixthTerminalFourthLipschitzThreshold <= W.fourthLipschitz) :
    ¬ W.postSixthTerminalLeadingAllowance < W.targetStrength := by
  intro h
  have hlt :=
    (W.postSixthTerminalLeadingAllowance_lt_target_iff_fourthLipschitz).1 h
  linarith

end Synthesis