import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleA2LeadingConstantCut

/-!
# A2 literal sixth/eighth debt cut

This file pushes the A2 audit one mechanically exact step past the normalized
leading-coefficient comparison.  The literal selected-sixth and G1-welded
eighth debts are each split into

* an exact expanded-zero-count / (t/16)^2 leading coordinate; and
* an explicit nonnegative inverse-power remainder.

No zero-count asymptotic, horizontal-curvature estimate, compensation sign, or
RH-equivalent premise is introduced.  The point is to expose exactly which
part of the literal positive debt survives at leading scale and which part is
strictly lower in powers of the high-ordinate scale once the same expanded
zero-count carrier is fixed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- Literal leading `NZ/(t/16)^2` coordinate of the selected-sixth debt. -/
def QuarticFourSignedPolePair.postSixthTerminalSixthLeadingDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (Real.pi^6 * eta^6 / 4800) * NZ / (t/16)^2

/-- Exact inverse-power remainder after removing the sixth debt's
`NZ/(t/16)^2` coordinate. -/
def QuarticFourSignedPolePair.postSixthTerminalSixthRemainderDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let s := t/16
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (Real.pi^6
      * (240 * eta^4 * s^4 + 60 * eta^2 * s^2 + 1)
      / (307200 * s^8)) * NZ

/-- The literal selected-sixth debt is exactly its leading count-scale
coordinate plus a lower inverse-power remainder. -/
theorem QuarticFourSignedPolePair.postSixthTerminalSixthDebt_eq_leading_add_remainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalSixthDebt
      = W.postSixthTerminalSixthLeadingDebt
        + W.postSixthTerminalSixthRemainderDebt := by
  unfold QuarticFourSignedPolePair.postSixthTerminalSixthDebt
    QuarticFourSignedPolePair.postSixthTerminalSixthLeadingDebt
    QuarticFourSignedPolePair.postSixthTerminalSixthRemainderDebt
    quarticSignedPoleLocalSixthPhaseEnvelope
    quarticSignedPoleLocalHalfWidth
  dsimp
  ring

/-- The sixth inverse-power remainder is nonnegative on the literal carrier. -/
theorem QuarticFourSignedPolePair.postSixthTerminalSixthRemainderDebt_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.postSixthTerminalSixthRemainderDebt := by
  unfold QuarticFourSignedPolePair.postSixthTerminalSixthRemainderDebt
    quarticSignedPoleLocalHalfWidth
  dsimp
  positivity

/-- Hence the exact sixth leading coordinate is a genuine lower bound on the
full positive sixth cap. -/
theorem QuarticFourSignedPolePair.postSixthTerminalSixthLeadingDebt_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalSixthLeadingDebt
      <= W.postSixthTerminalSixthDebt := by
  rw [W.postSixthTerminalSixthDebt_eq_leading_add_remainder]
  exact le_add_of_nonneg_right W.postSixthTerminalSixthRemainderDebt_nonneg

/-- Literal leading `NZ/(t/16)^2` coordinate of the G1-welded eighth debt. -/
def QuarticFourSignedPolePair.postSixthTerminalEighthLeadingDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (((Real.pi+1)^2 * W.fourthLipschitz) * eta^8 / 17000)
    * NZ / (t/16)^2

/-- Exact inverse-power remainder after removing the eighth debt's
`NZ/(t/16)^2` coordinate. -/
def QuarticFourSignedPolePair.postSixthTerminalEighthRemainderDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let s := t/16
  let NZ : ℝ := (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * (6400 * eta^6 * s^6
          + 1600 * eta^4 * s^4
          + 400 * eta^2 * s^2
          + 1)
      / (7680000 * s^10)) * NZ

/-- The literal eighth debt is exactly its leading count-scale coordinate plus
an explicit lower inverse-power remainder. -/
theorem QuarticFourSignedPolePair.postSixthTerminalEighthDebt_eq_leading_add_remainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalEighthDebt
      = W.postSixthTerminalEighthLeadingDebt
        + W.postSixthTerminalEighthRemainderDebt := by
  unfold QuarticFourSignedPolePair.postSixthTerminalEighthDebt
    QuarticFourSignedPolePair.postSixthTerminalEighthLeadingDebt
    QuarticFourSignedPolePair.postSixthTerminalEighthRemainderDebt
    quarticSignedPoleLocalEighthPhysicalEnvelope
    quarticSignedPoleLocalHalfWidth
  dsimp
  ring

/-- The G1 fourth-Lipschitz constant is nonnegative on every selected witness. -/
theorem QuarticFourSignedPolePair.fourthLipschitz_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.fourthLipschitz := by
  unfold QuarticFourSignedPolePair.fourthLipschitz
    compactCoshFourthLipschitzConstant
  positivity

/-- The eighth inverse-power remainder is nonnegative. -/
theorem QuarticFourSignedPolePair.postSixthTerminalEighthRemainderDebt_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.postSixthTerminalEighthRemainderDebt := by
  have hK := W.fourthLipschitz_nonneg
  unfold QuarticFourSignedPolePair.postSixthTerminalEighthRemainderDebt
    quarticSignedPoleLocalHalfWidth
  dsimp
  positivity

/-- Hence the exact eighth leading coordinate is a genuine lower bound on the
full positive eighth cap. -/
theorem QuarticFourSignedPolePair.postSixthTerminalEighthLeadingDebt_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalEighthLeadingDebt
      <= W.postSixthTerminalEighthDebt := by
  rw [W.postSixthTerminalEighthDebt_eq_leading_add_remainder]
  exact le_add_of_nonneg_right W.postSixthTerminalEighthRemainderDebt_nonneg

/-- The literal leading part of the combined sixth/eighth A2 debt. -/
def QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.postSixthTerminalSixthLeadingDebt
    + W.postSixthTerminalEighthLeadingDebt

/-- The exact lower inverse-power remainder of the combined sixth/eighth debt. -/
def QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.postSixthTerminalSixthRemainderDebt
    + W.postSixthTerminalEighthRemainderDebt

/-- Exact literal decomposition of the previously named leading-local debt.
This is the same physical count carrier; no asymptotic replacement is made. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLeadingLocalDebt_eq_literal_leading_add_remainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLeadingLocalDebt
      = W.postSixthTerminalLiteralLeadingDebt
        + W.postSixthTerminalLiteralLeadingRemainder := by
  unfold QuarticFourSignedPolePair.postSixthTerminalLeadingLocalDebt
    QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingDebt
    QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingRemainder
  rw [W.postSixthTerminalSixthDebt_eq_leading_add_remainder]
  rw [W.postSixthTerminalEighthDebt_eq_leading_add_remainder]
  ring

/-- The combined inverse-power remainder is nonnegative. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingRemainder_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.postSixthTerminalLiteralLeadingRemainder := by
  unfold QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingRemainder
  positivity

/-- Therefore any eventual A2 PASS must at least pay the exact literal
sixth-plus-eighth leading count-scale coordinate.  This is a necessary
condition, not a sufficient terminal theorem. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLiteralLeadingDebt_le_leadingLocalDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLiteralLeadingDebt
      <= W.postSixthTerminalLeadingLocalDebt := by
  rw [W.postSixthTerminalLeadingLocalDebt_eq_literal_leading_add_remainder]
  exact le_add_of_nonneg_right W.postSixthTerminalLiteralLeadingRemainder_nonneg

end Synthesis
