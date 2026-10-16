import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Synthesis.RiemannG21ScaledCothMonotonicity

/-!
# G21 positive-axis `x tanh x` monotonicity

Companion to the odd/sinh `x coth x` leaf.  We use the literal carrier
`x * sinh x / cosh x`; on the positive axis its derivative is

`(sinh x * cosh x + x) / cosh x^2 > 0`.

This is elementary real calculus.  Its role is to remove the even/cosh scalar
log-derivative leaf from the genuine G21 analytic frontier; continuum moment
and finite-radius determinant transport remain separate.
-/

noncomputable section

open Set

namespace Synthesis

/-- Literal `x tanh x` carrier. -/
def scaledTanhCarrier (x : ℝ) : ℝ :=
  x * Real.sinh x / Real.cosh x

/-- Exact derivative on the positive axis. -/
theorem hasDerivAt_scaledTanhCarrier {x : ℝ} (hx : 0 < x) :
    HasDerivAt scaledTanhCarrier
      ((Real.sinh x * Real.cosh x + x) / Real.cosh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hraw :=
    ((hasDerivAt_id' x).mul (Real.hasDerivAt_sinh x)).div
      (Real.hasDerivAt_cosh x) hcosh
  unfold scaledTanhCarrier
  convert hraw using 1
  · field_simp [hcosh]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- Derivative positivity. -/
theorem deriv_scaledTanhCarrier_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv scaledTanhCarrier x := by
  rw [(hasDerivAt_scaledTanhCarrier hx).deriv]
  have hsinh : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  exact div_pos (by positivity) (sq_pos_of_pos hcosh)

/-- `x ↦ x tanh x` is strictly increasing on `(0,∞)`. -/
theorem scaledTanhCarrier_strictMonoOn :
    StrictMonoOn scaledTanhCarrier (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_scaledTanhCarrier hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    exact deriv_scaledTanhCarrier_pos hx

end Synthesis
