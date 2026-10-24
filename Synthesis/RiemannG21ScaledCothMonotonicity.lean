import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Synthesis.RiemannImprovedZeroFreeG21UniformGap

/-!
# G21 positive-axis `x coth x` monotonicity

The live Agda G21 programme isolated the odd/sinh TP2 gate to the elementary
real-analysis statement that

`x ↦ x * coth x`

is strictly increasing for `x > 0`.  Mathlib v4.28.0 already owns the required
hyperbolic identities and mean-value theorem, but the composed theorem was not
previously source-written in DASHI.

To avoid depending on a separate `coth` API, the carrier is written literally
as `x * cosh x / sinh x`.  Its derivative is

`(sinh x * cosh x - x) / sinh x^2`,

whose numerator is positive because `sinh(2x) > 2x` for `x>0` and
`sinh(2x)=2 sinh x cosh x`.

This closes the scalar calculus leaf only.  Transport into the Agda G21 action,
the continuum odd-moment double integral, finite-radius Taylor control and the
actual parity minor remain separate same-object obligations.
-/

noncomputable section

open Set

namespace Synthesis

/-- Literal positive-axis `x coth x` carrier used by G21. -/
def scaledCothCarrier (x : ℝ) : ℝ :=
  x * Real.cosh x / Real.sinh x

/-- Atomic positivity behind the derivative of `x coth x`. -/
theorem sinh_mul_cosh_gt_self {x : ℝ} (hx : 0 < x) :
    x < Real.sinh x * Real.cosh x := by
  have h2x : (2 : ℝ) * x < Real.sinh ((2 : ℝ) * x) := by
    rw [Real.self_lt_sinh_iff]
    linarith
  rw [Real.sinh_two_mul] at h2x
  linarith

/-- Exact derivative of the literal carrier on the positive axis. -/
theorem hasDerivAt_scaledCothCarrier {x : ℝ} (hx : 0 < x) :
    HasDerivAt scaledCothCarrier
      ((Real.sinh x * Real.cosh x - x) / Real.sinh x ^ 2) x := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_ne_zero).2 hx.ne'
  have hraw :=
    ((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x)).div
      (Real.hasDerivAt_sinh x) hsinh
  unfold scaledCothCarrier
  convert hraw using 1
  · field_simp [hsinh]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The derivative is strictly positive at every positive point. -/
theorem deriv_scaledCothCarrier_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv scaledCothCarrier x := by
  rw [(hasDerivAt_scaledCothCarrier hx).deriv]
  have hnum : 0 < Real.sinh x * Real.cosh x - x := sub_pos.mpr (sinh_mul_cosh_gt_self hx)
  have hsinh : 0 < Real.sinh x := (Real.sinh_pos_iff).2 hx
  exact div_pos hnum (sq_pos_of_pos hsinh)

/-- `x ↦ x coth x` is strictly increasing on `(0,∞)`. -/
theorem scaledCothCarrier_strictMonoOn :
    StrictMonoOn scaledCothCarrier (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_scaledCothCarrier hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    exact deriv_scaledCothCarrier_pos hx

/-- Direct two-point form consumed by G21's scaled log-derivative bridge. -/
theorem scaledCothCarrier_lt
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    scaledCothCarrier x < scaledCothCarrier y := by
  exact scaledCothCarrier_strictMonoOn hx (hx.trans hxy) hxy

end Synthesis
