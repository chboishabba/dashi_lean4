import Mathlib
import Synthesis.RiemannFarShellQuarticCutoff

/-!
# Horizontal-displacement-adaptive far-shell scaling

The fixed quartic schedule J=t^4 gives O(t^-2), but the actual pole-quotient
cluster surplus vanishes quadratically with horizontal displacement

    a = Re rho - 1/2.

For a uniform arbitrary off-line-zero theorem, a fixed O(t^-2) far error is
therefore too coarse as a -> 0.  The natural schedule is quartic in t/|a|.

This file proves the real-analysis atom behind that adaptive schedule.  It is
domain-neutral and does not yet identify the natural cutoff with the literal
near/far carrier.
-/

namespace Synthesis

/-- Under 0 < alpha <= 1 and t >= 1, the scaled ordinate x=t/alpha is at least
one. -/
theorem one_le_div_of_unit_displacement {t alpha : ℝ}
    (ht : 1 ≤ t) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    1 ≤ t / alpha := by
  rw [le_div_iff₀ ha0]
  exact le_trans ha1 ht

/-- Replacing t by t/alpha in the quartic schedule gives precisely the desired
alpha^2/t^2 scale.  The logarithm in the original far shell only decreases,
because t <= t/alpha for alpha <= 1. -/
theorem farShell_scaledQuartic_le_displacementInverseSquare
    {A t alpha : ℝ}
    (hA : 0 ≤ A) (ht : 1 ≤ t) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    18 * A * Real.log (t + 4) / ((t / alpha) ^ 4) +
      72 * A / Real.sqrt ((t / alpha) ^ 4)
      ≤ 144 * A * alpha ^ 2 / (t ^ 2) := by
  have hx : 1 ≤ t / alpha :=
    one_le_div_of_unit_displacement ht ha0 ha1
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hxpos : 0 < t / alpha := by positivity
  have htx : t ≤ t / alpha := by
    rw [le_div_iff₀ ha0]
    nlinarith
  have hlogarg : t + 4 ≤ t / alpha + 4 := by linarith
  have hlog :
      Real.log (t + 4) ≤ Real.log (t / alpha + 4) := by
    exact Real.log_le_log (by linarith) hlogarg
  have hden : 0 < (t / alpha) ^ 4 := pow_pos hxpos 4
  have hcoef : 0 ≤ 18 * A := by positivity
  have hfirst :
      18 * A * Real.log (t + 4) / ((t / alpha) ^ 4)
        ≤ 18 * A * Real.log (t / alpha + 4) / ((t / alpha) ^ 4) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hcoef) hden.le
  have hquartic :=
    farShell_quartic_le_inverseSquare
      (A := A) (t := t / alpha) hA hx
  have hrhs :
      144 * A / ((t / alpha) ^ 2)
        = 144 * A * alpha ^ 2 / (t ^ 2) := by
    field_simp [ne_of_gt htpos, ne_of_gt ha0]
    <;> ring
  calc
    18 * A * Real.log (t + 4) / ((t / alpha) ^ 4) +
        72 * A / Real.sqrt ((t / alpha) ^ 4)
        ≤ 18 * A * Real.log (t / alpha + 4) / ((t / alpha) ^ 4) +
            72 * A / Real.sqrt ((t / alpha) ^ 4) := by
              exact add_le_add_right hfirst _
    _ ≤ 144 * A / ((t / alpha) ^ 2) := hquartic
    _ = 144 * A * alpha ^ 2 / (t ^ 2) := hrhs

end Synthesis
