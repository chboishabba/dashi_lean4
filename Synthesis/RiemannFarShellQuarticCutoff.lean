import Mathlib

/-!
# Quartic cutoff atoms for the RH far shell

The retained checked far-shell formula in DASHI has shape

    18 * A * log (t + 4) / J + 72 * A / sqrt J.

For the high-ordinate schedule `J = t^4`, two elementary real-analysis facts
remove the transcendental/square-root part of the asymptotic bookkeeping:

* for `t ≥ 1`, `log (t + 4) ≤ 4 t`;
* for `t ≥ 0`, `sqrt (t^4) = t^2`.

These lemmas are domain-neutral.  They do not identify a concrete RH cutoff,
taper, far-shell owner, cluster response, or off-line zero.  They are intended
as small donors for a later same-object R2 envelope producer.
-/

namespace Synthesis

/-- A deliberately coarse bound sufficient for quartic-cutoff asymptotics. -/
theorem log_add_four_le_four_mul {t : ℝ} (ht : 1 ≤ t) :
    Real.log (t + 4) ≤ 4 * t := by
  have hpos : 0 < t + 4 := by linarith
  have hlog : Real.log (t + 4) ≤ (t + 4) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  linarith

/-- The square-root term in a quartic cutoff is exactly quadratic at nonnegative
ordinate. -/
theorem sqrt_pow_four {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (t ^ 4) = t ^ 2 := by
  rw [show t ^ 4 = (t ^ 2) ^ 2 by ring]
  exact Real.sqrt_sq (sq_nonneg t)

end Synthesis
