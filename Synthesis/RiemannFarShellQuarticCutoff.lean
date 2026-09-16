import Mathlib

/-!
# Quartic cutoff atoms for the RH far shell

The retained checked far-shell formula in DASHI has shape

    18 * A * log (t + 4) / J + 72 * A / sqrt J.

For the high-ordinate schedule `J = t^4`, the source below proves the elementary
real-analysis reduction

    farShellBound A t (t^4) ≤ 144 * A / t^2

for `A ≥ 0` and `t ≥ 1`.

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

/-- The retained far-shell formula is `O(t⁻²)` under the quartic cutoff
`J(t)=t^4`, with an explicit coarse coefficient `144*A`. -/
theorem farShell_quartic_le_inverseSquare {A t : ℝ}
    (hA : 0 ≤ A) (ht : 1 ≤ t) :
    18 * A * Real.log (t + 4) / (t ^ 4) +
      72 * A / Real.sqrt (t ^ 4)
      ≤ 144 * A / (t ^ 2) := by
  have ht0 : 0 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have ht4pos : 0 < t ^ 4 := pow_pos htpos 4
  have ht2ne : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htpos)
  have htt2 : t ≤ t ^ 2 := by
    have hprod : 0 ≤ t * (t - 1) :=
      mul_nonneg ht0 (sub_nonneg.mpr ht)
    nlinarith
  have hlog2 : Real.log (t + 4) ≤ 4 * (t ^ 2) := by
    have hlog := log_add_four_le_four_mul ht
    nlinarith
  have hcoef : 0 ≤ 18 * A := by positivity
  have hnum :
      18 * A * Real.log (t + 4) ≤ 72 * A * (t ^ 2) := by
    calc
      18 * A * Real.log (t + 4)
          ≤ 18 * A * (4 * (t ^ 2)) :=
            mul_le_mul_of_nonneg_left hlog2 hcoef
      _ = 72 * A * (t ^ 2) := by ring
  have hterm1 :
      18 * A * Real.log (t + 4) / (t ^ 4)
        ≤ 72 * A / (t ^ 2) := by
    apply (div_le_iff₀ ht4pos).2
    calc
      18 * A * Real.log (t + 4)
          ≤ 72 * A * (t ^ 2) := hnum
      _ = (72 * A / (t ^ 2)) * (t ^ 4) := by
        field_simp [ht2ne]
        <;> ring
  calc
    18 * A * Real.log (t + 4) / (t ^ 4) +
        72 * A / Real.sqrt (t ^ 4)
        = 18 * A * Real.log (t + 4) / (t ^ 4) +
            72 * A / (t ^ 2) := by rw [sqrt_pow_four ht0]
    _ ≤ 72 * A / (t ^ 2) + 72 * A / (t ^ 2) :=
      add_le_add_right hterm1 _
    _ = 144 * A / (t ^ 2) := by ring

end Synthesis
