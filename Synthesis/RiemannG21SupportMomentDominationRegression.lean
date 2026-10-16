import Synthesis.RiemannG21SupportMomentDomination

/-! RED-first regression contract for compact-support moment domination. -/

open Set
open intervalIntegral

namespace Synthesis

example {base : ℝ → ℝ} {R : ℝ}
    (hR : 0 <= R)
    (hbase : ∀ u ∈ Icc (0 : ℝ) R, 0 <= base u)
    (h0 : IntervalIntegrable base volume 0 R)
    (h2 : IntervalIntegrable (fun u => u^2 * base u) volume 0 R) :
    supportMoment2 base R <= R^2 * supportMoment0 base R := by
  exact supportMoment2_le_sq_mul hR hbase h0 h2

example {base : ℝ → ℝ} {R : ℝ}
    (hR : 0 <= R)
    (hbase : ∀ u ∈ Icc (0 : ℝ) R, 0 <= base u)
    (h0 : IntervalIntegrable base volume 0 R)
    (h4 : IntervalIntegrable (fun u => u^4 * base u) volume 0 R) :
    supportMoment4 base R <= R^4 * supportMoment0 base R := by
  exact supportMoment4_le_fourth_mul hR hbase h0 h4

end Synthesis
