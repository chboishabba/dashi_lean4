import Mathlib
import YangMills.CMP119PolymerReflectionAudit

namespace RequestProject.YangMills

example : cmp119ClassifyPolymerSupport false false = CMP119PolymerPlacement.empty := by
  rfl

example : cmp119ClassifyPolymerSupport true false = CMP119PolymerPlacement.positive := by
  rfl

example : cmp119ClassifyPolymerSupport false true = CMP119PolymerPlacement.negative := by
  rfl

example : cmp119ClassifyPolymerSupport true true = CMP119PolymerPlacement.crossing := by
  rfl

example
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ)
    (test : ι → ℝ)
    (hneg : indexedReflectionQuadratic K test < 0) :
    ¬ (∀ f : ι → ℝ, 0 ≤ indexedReflectionQuadratic K f) :=
  cmp119_crossing_kernel_falsified_by_negative_quadratic K test hneg

end RequestProject.YangMills
