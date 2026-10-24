import Synthesis.RiemannG21ContinuumMomentStrictness

/-! RED-first regression contract for the continuum strictness/falsification layer. -/

open MeasureTheory Set

namespace Synthesis

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {s : Set α}
    (hf : Integrable f μ)
    (hnonneg : ∀ x, 0 <= f x)
    (hs : 0 < μ s)
    (hpos : ∀ x ∈ s, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  exact integral_pos_of_nonneg_of_pos_on_posMeasure hf hnonneg hs hpos

example (ka kp q : ℝ) :
    ka * (q * kp) - (q * ka) * kp = 0 := by
  exact oneAtomMomentDeterminant_zero ka kp q

example :
    ((0:ℝ) * (-2) - (-1) * (-1)) < 0 := by
  exact signedTwoPointWeight_canFlipMomentOrientation

end Synthesis
