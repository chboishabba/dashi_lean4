import Synthesis.RiemannG21ContinuumMomentSymmetrization

/-! RED-first regression contract for exact continuum moment symmetrization. -/

open MeasureTheory Set

namespace Synthesis

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A P q : α → ℝ}
    (hA : Integrable A μ) (hP : Integrable P μ)
    (hqA : Integrable (fun x => q x * A x) μ)
    (hqP : Integrable (fun x => q x * P x) μ) :
    (∫ z, symmetrizedMomentIntegrand A P q z ∂(μ.prod μ)) =
      2 * (moment0 A μ * momentQ q P μ - momentQ q A μ * moment0 P μ) := by
  exact integral_symmetrizedMomentIntegrand hA hP hqA hqP

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A P q : α → ℝ} {s : Set (α × α)}
    (hA : Integrable A μ) (hP : Integrable P μ)
    (hqA : Integrable (fun x => q x * A x) μ)
    (hqP : Integrable (fun x => q x * P x) μ)
    (hFnonneg : ∀ z, 0 <= symmetrizedMomentIntegrand A P q z)
    (hs : 0 < (μ.prod μ) s)
    (hFpos : ∀ z ∈ s, 0 < symmetrizedMomentIntegrand A P q z) :
    0 < moment0 A μ * momentQ q P μ - momentQ q A μ * moment0 P μ := by
  exact strictMomentCrossProduct_of_symmetrizedCarrier hA hP hqA hqP hFnonneg hs hFpos

end Synthesis
