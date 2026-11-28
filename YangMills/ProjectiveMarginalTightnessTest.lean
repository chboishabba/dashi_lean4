import Mathlib
import YangMills.ProjectiveMarginalTightness

open Filter Set MeasureTheory

namespace RequestProject.YangMills

example
    (producer : RealProjectiveMarginalTightnessProducer) :
    ∀ m : ℕ,
      ∃ μ∞ : ProbabilityMeasure (Fin m → ℝ),
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto (producer.marginal m ∘ φ) atTop (𝓝 μ∞) :=
  exists_each_real_finite_marginal_weak_subsequence producer

example
    (limits : (m : ℕ) → ProbabilityMeasure (Fin m → ℝ)) : Prop :=
  RealProjectiveLimitExistenceObligation limits

end RequestProject.YangMills
