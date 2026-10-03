import Mathlib
import YangMills.ProjectiveMarginalTightness

/-!
# D3.2 marginal moment / compact-sublevel tightness compiler

For each selected finite-dimensional marginal, a measurable coercive observable
with compact sublevel sets and a cutoff-uniform expectation bound gives genuine
tightness by the existing Prokhorov/Markov compiler.  This is the analytic
interface through which CMP109/116/119 moment or tail estimates can enter D3.

No source estimate is manufactured here.  Each marginal carries its own cost,
uniform moment bound, compact-sublevel theorem, and threshold arithmetic.
-/

open Filter Set MeasureTheory

namespace RequestProject.YangMills

structure RealMarginalMomentTightnessProducer where
  marginal : (m : ℕ) → ℕ → ProbabilityMeasure (Fin m → ℝ)
  cost : (m : ℕ) → (Fin m → ℝ) → ENNReal
  costMeasurable : ∀ m, Measurable (cost m)
  momentBound : ℕ → ENNReal
  uniformMoment :
    ∀ (m k : ℕ),
      (∫⁻ x : Fin m → ℝ, cost m x
        ∂((marginal m k : ProbabilityMeasure (Fin m → ℝ)) :
          Measure (Fin m → ℝ))) ≤ momentBound m
  compactSublevel :
    ∀ (m : ℕ) (R : ENNReal), R ≠ ⊤ →
      IsCompact {x : Fin m → ℝ | cost m x ≤ R}
  threshold :
    ∀ (m : ℕ) (ε : ENNReal), 0 < ε →
      ∃ R : ENNReal,
        R ≠ 0 ∧ R ≠ ⊤ ∧ momentBound m / R ≤ ε

namespace RealMarginalMomentTightnessProducer

/-- Every marginal family is tight by the actual uniform moment estimate. -/
theorem marginal_tight
    (producer : RealMarginalMomentTightnessProducer)
    (m : ℕ) :
    IsTightMeasureSet
      {ν : Measure (Fin m → ℝ) |
        ∃ p ∈ Set.range (producer.marginal m),
          ((p : ProbabilityMeasure (Fin m → ℝ)) :
            Measure (Fin m → ℝ)) = ν} := by
  exact isTightMeasureSet_of_uniform_coercive_lintegral_bound
    (producer.marginal m)
    (producer.cost m)
    (producer.costMeasurable m)
    (producer.momentBound m)
    (producer.uniformMoment m)
    (producer.compactSublevel m)
    (producer.threshold m)

/-- Package all marginal moment estimates as the D3 tightness producer. -/
def toTightnessProducer
    (producer : RealMarginalMomentTightnessProducer) :
    RealProjectiveMarginalTightnessProducer where
  marginal := producer.marginal
  tight := producer.marginal_tight

/-- Every fixed marginal therefore admits an actual Prokhorov subsequence. -/
theorem exists_each_marginal_weak_subsequence
    (producer : RealMarginalMomentTightnessProducer) :
    ∀ m : ℕ,
      ∃ μ∞ : ProbabilityMeasure (Fin m → ℝ),
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto (producer.marginal m ∘ φ)
            atTop (𝓝 μ∞) :=
  exists_each_real_finite_marginal_weak_subsequence
    producer.toTightnessProducer

end RealMarginalMomentTightnessProducer

end RequestProject.YangMills
