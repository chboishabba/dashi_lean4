import Mathlib
import YangMills.ContinuumProkhorov
import YangMills.ContinuumWilsonCovariance

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/--
Native mathlib-backed A3/P2 package.

A Yang--Mills-specific coercive moment estimate plus limits of all bounded
continuous expectations produce the unique full continuum probability measure.
For any selected bounded continuous Wilson pair, a cutoff-uniform finite
covariance estimate then passes to that same continuum measure.

The theorem deliberately does not manufacture the physical inputs:
`cost`, compact sublevels, the uniform moment bound, scalar expectation
limits, and the finite clustering estimate remain hypotheses.
-/
theorem exists_unique_continuum_measure_with_selected_covariance_bound
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [T2Space Ω]
    [BorelSpace Ω]
    [FirstCountableTopology (ProbabilityMeasure Ω)]
    (μ : ℕ → ProbabilityMeasure Ω)
    (cost : Ω → ENNReal)
    (hcost : Measurable cost)
    (M : ENNReal)
    (hmoment :
      ∀ n : ℕ,
        (∫⁻ x : Ω, cost x ∂((μ n : ProbabilityMeasure Ω) : Measure Ω)) ≤ M)
    (hcompact :
      ∀ R : ENNReal, R ≠ ⊤ → IsCompact {x : Ω | cost x ≤ R})
    (hthreshold :
      ∀ ε : ENNReal, 0 < ε →
        ∃ R : ENNReal, R ≠ 0 ∧ R ≠ ⊤ ∧ M / R ≤ ε)
    (L : BoundedContinuousFunction Ω ℝ → ℝ)
    (hScalar :
      ∀ f : BoundedContinuousFunction Ω ℝ,
        Tendsto
          (fun n =>
            ∫ x : Ω, f x ∂((μ n : ProbabilityMeasure Ω) : Measure Ω))
          atTop
          (𝓝 (L f)))
    (left right : BoundedContinuousFunction Ω ℝ)
    (bound : ℝ)
    (hFinite :
      ∀ n, |probabilityCovariance (μ n) left right| ≤ bound) :
    ∃! μ∞ : ProbabilityMeasure Ω,
      Tendsto μ atTop (𝓝 μ∞) ∧
      (∀ f : BoundedContinuousFunction Ω ℝ,
        (∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω)) = L f) ∧
      |probabilityCovariance μ∞ left right| ≤ bound := by
  rcases
      tendsto_unique_continuum_measure_of_coercive_moment_and_bcf_limits
        μ cost hcost M hmoment hcompact hthreshold L hScalar with
    ⟨μ∞, ⟨hconv, hidentify⟩, hunique⟩
  have hcov :
      |probabilityCovariance μ∞ left right| ≤ bound :=
    probabilityCovariance_abs_le_of_weak_limit
      hconv left right bound hFinite
  refine ⟨μ∞, ⟨hconv, hidentify, hcov⟩, ?_⟩
  intro ν hν
  exact hunique ν ⟨hν.1, hν.2.1⟩

/--
Exponential-clustering specialization of the combined A3/P2 package.
-/
theorem exists_unique_continuum_measure_with_selected_exponential_clustering
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [T2Space Ω]
    [BorelSpace Ω]
    [FirstCountableTopology (ProbabilityMeasure Ω)]
    (μ : ℕ → ProbabilityMeasure Ω)
    (cost : Ω → ENNReal)
    (hcost : Measurable cost)
    (M : ENNReal)
    (hmoment :
      ∀ n : ℕ,
        (∫⁻ x : Ω, cost x ∂((μ n : ProbabilityMeasure Ω) : Measure Ω)) ≤ M)
    (hcompact :
      ∀ R : ENNReal, R ≠ ⊤ → IsCompact {x : Ω | cost x ≤ R})
    (hthreshold :
      ∀ ε : ENNReal, 0 < ε →
        ∃ R : ENNReal, R ≠ 0 ∧ R ≠ ⊤ ∧ M / R ≤ ε)
    (L : BoundedContinuousFunction Ω ℝ → ℝ)
    (hScalar :
      ∀ f : BoundedContinuousFunction Ω ℝ,
        Tendsto
          (fun n =>
            ∫ x : Ω, f x ∂((μ n : ProbabilityMeasure Ω) : Measure Ω))
          atTop
          (𝓝 (L f)))
    (left right : BoundedContinuousFunction Ω ℝ)
    (C m t : ℝ)
    (hFinite :
      ∀ n,
        |probabilityCovariance (μ n) left right| ≤
          C * Real.exp (-m * t)) :
    ∃! μ∞ : ProbabilityMeasure Ω,
      Tendsto μ atTop (𝓝 μ∞) ∧
      (∀ f : BoundedContinuousFunction Ω ℝ,
        (∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω)) = L f) ∧
      |probabilityCovariance μ∞ left right| ≤
        C * Real.exp (-m * t) := by
  exact
    exists_unique_continuum_measure_with_selected_covariance_bound
      μ cost hcost M hmoment hcompact hthreshold L hScalar
      left right (C * Real.exp (-m * t)) hFinite

end RequestProject.YangMills
