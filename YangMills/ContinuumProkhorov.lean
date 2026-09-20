import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.Sequences

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/--
Prokhorov extraction for the continuum Yang--Mills lane.

This theorem deliberately consumes a genuine tightness theorem for the actual
finite-volume probability measures.  It returns a subsequence converging in the
native weak topology on `ProbabilityMeasure Ω`; no surrogate measure carrier is
introduced.
-/
theorem exists_weakly_convergent_subsequence_of_tight
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [T2Space Ω]
    [BorelSpace Ω]
    [FirstCountableTopology (ProbabilityMeasure Ω)]
    (μ : ℕ → ProbabilityMeasure Ω)
    (hTight :
      IsTightMeasureSet
        {m : Measure Ω | ∃ p ∈ Set.range μ, (p : Measure Ω) = m}) :
    ∃ μ∞ : ProbabilityMeasure Ω,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Tendsto (μ ∘ φ) atTop (𝓝 μ∞) := by
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet hTight
  have hmem : ∀ n : ℕ, μ n ∈ closure (Set.range μ) := by
    intro n
    exact subset_closure (Set.mem_range_self n)
  rcases hcompact.tendsto_subseq hmem with
    ⟨μ∞, _hμ∞, φ, hφ, hconv⟩
  exact ⟨μ∞, φ, hφ, hconv⟩

/--
The extracted continuum measure automatically realizes the subsequential limits
of every bounded continuous observable.

This is the measure-level A3 bridge needed by the pinned Yang--Mills continuum
producer: once tightness is paid, weak convergence and the corresponding
expectation convergence are one theorem, not two independent physical inputs.
-/
theorem exists_subsequence_with_all_boundedContinuous_expectations
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [T2Space Ω]
    [BorelSpace Ω]
    [FirstCountableTopology (ProbabilityMeasure Ω)]
    (μ : ℕ → ProbabilityMeasure Ω)
    (hTight :
      IsTightMeasureSet
        {m : Measure Ω | ∃ p ∈ Set.range μ, (p : Measure Ω) = m}) :
    ∃ μ∞ : ProbabilityMeasure Ω,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Tendsto (μ ∘ φ) atTop (𝓝 μ∞) ∧
        ∀ f : BoundedContinuousFunction Ω ℝ,
          Tendsto
            (fun n =>
              ∫ x : Ω, f x ∂((μ (φ n) : ProbabilityMeasure Ω) : Measure Ω))
            atTop
            (𝓝 (∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω))) := by
  rcases exists_weakly_convergent_subsequence_of_tight μ hTight with
    ⟨μ∞, φ, hφ, hconv⟩
  refine ⟨μ∞, φ, hφ, hconv, ?_⟩
  have hExpect :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hconv
  intro f
  simpa [Function.comp_def] using hExpect f


/--
Bounded continuous expectations determine the continuum probability measure.

This removes a separate "same-limit measure" assumption once the candidate
continuum measure and the complete bounded-continuous expectation functional
have been identified.
-/
theorem probabilityMeasure_ext_of_all_boundedContinuous_integrals_eq
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [HasOuterApproxClosed Ω]
    [BorelSpace Ω]
    (μ ν : ProbabilityMeasure Ω)
    (h :
      ∀ f : BoundedContinuousFunction Ω ℝ,
        (∫ x : Ω, f x ∂((μ : ProbabilityMeasure Ω) : Measure Ω)) =
        (∫ x : Ω, f x ∂((ν : ProbabilityMeasure Ω) : Measure Ω))) :
    μ = ν := by
  apply Subtype.ext
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure h

/--
Closed positivity inequalities survive weak convergence.

For OS reconstruction this is the generic analytic step: once a reflection
quadratic form has been represented by a bounded continuous observable and is
nonnegative at every finite cutoff, its expectation is nonnegative in the same
weak limit measure.
-/
theorem nonnegative_boundedContinuous_expectation_of_weak_limit
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hconv : Tendsto μs atTop (𝓝 μ∞))
    (f : BoundedContinuousFunction Ω ℝ)
    (hfinite :
      ∀ n : ℕ,
        0 ≤ ∫ x : Ω, f x ∂((μs n : ProbabilityMeasure Ω) : Measure Ω)) :
    0 ≤ ∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω) := by
  have hExpect :
      Tendsto
        (fun n =>
          ∫ x : Ω, f x ∂((μs n : ProbabilityMeasure Ω) : Measure Ω))
        atTop
        (𝓝 (∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hconv f
  exact ge_of_tendsto hExpect (Filter.Eventually.of_forall hfinite)

end RequestProject.YangMills
