import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
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

end RequestProject.YangMills
