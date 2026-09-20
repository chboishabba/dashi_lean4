import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

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
A uniform coercive moment bound gives tightness of the actual finite-volume
probability measures.

The only Yang--Mills-specific input is the coercive observable `cost`: its
sublevel sets must be compact, and its `lintegral` must be bounded uniformly
over the cutoff family.  Tightness then follows from Markov's inequality.

The explicit threshold hypothesis isolates only elementary ENNReal arithmetic;
in concrete applications it is discharged by choosing a sufficiently large
finite radius.
-/
theorem isTightMeasureSet_of_uniform_coercive_lintegral_bound
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
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
        ∃ R : ENNReal, R ≠ 0 ∧ R ≠ ⊤ ∧ M / R ≤ ε) :
    IsTightMeasureSet
      {m : Measure Ω | ∃ p ∈ Set.range μ, (p : Measure Ω) = m} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases hthreshold ε hε with ⟨R, hR0, hRtop, hMR⟩
  let K : Set Ω := {x : Ω | cost x ≤ R}
  refine ⟨K, hcompact R hRtop, ?_⟩
  intro ν hν
  rcases hν with ⟨p, ⟨n, rfl⟩, rfl⟩
  have hsubset : Kᶜ ⊆ {x : Ω | R ≤ cost x} := by
    intro x hx
    have hx' : ¬ cost x ≤ R := by
      simpa [K] using hx
    exact (lt_of_not_ge hx').le
  calc
    ((μ n : ProbabilityMeasure Ω) : Measure Ω) Kᶜ
        ≤ ((μ n : ProbabilityMeasure Ω) : Measure Ω) {x : Ω | R ≤ cost x} :=
      measure_mono hsubset
    _ ≤ (∫⁻ x : Ω, cost x ∂((μ n : ProbabilityMeasure Ω) : Measure Ω)) / R :=
      meas_ge_le_lintegral_div hcost.aemeasurable hR0 hRtop
    _ ≤ M / R :=
      ENNReal.div_le_div_right (hmoment n) R
    _ ≤ ε := hMR

/--
Coercivity + a uniform moment bound already produce a continuum measure
subsequence and convergence of every bounded continuous expectation.

This is the A2 -> A3 continuum producer used by the literal YM lane.
-/
theorem exists_continuum_measure_of_uniform_coercive_lintegral_bound
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
        ∃ R : ENNReal, R ≠ 0 ∧ R ≠ ⊤ ∧ M / R ≤ ε) :
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
  apply exists_subsequence_with_all_boundedContinuous_expectations μ
  exact isTightMeasureSet_of_uniform_coercive_lintegral_bound
    μ cost hcost M hmoment hcompact hthreshold


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


/--
Every continuous finite-dimensional projection of the extracted continuum
measure is the weak limit of the corresponding projected finite measures.

This is the cylinder-law bridge used to attach Schwinger / finite-dimensional
distributions to the SAME continuum measure.
-/
theorem tendsto_continuous_marginals_of_weak_limit
    {Ω E : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    [MeasurableSpace E]
    [TopologicalSpace E]
    [BorelSpace E]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hconv : Tendsto μs atTop (𝓝 μ∞))
    {projection : Ω → E}
    (hprojection : Continuous projection) :
    Tendsto
      (fun n => (μs n).map projection)
      atTop
      (𝓝 (μ∞.map projection)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    μs μ∞ hconv hprojection

/--
An exact continuous symmetry of every finite measure survives in the SAME weak
limit measure.

This is the generic Euclidean/gauge-symmetry closure step for the A lane.
-/
theorem invariant_under_continuous_map_of_weak_limit
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    [BorelSpace Ω]
    [T2Space (ProbabilityMeasure Ω)]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hconv : Tendsto μs atTop (𝓝 μ∞))
    {symmetry : Ω → Ω}
    (hsymmetry : Continuous symmetry)
    (hinvariant : ∀ n : ℕ, (μs n).map symmetry = μs n) :
    μ∞.map symmetry = μ∞ := by
  have hmap :
      Tendsto
        (fun n => (μs n).map symmetry)
        atTop
        (𝓝 (μ∞.map symmetry)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      μs μ∞ hconv hsymmetry
  have hsame :
      (fun n => (μs n).map symmetry) = μs := by
    funext n
    exact hinvariant n
  rw [hsame] at hmap
  exact tendsto_nhds_unique hmap hconv

end RequestProject.YangMills
