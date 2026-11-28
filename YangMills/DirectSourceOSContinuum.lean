import Mathlib
import YangMills.ContinuumProkhorov
import YangMills.ContinuumWilsonCovariance
import YangMills.OSGramNullSpace
import YangMills.PreGapOSSemigroup

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

/--
H2 finite-to-continuum core with OS2 on the VERY SAME probability measure.

The positive-time reflected product is a bounded continuous cylinder
observable for every pair in each finite test family.  The physical finite
reflection-positive inequality transfers to the UNIQUE continuum
probability-measure limit obtained from the uniform coercive bound and all
bounded-continuous expectation limits.

This is a source-facing implication, not a standalone construction of
4-dimensional YM: CMP119 must still furnish the gauge-invariant
configuration-space topology, selected Gibbs measures, moment bound,
cutoff-wise reflection positivity and expectation convergence.
-/
theorem exists_unique_continuum_measure_with_real_os2_gram
    {Ω Test : Type*}
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
    (reflectedProduct :
      ∀ {n : ℕ}, (Fin n → Test) →
        Fin n → Fin n → BoundedContinuousFunction Ω ℝ)
    (hFiniteOS2 :
      ∀ (n : ℕ) (tests : Fin n → Test)
        (coeff : Fin n → ℝ) (cutoff : ℕ),
        0 ≤
          ∫ x : Ω,
            (∑ i : Fin n, ∑ j : Fin n,
              (coeff i * coeff j) • reflectedProduct tests i j) x
            ∂((μ cutoff : ProbabilityMeasure Ω) : Measure Ω)) :
    ∃! μ∞ : ProbabilityMeasure Ω,
      Tendsto μ atTop (𝓝 μ∞) ∧
      (∀ f : BoundedContinuousFunction Ω ℝ,
        (∫ x : Ω, f x ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω)) = L f) ∧
      (∀ (n : ℕ) (tests : Fin n → Test) (coeff : Fin n → ℝ),
        0 ≤
          ∫ x : Ω,
            (∑ i : Fin n, ∑ j : Fin n,
              (coeff i * coeff j) • reflectedProduct tests i j) x
            ∂((μ∞ : ProbabilityMeasure Ω) : Measure Ω)) := by
  rcases
      tendsto_unique_continuum_measure_of_coercive_moment_and_bcf_limits
        μ cost hcost M hmoment hcompact hthreshold L hScalar with
    ⟨μ∞, ⟨hconv, hidentify⟩, hunique⟩
  have hGram :=
    reflected_gram_positive_all_test_families_of_weak_limit
      hconv reflectedProduct hFiniteOS2
  refine ⟨μ∞, ⟨hconv, hidentify, hGram⟩, ?_⟩
  intro ν hν
  exact hunique ν ⟨hν.1, hν.2.1⟩

/--
C2: a literal nonnegative dyadic OPE tail makes the actual finite-depth
truncations converge to the SAME physical product coefficient.  The
physics is the identification of the CMP119 marked-composite remainder
with this actual local product; the rate-to-limit implication is analytic.
-/
theorem physical_ope_truncations_converge_of_dyadic_tail
    (product : ℝ) (truncation : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hRemainder :
      ∀ depth : ℕ,
        |product - truncation depth| ≤ C * (1 / 2 : ℝ) ^ depth) :
    Tendsto truncation atTop (𝓝 product) := by
  have hGeometric :
      Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hGeometric ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hbound := hRemainder n
  have hsmall : C * (1 / 2 : ℝ) ^ n < ε := by
    have hnsmall := hN n hn
    have hpositive : 0 ≤ C * (1 / 2 : ℝ) ^ n := by positivity
    simpa [Real.dist_eq, abs_of_nonneg hpositive] using hnsmall
  have hfinal : |truncation n - product| < ε := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hbound hsmall
  simpa [Real.dist_eq] using hfinal

end RequestProject.YangMills
