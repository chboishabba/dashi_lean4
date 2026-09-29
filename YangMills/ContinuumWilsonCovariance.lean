import Mathlib
import YangMills.ContinuumProkhorov
import YangMills.SelectedCovarianceLimit

open Filter MeasureTheory

namespace RequestProject.YangMills

/-- Connected covariance of two bounded continuous real observables. -/
def probabilityCovariance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (f g : BoundedContinuousFunction Ω ℝ) : ℝ :=
  (∫ x : Ω, (f * g) x ∂((μ : ProbabilityMeasure Ω) : Measure Ω))
    -
  (∫ x : Ω, f x ∂((μ : ProbabilityMeasure Ω) : Measure Ω)) *
  (∫ x : Ω, g x ∂((μ : ProbabilityMeasure Ω) : Measure Ω))

/--
Weak convergence of probability measures transports connected covariance for
bounded continuous observables.  This is the native measure-theoretic P2
statement for the direct Yang--Mills route.
-/
theorem tendsto_probabilityCovariance_of_weak_convergence
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ∞))
    (f g : BoundedContinuousFunction Ω ℝ) :
    Tendsto
      (fun n => probabilityCovariance (μs n) f g)
      atTop
      (𝓝 (probabilityCovariance μ∞ f g)) := by
  have hAll :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hμ
  have hLeft := hAll f
  have hRight := hAll g
  have hProduct := hAll (f * g)
  exact tendsto_scalarCovariance_of_three_expectations
    hLeft hRight hProduct

/--
A cutoff-independent covariance bound passes to the weak continuum limit.
-/
theorem probabilityCovariance_abs_le_of_weak_limit
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ∞))
    (f g : BoundedContinuousFunction Ω ℝ)
    (bound : ℝ)
    (hfinite : ∀ n, |probabilityCovariance (μs n) f g| ≤ bound) :
    |probabilityCovariance μ∞ f g| ≤ bound := by
  exact abs_le_of_tendsto_of_forall_abs_le
    (tendsto_probabilityCovariance_of_weak_convergence hμ f g)
    hfinite

/--
Fixed-time exponential-clustering transport.  The shape of the right-hand side
is deliberately abstracted as `C * exp (-m * t)`; no positivity assumptions
are needed for the closed-limit step itself.
-/
theorem probabilityCovariance_exponential_bound_of_weak_limit
    {Ω : Type*}
    [MeasurableSpace Ω]
    [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω}
    {μ∞ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ∞))
    (f g : BoundedContinuousFunction Ω ℝ)
    (C m t : ℝ)
    (hfinite :
      ∀ n,
        |probabilityCovariance (μs n) f g| ≤ C * Real.exp (-m * t)) :
    |probabilityCovariance μ∞ f g| ≤ C * Real.exp (-m * t) := by
  exact probabilityCovariance_abs_le_of_weak_limit
    hμ f g (C * Real.exp (-m * t)) hfinite

/--
Dense-class clustering extension, the analytic component of Agda R583.

The continuity modulus is uniform in Euclidean time and controls both
observable slots.  Density is given as an actual metric approximation rather
than an abstract proposition called "dense".  This theorem does NOT infer
CMP119 Wilson-product density or the bound from a single selected Wilson pair.
Those are the separate physical H1/OS4 hypotheses.
-/
theorem full_test_clustering_of_uniform_dense_wilson_clustering
    {Test : Type*} [MetricSpace Test]
    (wilsonProducts : Set Test)
    (connected : ℕ → Test → Test → ℝ)
    (hDense :
      ∀ (test : Test) (δ : ℝ), 0 < δ →
        ∃ w ∈ wilsonProducts, dist test w < δ)
    (hUniform :
      ∀ (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (n : ℕ) (left left' right right' : Test),
            dist left left' < δ →
            dist right right' < δ →
            |connected n left right - connected n left' right'| < ε)
    (hWilson :
      ∀ left ∈ wilsonProducts, ∀ right ∈ wilsonProducts,
        Tendsto (fun n : ℕ => connected n left right) atTop (𝓝 0)) :
    ∀ left right : Test,
      Tendsto (fun n : ℕ => connected n left right) atTop (𝓝 0) := by
  intro left right
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hεtwo : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hcontinuity⟩ := hUniform (ε / 2) hεtwo
  obtain ⟨wleft, hwleft, hdleft⟩ := hDense left δ hδ
  obtain ⟨wright, hwright, hdright⟩ := hDense right δ hδ
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1 (hWilson wleft hwleft wright hwright)
      (ε / 2) hεtwo
  refine ⟨N, ?_⟩
  intro n hn
  have hnear :
      |connected n left right - connected n wleft wright| < ε / 2 :=
    hcontinuity n left wleft right wright hdleft hdright
  have hsmall : |connected n wleft wright| < ε / 2 := by
    simpa [Real.dist_eq] using hN n hn
  have htriangle :
      |connected n left right| ≤
        |connected n left right - connected n wleft wright| +
          |connected n wleft wright| := by
    calc
      |connected n left right| =
          |(connected n left right - connected n wleft wright) +
            connected n wleft wright| := by
            congr 1
            ring
      _ ≤
          |connected n left right - connected n wleft wright| +
            |connected n wleft wright| := abs_add_le _ _
  have hfinal : |connected n left right| < ε := by linarith
  simpa [Real.dist_eq] using hfinal

/--
OS4 dense-class extension in the **local** topology of a selected physical
test pair.  Unlike global equicontinuity on the entire unbounded Hilbert
space, this only needs a modulus in a neighbourhood of the chosen
observable pair, uniformly in Euclidean time.

Instantiating the metric by the OS Hilbert norm requires the actual
reflection-positive quotient and its Wilson-vector map.  Those are the
physical obligations, not part of this generic theorem.
-/
theorem full_test_clustering_of_locally_uniform_dense_wilson_clustering
    {Test : Type*} [MetricSpace Test]
    (wilsonProducts : Set Test)
    (connected : ℕ → Test → Test → ℝ)
    (hDense :
      ∀ (test : Test) (δ : ℝ), 0 < δ →
        ∃ w ∈ wilsonProducts, dist test w < δ)
    (hLocalUniform :
      ∀ (left right : Test) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (n : ℕ) (left' right' : Test),
            dist left left' < δ →
            dist right right' < δ →
            |connected n left right - connected n left' right'| < ε)
    (hWilson :
      ∀ left ∈ wilsonProducts, ∀ right ∈ wilsonProducts,
        Tendsto (fun n : ℕ => connected n left right) atTop (𝓝 0)) :
    ∀ left right : Test,
      Tendsto (fun n : ℕ => connected n left right) atTop (𝓝 0) := by
  intro left right
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hεtwo : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hcontinuity⟩ := hLocalUniform left right (ε / 2) hεtwo
  obtain ⟨wleft, hwleft, hdleft⟩ := hDense left δ hδ
  obtain ⟨wright, hwright, hdright⟩ := hDense right δ hδ
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1 (hWilson wleft hwleft wright hwright)
      (ε / 2) hεtwo
  refine ⟨N, ?_⟩
  intro n hn
  have hnear :
      |connected n left right - connected n wleft wright| < ε / 2 :=
    hcontinuity n wleft wright hdleft hdright
  have hsmall : |connected n wleft wright| < ε / 2 := by
    simpa [Real.dist_eq] using hN n hn
  have htriangle :
      |connected n left right| ≤
        |connected n left right - connected n wleft wright| +
          |connected n wleft wright| := by
    calc
      |connected n left right| =
          |(connected n left right - connected n wleft wright) +
            connected n wleft wright| := by
            congr 1
            ring
      _ ≤
          |connected n left right - connected n wleft wright| +
            |connected n wleft wright| := abs_add_le _ _
  have hfinal : |connected n left right| < ε := by linarith
  simpa [Real.dist_eq] using hfinal

end RequestProject.YangMills
