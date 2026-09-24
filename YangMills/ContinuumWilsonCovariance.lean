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

end RequestProject.YangMills
