import Mathlib
import YangMills.ContinuumWilsonCovariance

/-!
# Direct CMP116 two-source clustering cut

The Agda source route already compiles a literal two-source connected shell to
geometric clustering, but its current physical seam is still the same-object
identification of two literal physical source insertions with that CMP116 shell.
This Lean surface records exactly the corresponding source-facing producer and
reuses the existing weak-limit covariance transport.

No source insertion identity is manufactured here.
-/

open Filter MeasureTheory

namespace RequestProject.YangMills

/--
Same-law direct clustering source.  `finiteExponentialClustering` is the literal
CMP116 two-insertion payment; everything else is transport/bookkeeping.
-/
structure CMP116DirectClusteringSource
    (Ω Obs : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  continuumLaw : ProbabilityMeasure Ω
  left right : Obs → ℕ → BoundedContinuousFunction Ω ℝ
  amplitude massRate : ℝ
  amplitudeNonneg : 0 ≤ amplitude
  massRatePositive : 0 < massRate
  finiteExponentialClustering :
    ∀ (cutoff : ℕ) (obs : Obs) (time : ℕ),
      |probabilityCovariance (cutoffLaw cutoff)
          (left obs time) (right obs time)| ≤
        amplitude * Real.exp (-massRate * time)

namespace CMP116DirectClusteringSource

/-- The exact finite clustering bound on the selected source observables. -/
theorem finite_exponential_clustering
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (source : CMP116DirectClusteringSource Ω Obs)
    (cutoff : ℕ) (obs : Obs) (time : ℕ) :
    |probabilityCovariance (source.cutoffLaw cutoff)
        (source.left obs time) (source.right obs time)| ≤
      source.amplitude * Real.exp (-source.massRate * time) :=
  source.finiteExponentialClustering cutoff obs time

/--
Once the SAME cutoff laws converge weakly, the literal CMP116 finite bound
passes to the SAME continuum covariance.
-/
theorem continuum_exponential_clustering
    {Ω Obs : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (source : CMP116DirectClusteringSource Ω Obs)
    (hconv : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw))
    (obs : Obs) (time : ℕ) :
    |probabilityCovariance source.continuumLaw
        (source.left obs time) (source.right obs time)| ≤
      source.amplitude * Real.exp (-source.massRate * time) := by
  exact probabilityCovariance_exponential_bound_of_weak_limit
    hconv (source.left obs time) (source.right obs time)
    source.amplitude source.massRate time
    (fun cutoff => source.finiteExponentialClustering cutoff obs time)

/-- Literal F1 producer existence: deliberately a source obligation. -/
def ProducerExists
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] : Prop :=
  Nonempty (CMP116DirectClusteringSource Ω Obs)

end CMP116DirectClusteringSource

end RequestProject.YangMills
