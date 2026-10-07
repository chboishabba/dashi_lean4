import Mathlib
import YangMills.YMClayFourCampaignFrontier20261007

open MeasureTheory

namespace RequestProject.YangMills

example
    (cutoff : ∀ k : ℕ, CMP119SelectedPhysicalCutoff (k + 1))
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i)) :
    RealCountableObservableDeterminingSource HeterogeneousWilsonCylinderState :=
  ym20261007SelectedHeterogeneousCylinderDeterminingSource cutoff raw hMeas

example
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [DecidableEq Cluster]
    (source : CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster) :
    CMP116WilsonMixedHalfRateClusteringSource Ω Obs :=
  ym20261007F1FromPointwiseLocalization source

example
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight shellCharge : Cluster → ℝ)
    (shell : ℝ)
    (hpoint : ∀ c ∈ clusters, |weight c| ≤ shellCharge c)
    (hshell : (∑ c ∈ clusters, shellCharge c) ≤ shell) :
    (∑ c ∈ clusters, |weight c|) ≤ shell :=
  ym20261007W3FiniteAggregationCompiler
    clusters weight shellCharge shell hpoint hshell

example
    {GaugeGroup : Type*}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (orbit : FourOrbitScalar)
    (bound : UniversalFourOrbitLowerBound orbit) :
    carrier.adjointCasimir group * bound.lower ≤
      groupScaledOneLoopCoefficient carrier group orbit :=
  ym20261007CompactSimpleCasimirLowerBoundCompiler
    carrier group orbit bound

end RequestProject.YangMills
