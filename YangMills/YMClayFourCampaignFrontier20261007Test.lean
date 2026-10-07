import Mathlib
import YangMills.YMClayFourCampaignFrontier20261007

open MeasureTheory

namespace RequestProject.YangMills

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

end RequestProject.YangMills
