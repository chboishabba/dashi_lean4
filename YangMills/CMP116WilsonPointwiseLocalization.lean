import Mathlib
import YangMills.CMP116WilsonMixedHalfRateClustering

open MeasureTheory

/-!
# W3 finite aggregation from pointwise Wilson-cluster localization

The current Agda source makes the preferred W3 input local rather than an
opaque aggregate inequality: each actual connecting Wilson cluster is bounded
by a nonnegative shell charge, and the total shell charge is bounded by the
selected rooted-shell majorant.  Finite summation then gives the aggregate W3
bound automatically.

This file mirrors that compiler cut in Lean.  It deliberately does not create
the missing physical pointwise localization theorem, W1 mixed-log identity, or
support-distance/time semantics.
-/

namespace RequestProject.YangMills

/-- Finite absolute connecting-weight aggregation is ordinary monotonicity. -/
theorem finite_abs_weight_sum_le_shell_of_pointwise_localization
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight shellCharge : Cluster → ℝ)
    (shell : ℝ)
    (hpoint : ∀ c ∈ clusters, |weight c| ≤ shellCharge c)
    (hshell : (∑ c ∈ clusters, shellCharge c) ≤ shell) :
    (∑ c ∈ clusters, |weight c|) ≤ shell := by
  exact (Finset.sum_le_sum hpoint).trans hshell

/--
Source-facing finite Wilson clustering data after removing aggregate W3 as an
independent field.  `covarianceEqClusterSum` is the W1 content; W3 is produced
from `pointwiseLocalization` plus `localizedShellChargeSum`.
-/
structure CMP116WilsonPointwiseLocalizationSource
    (Ω Obs Cluster : Type*)
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  continuumLaw : ProbabilityMeasure Ω
  wilson : Obs → BoundedContinuousFunction Ω ℝ
  timeTranslate : Obs → ℕ → BoundedContinuousFunction Ω ℝ
  connectingClusters : ℕ → Obs → Obs → Finset Cluster
  clusterWeight : ℕ → Obs → Obs → Cluster → ℝ
  shellCharge : ℕ → Obs → Obs → Cluster → ℝ
  covarianceEqClusterSum :
    ∀ cutoff left right time,
      probabilityCovariance (cutoffLaw cutoff)
          (wilson left) (timeTranslate right time) =
        ∑ c ∈ connectingClusters cutoff left right,
          clusterWeight cutoff left right c
  pointwiseLocalization :
    ∀ cutoff left right c,
      c ∈ connectingClusters cutoff left right →
      |clusterWeight cutoff left right c| ≤
        shellCharge cutoff left right c
  localizedShellChargeSum :
    ∀ cutoff left right time,
      (∑ c ∈ connectingClusters cutoff left right,
        shellCharge cutoff left right c) ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time

namespace CMP116WilsonPointwiseLocalizationSource

/-- Preferred W3 aggregate inequality is compiler-owned from local charges. -/
theorem aggregate_connecting_weight_bound
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster)
    (cutoff : ℕ) (left right : Obs) (time : ℕ) :
    (∑ c ∈ source.connectingClusters cutoff left right,
      |source.clusterWeight cutoff left right c|) ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  exact finite_abs_weight_sum_le_shell_of_pointwise_localization
    (source.connectingClusters cutoff left right)
    (source.clusterWeight cutoff left right)
    (source.shellCharge cutoff left right)
    ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time)
    (source.pointwiseLocalization cutoff left right)
    (source.localizedShellChargeSum cutoff left right time)

/-- W1 plus pointwise W3 localization yields the exact finite half-rate. -/
theorem finite_half_rate
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster)
    (cutoff : ℕ) (left right : Obs) (time : ℕ) :
    |probabilityCovariance (source.cutoffLaw cutoff)
        (source.wilson left) (source.timeTranslate right time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  rw [source.covarianceEqClusterSum cutoff left right time]
  calc
    |∑ c ∈ source.connectingClusters cutoff left right,
        source.clusterWeight cutoff left right c|
        ≤ ∑ c ∈ source.connectingClusters cutoff left right,
            |source.clusterWeight cutoff left right c| := by
          exact abs_sum_le_sum_abs _ _
    _ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
      source.aggregate_connecting_weight_bound cutoff left right time

/-- Compile directly into the existing mixed half-rate continuum source. -/
def toMixedHalfRateSource
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster) :
    CMP116WilsonMixedHalfRateClusteringSource Ω Obs where
  cutoffLaw := source.cutoffLaw
  continuumLaw := source.continuumLaw
  wilson := source.wilson
  timeTranslate := source.timeTranslate
  finiteHalfRate := source.finite_half_rate

end CMP116WilsonPointwiseLocalizationSource

end RequestProject.YangMills
