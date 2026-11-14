import Mathlib
import YangMills.CMP116WilsonPointwiseLocalization

open MeasureTheory

/-!
# W1 connected-cluster filter from support-indexed marked locality

The preferred Agda source does not need the connected-cluster sum itself as an
independent physical field.  It starts from a support-indexed marked expansion,
then uses mixed-derivative vanishing away from clusters touching BOTH Wilson
supports to filter the full finite sum down to the connected family.

This file mirrors that finite compiler step.  The physical/source inputs remain
the actual marked expansion/response identity, the locality/vanishing theorem,
pointwise Wilson-cluster localization, the shell-charge majorant, and physical
support-distance/time semantics.
-/

namespace RequestProject.YangMills

/-- Finite support filtering removes terms which vanish away from both supports. -/
theorem full_cluster_sum_eq_connecting_filter
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight : Cluster → ℝ)
    (touchesLeft touchesRight : Cluster → Bool)
    (hzero : ∀ c ∈ clusters,
      ¬ (touchesLeft c = true ∧ touchesRight c = true) → weight c = 0) :
    (∑ c ∈ clusters, weight c) =
      ∑ c ∈ clusters.filter (fun c => touchesLeft c && touchesRight c), weight c := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hnot
  apply hzero c hc
  intro hboth
  apply hnot
  simp [hc, hboth.1, hboth.2]

/--
Source-facing W1+localization package before finite connected filtering.
Everything is indexed by the same Euclidean translation time as the physical
Wilson covariance.
-/
structure CMP116WilsonMarkedExpansionLocalizationSource
    (Ω Obs Cluster : Type*)
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  continuumLaw : ProbabilityMeasure Ω
  wilson : Obs → BoundedContinuousFunction Ω ℝ
  timeTranslate : Obs → ℕ → BoundedContinuousFunction Ω ℝ

  allClusters : ℕ → Obs → Obs → ℕ → Finset Cluster
  clusterWeight : ℕ → Obs → Obs → ℕ → Cluster → ℝ
  touchesLeft : ℕ → Obs → Obs → ℕ → Cluster → Bool
  touchesRight : ℕ → Obs → Obs → ℕ → Cluster → Bool

  -- Source-native marked expansion/response identity before locality filtering.
  covarianceEqFullMarkedSum :
    ∀ cutoff left right time,
      probabilityCovariance (cutoffLaw cutoff)
          (wilson left) (timeTranslate right time) =
        ∑ c ∈ allClusters cutoff left right time,
          clusterWeight cutoff left right time c

  -- Mixed derivative vanishes unless the cluster meets both selected supports.
  disconnectedWeightZero :
    ∀ cutoff left right time c,
      c ∈ allClusters cutoff left right time →
      ¬ (touchesLeft cutoff left right time c = true ∧
         touchesRight cutoff left right time c = true) →
      clusterWeight cutoff left right time c = 0

  shellCharge : ℕ → Obs → Obs → ℕ → Cluster → ℝ
  pointwiseLocalization :
    ∀ cutoff left right time c,
      c ∈ (allClusters cutoff left right time).filter
        (fun cluster =>
          touchesLeft cutoff left right time cluster &&
          touchesRight cutoff left right time cluster) →
      |clusterWeight cutoff left right time c| ≤
        shellCharge cutoff left right time c
  localizedShellChargeSum :
    ∀ cutoff left right time,
      (∑ c ∈ (allClusters cutoff left right time).filter
          (fun cluster =>
            touchesLeft cutoff left right time cluster &&
            touchesRight cutoff left right time cluster),
        shellCharge cutoff left right time c) ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time

namespace CMP116WilsonMarkedExpansionLocalizationSource

/-- The selected connected family is definitionally the both-support filter. -/
def connectingClusters
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster)
    (cutoff : ℕ) (left right : Obs) (time : ℕ) : Finset Cluster :=
  (source.allClusters cutoff left right time).filter
    (fun cluster =>
      source.touchesLeft cutoff left right time cluster &&
      source.touchesRight cutoff left right time cluster)

/-- Locality/derivative-vanishing compiles the full marked sum to the connecting sum. -/
theorem covariance_eq_connecting_cluster_sum
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster)
    (cutoff : ℕ) (left right : Obs) (time : ℕ) :
    probabilityCovariance (source.cutoffLaw cutoff)
        (source.wilson left) (source.timeTranslate right time) =
      ∑ c ∈ source.connectingClusters cutoff left right time,
        source.clusterWeight cutoff left right time c := by
  rw [source.covarianceEqFullMarkedSum cutoff left right time]
  exact full_cluster_sum_eq_connecting_filter
    (source.allClusters cutoff left right time)
    (source.clusterWeight cutoff left right time)
    (source.touchesLeft cutoff left right time)
    (source.touchesRight cutoff left right time)
    (source.disconnectedWeightZero cutoff left right time)

/-- Compile the marked/local source directly into the pointwise W3 source. -/
def toPointwiseLocalizationSource
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster) :
    CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster where
  cutoffLaw := source.cutoffLaw
  continuumLaw := source.continuumLaw
  wilson := source.wilson
  timeTranslate := source.timeTranslate
  connectingClusters := source.connectingClusters
  clusterWeight := source.clusterWeight
  shellCharge := source.shellCharge
  covarianceEqClusterSum := source.covariance_eq_connecting_cluster_sum
  pointwiseLocalization := by
    intro cutoff left right time c hc
    exact source.pointwiseLocalization cutoff left right time c hc
  localizedShellChargeSum := by
    intro cutoff left right time
    exact source.localizedShellChargeSum cutoff left right time

/-- Preferred F1 source compiles all the way to the existing mixed half-rate source. -/
def toMixedHalfRateSource
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster) :
    CMP116WilsonMixedHalfRateClusteringSource Ω Obs :=
  source.toPointwiseLocalizationSource.toMixedHalfRateSource

end CMP116WilsonMarkedExpansionLocalizationSource

end RequestProject.YangMills
