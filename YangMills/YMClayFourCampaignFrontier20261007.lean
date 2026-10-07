import Mathlib
import YangMills.YMClayFiveCampaignFrontier20261007
import YangMills.CMP116WilsonMarkedExpansionLocalization
import YangMills.CMP119SelectedHeterogeneousCylinderLaw
import YangMills.CompactSimpleCasimirOrbitFactorization

/-!
# Yang--Mills four-campaign terminal frontier — 2026-10-07

This is the shortest current honest board after internalizing the centered
vacuum sector, excitation restriction, W1 connected filtering, W3 finite
aggregation, no-pollution spectral contradiction, varying-cutoff cylinder
transport and generic compact-simple Casimir transport.

The live proof programmes are now:

1. BC: source-native CMP119 E/R/B reflection geometry and actual crossing
   kernels.  Successful source extraction already terminates in the complete
   Wilson × E/R/B/V functional RP kernel.
2. C/E1: identify the published source Haar/coupling/Wilson normalization with
   the canonical selected Lean cutoff, and identify the intended physical
   Wilson algebra with its bounded cylinder representation.  Once a measurable
   cutoff-dependent Wilson coordinate family is supplied, the changing finite
   lattice carriers are already pushed to one common compact determining cube.
3. F1: the source-native full marked-expansion/response identity, derivative
   vanishing away from clusters touching both Wilson supports, pointwise
   connecting-cluster localization, a localized shell-charge majorant and
   physical support-distance/time semantics.  Both connected-only filtering and
   aggregate W3 summation are compiler-owned.
4. E2/GEN: construct the physical strongly-continuous OS extension of the same
   discrete transfer, its same-H nonnegative self-adjoint generator, physical
   time step and standard functional calculus.  Once a genuine subgap H-window
   is converted into the same transfer spectral window, the gap contradiction
   is compiler-owned by `YMClayFiveCampaignFrontier20261007`.

G remains downstream, but generic all-group scaling is no longer a leaf.  Once
the physical Wilson/ghost/Haar colour algebra identifies the selected compact
simple group expression as `C_A × universalFourOrbit`, the orbit sum and every
certified universal lower bound transport automatically.  The remaining G bill
is therefore the physical Casimir factorization, physical same-object
composite/local-stress identification, accepted OS/Wightman reconstruction,
nontriviality, and same-theory completion for every compact simple group.

No conditional source theorem is promoted here.
-/

namespace RequestProject.YangMills

/-! ## C/DF2: varying finite carriers already share one determining cylinder law -/

/--
Selected physical cutoffs of sizes `k+1` push to one exact bounded determining
source on the common countable cylinder cube.  No common raw lattice carrier is
assumed.
-/
noncomputable def ym20261007SelectedHeterogeneousCylinderDeterminingSource
    (cutoff : ∀ k : ℕ, CMP119SelectedPhysicalCutoff (k + 1))
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i)) :
    RealCountableObservableDeterminingSource HeterogeneousWilsonCylinderState :=
  selectedCMP119HeterogeneousDeterminingSource cutoff raw hMeas

/-! ## F1: connected filtering and W3 aggregation are compiler-owned -/

/-- Exact finite W3 aggregation from pointwise localization and shell charge. -/
theorem ym20261007W3FiniteAggregationCompiler
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight shellCharge : Cluster → ℝ)
    (shell : ℝ)
    (hpoint : ∀ c ∈ clusters, |weight c| ≤ shellCharge c)
    (hshell : (∑ c ∈ clusters, shellCharge c) ≤ shell) :
    (∑ c ∈ clusters, |weight c|) ≤ shell :=
  finite_abs_weight_sum_le_shell_of_pointwise_localization
    clusters weight shellCharge shell hpoint hshell

/-- Exact finite W1 support filter from marked locality/derivative vanishing. -/
theorem ym20261007W1ConnectingFilterCompiler
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight : Cluster → ℝ)
    (touchesLeft touchesRight : Cluster → Bool)
    (hzero : ∀ c ∈ clusters,
      ¬ (touchesLeft c = true ∧ touchesRight c = true) → weight c = 0) :
    (∑ c ∈ clusters, weight c) =
      ∑ c ∈ clusters.filter (fun c => touchesLeft c && touchesRight c), weight c :=
  full_cluster_sum_eq_connecting_filter
    clusters weight touchesLeft touchesRight hzero

/--
The preferred F1 source surface is now the full marked/local source; both finite
connected filtering and aggregate W3 compilation are derived.
-/
def ym20261007F1FromMarkedLocalization
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster) :
    CMP116WilsonMixedHalfRateClusteringSource Ω Obs :=
  source.toMixedHalfRateSource

/-- Exact remaining F1 source producer at the marked-localization boundary. -/
def YM20261007F1MarkedLocalizationProducerExists
    (Ω Obs Cluster : Type*)
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster] : Prop :=
  Nonempty (CMP116WilsonMarkedExpansionLocalizationSource Ω Obs Cluster)

/-! ## G: generic compact-simple Casimir transport is compiler-owned -/

/-- Reuse one universal four-orbit lower bound for every nonnegative `C_A`. -/
theorem ym20261007CompactSimpleCasimirLowerBoundCompiler
    {GaugeGroup : Type*}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (orbit : FourOrbitScalar)
    (bound : UniversalFourOrbitLowerBound orbit) :
    carrier.adjointCasimir group * bound.lower ≤
      groupScaledOneLoopCoefficient carrier group orbit :=
  compact_simple_casimir_transports_universal_lower_bound
    carrier group orbit bound

/--
Exact remaining group-specific producer before generic Casimir reuse: prove the
literal physical one-loop coefficient is the selected `C_A × universal` object.
-/
def YM20261007PhysicalCompactSimpleCasimirFactorizationExists
    (GaugeGroup : Type*) : Prop :=
  Nonempty (CompactSimplePhysicalCasimirFactorization GaugeGroup)

/-!
The rest of the preferred terminal path is inherited without weakening from the
five-campaign owner:

* `ym20261007BCCompleteFunctionalCompiler` closes BC assembly after source
  extraction;
* `CMP119SelectedPhysicalCutoff` fixes canonical product Haar and physical beta;
* `YM20261007FiveCampaignSameHGapAssembly.no_subgap_spectrum` derives the gap
  contradiction from genuine same-H spectral calculus;
* `excitation_continuous_nat_eq_discrete` proves the continuous and discrete
  excitation transfers are exactly the same at integer Euclidean times.
-/

end RequestProject.YangMills
