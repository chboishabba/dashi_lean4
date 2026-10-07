import Mathlib
import YangMills.YMClayFiveCampaignFrontier20261007
import YangMills.CMP116WilsonPointwiseLocalization

/-!
# Yang--Mills four-campaign terminal frontier — 2026-10-07

This is the shortest current honest board after internalizing the centered
vacuum sector, excitation restriction, W3 finite aggregation and no-pollution
spectral contradiction.

The live proof programmes are now:

1. BC: source-native CMP119 E/R/B reflection geometry and actual crossing
   kernels.  Successful source extraction already terminates in the complete
   Wilson × E/R/B/V functional RP kernel.
2. C/E1: identify the published source Haar/coupling/Wilson normalization with
   the canonical selected Lean cutoff, and identify the intended physical
   Wilson algebra with its bounded cylinder representation.
3. F1: W1 plus pointwise connecting-cluster localization, a localized shell
   charge majorant and physical support-distance/time semantics.  The aggregate
   W3 inequality is compiler-owned.
4. E2/GEN: construct the physical strongly-continuous OS extension of the same
   discrete transfer, its same-H nonnegative self-adjoint generator, physical
   time step and standard functional calculus.  Once a genuine subgap H-window
   is converted into the same transfer spectral window, the gap contradiction
   is compiler-owned by `YMClayFiveCampaignFrontier20261007`.

G remains downstream: physical same-object composite/local-stress
identification, accepted OS/Wightman reconstruction, nontriviality, and the
same-theory extension to every compact simple gauge group.

No conditional source theorem is promoted here.
-/

namespace RequestProject.YangMills

/-! ## F1: W3 aggregation is no longer a source leaf -/

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

/--
The preferred F1 source surface now stores W1 plus local cluster estimates,
then compiles directly to the existing mixed half-rate source.
-/
def ym20261007F1FromPointwiseLocalization
    {Ω Obs Cluster : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster]
    (source : CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster) :
    CMP116WilsonMixedHalfRateClusteringSource Ω Obs :=
  source.toMixedHalfRateSource

/-- Exact remaining F1 source producer after paying finite W3 aggregation. -/
def YM20261007F1PointwiseLocalizationProducerExists
    (Ω Obs Cluster : Type*)
    [MeasurableSpace Ω] [TopologicalSpace Ω]
    [DecidableEq Cluster] : Prop :=
  Nonempty (CMP116WilsonPointwiseLocalizationSource Ω Obs Cluster)

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
