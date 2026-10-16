import RequestProject.QuantumMereologyHeterogeneousFiniteAtlas
import RequestProject.QuantumMereologyFiniteSubsetMarginal
import RequestProject.QuantumMereologyPartialTraceCoherence
import RequestProject.QuantumMereologyPartialTraceCoherenceRegression
import RequestProject.QuantumMereologyEnvironmentReindex
import RequestProject.QuantumMereologyEnvironmentReindexRegression
import RequestProject.QuantumMereologyGTPSShortTime2026
import RequestProject.QuantumMereologyGTPSProjectionProducer
import RequestProject.QuantumMereologyGTPSProjectionProducerRegression
import RequestProject.QuantumMereologyPointerObjectivity2026
import RequestProject.QuantumMereologySelectionConvergence2026

/-!
# Selected-atlas terminal max-cut

This owner records the phase boundary after the heterogeneous-coordinate and
source-facing g-TPS tranches. It deliberately distinguishes:

* finite coordinate theorems now paid by DASHI;
* exact external-source formulas reconstructed over explicit source objects;
* finite Hilbert--Schmidt projectors now derived from pinned mathlib rather
  than treated as physical/source inputs;
* remaining same-object physical/Hilbert/operator-algebra attachments;
* downstream information-geometry, holography and spacetime promotions.

No status flag below upgrades an external paper into local theorem authority.
-/

namespace QuantumMereology
namespace SelectedAtlasTerminalMaxCut

structure Boundary where
  -- Finite same-state atlas payments.
  heterogeneousCanonicalPairChartsPaid : Bool := true
  arbitraryFiniteSubsetMarginalsPaid : Bool := true
  pairAndSubsetDensityPreservationPaid : Bool := true
  iteratedProductPartialTraceAssociativityPaid : Bool := true
  environmentRelabelingInvariancePaid : Bool := true

  -- Source-facing g-TPS recut/formulas.
  sourceGeneralGTPSCarrierPaid : Bool := true
  sourceGTPSShortTimeFormulaPaid : Bool := true
  sourceGTPSAlgebraDistanceFormulaPaid : Bool := true
  orthogonalProjectionProducerForFiniteSourceAlgebrasPaid : Bool := true
  finiteSourceGTPSShortTimeScoreFullyInstantiated : Bool := true
  finiteSourceGTPSAlgebraDistanceFullyInstantiated : Bool := true
  finiteShortTimeSelectionCompilerPaid : Bool := true

  -- Exact next state/TPS coherence leaves.
  arbitrarySelectedHilbertTPSToCoordinateAtlasPaid : Bool := false
  arbitrarySelectedGTPSToCoordinateAtlasPaid : Bool := false
  nestedMarginalCoherencePaid : Bool := false
  arbitraryRetainedCoordinateChartIndependencePaid : Bool := false
  retainedEnvironmentMixingChartIndependencePaid : Bool := false

  -- Physical pointer/selection leaves.
  selectedCPOPhysicalSelfAdjointnessPaid : Bool := false
  mathematicalEigenbasisToPhysicalPointerWeldPaid : Bool := false
  sourceFaithfulPhysicalSearchDomainPaid : Bool := false
  physicalSourceGTPSIdentificationPaid : Bool := false
  physicalHamiltonianAttachmentPaid : Bool := false
  crossObjectivePhysicalConvergencePaid : Bool := false

  -- g-TPS source geometry still missing.
  sourceRiemannianPullbackPaid : Bool := false
  sourceAlgebraSusceptibilityPaid : Bool := false
  thermodynamicLimitMQPTPaid : Bool := false

  -- Information geometry.
  quantumMutualInformationInequalityPackagePaid : Bool := false
  ccmGraphGlobalMetricAssumptionsPaid : Bool := false
  mdsSpatialRealizationPaid : Bool := false

  -- Downstream same-object physics.
  sameStateHolographicWeldPaid : Bool := false
  lorentzianCauchyPromotionPaid : Bool := false
  einsteinDynamicsPromotionPaid : Bool := false

deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem heterogeneous_pair_charts_paid :
    canonicalBoundary.heterogeneousCanonicalPairChartsPaid = true := rfl

theorem arbitrary_subset_marginals_paid :
    canonicalBoundary.arbitraryFiniteSubsetMarginalsPaid = true := rfl

theorem partial_trace_associativity_paid :
    canonicalBoundary.iteratedProductPartialTraceAssociativityPaid = true := rfl

theorem environment_relabeling_invariance_paid :
    canonicalBoundary.environmentRelabelingInvariancePaid = true := rfl

theorem source_gtps_short_time_formula_paid :
    canonicalBoundary.sourceGTPSShortTimeFormulaPaid = true := rfl

theorem finite_source_gtps_projectors_paid :
    canonicalBoundary.orthogonalProjectionProducerForFiniteSourceAlgebrasPaid = true := rfl

theorem nested_marginal_coherence_open :
    canonicalBoundary.nestedMarginalCoherencePaid = false := rfl

theorem same_state_holographic_weld_open :
    canonicalBoundary.sameStateHolographicWeldPaid = false := rfl

/-- Cross-module DASHI status receipt. -/
def dashiSelectedAtlasTerminalReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI Lean"
  claim := "Records that heterogeneous finite coordinate pair charts, arbitrary finite-subset same-state marginals, ordinary finite product partial-trace associativity, environment-relabeling invariance, the corrected source-facing operator-algebra g-TPS carrier, squared short-time scrambling and algebra-distance formulas, canonical finite Hilbert--Schmidt projectors, and finite score minimization are source-written in their dedicated owners. It keeps arbitrary selected Hilbert/g-TPS attachment, dependent nested marginal coherence, retained-coordinate/mixing chart independence, physical pointer and physical source-algebra/Hamiltonian identification, algebra susceptibility, MI metric geometry, holography and spacetime dynamics explicitly unpaid."

end SelectedAtlasTerminalMaxCut
end QuantumMereology
