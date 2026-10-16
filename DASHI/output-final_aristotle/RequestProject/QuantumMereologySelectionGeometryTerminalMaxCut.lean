import RequestProject.QuantumMereologyMaxCut
import RequestProject.QuantumMereologyFiniteNChartedAtlas
import RequestProject.QuantumMereologyPointerObjectivity2026
import RequestProject.QuantumMereologySelectionConvergence2026
import RequestProject.QuantumMereologyGeneralizedTPS2026

/-!
# Quantum-mereology selection -> geometry terminal max-cut

This owner is a machine-readable phase boundary over the theorem surfaces now
present on the branch.  It does not manufacture any missing physics.  The goal
is to prevent already-paid finite infrastructure from being repeatedly charged
while keeping the true same-object and analytic leaves explicit.

Paid/source-written on this branch:
* selected-TPS / consumer-relative geometry composition;
* finite selected-product CPO spectral basis under literal symmetry refinement;
* finite Born closure;
* finite von Neumann entropy and bipartite mutual information;
* three-factor same-global-state overlap consistency;
* charted homogeneous finite-N pair extraction from one global density state;
* finite nonempty Schwinger minimizer existence;
* cross-objective selection comparison/convergence surface;
* finite-dimensional operator-algebra g-TPS carrier and finite-family minimizer;
* source-bounded 2026 pointer/objectivity comparison.

Still open:
* physical/source-backed CPO self-adjointness and pointer identification;
* source-faithful physical search-domain payment;
* heterogeneous selected-TPS -> finite-N chart family attachment;
* chart-independence / global overlap coherence for that attachment;
* quantum mutual-information inequalities needed by stronger graph claims;
* Zanardi source scrambling functional / information metric / susceptibility;
* CCM graph-global metric assumptions and MDS realization;
* same-object RT/holographic state weld;
* Lorentzian/Cauchy/Einstein dynamics.
-/

namespace QuantumMereology
namespace SelectionGeometryTerminalMaxCut

/-- Ordered residual producer classes.  The order is dependency-oriented, not a
claim of scientific importance or empirical likelihood. -/
inductive ResidualLeaf where
  | physicalCPOSymmetry
  | physicalPointerWeld
  | physicalSearchDomain
  | heterogeneousSelectedTPSAtlas
  | chartCoherence
  | mutualInformationInequalities
  | sourceScramblingFunctional
  | sourceInformationMetric
  | ccmMetricAssumptions
  | ccmMDSRealization
  | sameObjectHolographicWeld
  | lorentzianSpacetimePromotion
deriving Repr, DecidableEq

/-- Dependency-oriented next-producer order.  This list is a DASHI scheduling
artifact only; it is not an external scientific source claim. -/
def preferredResidualOrder : List ResidualLeaf :=
  [ .physicalCPOSymmetry
  , .physicalPointerWeld
  , .physicalSearchDomain
  , .heterogeneousSelectedTPSAtlas
  , .chartCoherence
  , .mutualInformationInequalities
  , .sourceScramblingFunctional
  , .sourceInformationMetric
  , .ccmMetricAssumptions
  , .ccmMDSRealization
  , .sameObjectHolographicWeld
  , .lorentzianSpacetimePromotion
  ]

structure Status where
  selectedTPSGeometryCompositionPaid : Bool := true
  selectedProductCPOBasisConditionalPaid : Bool := true
  finiteBornClosurePaid : Bool := true
  finiteVonNeumannMutualInformationPaid : Bool := true
  tripartiteOverlapConsistencyPaid : Bool := true
  chartedFiniteNPairExtractionPaid : Bool := true
  finiteSchwingerMinimizerPaid : Bool := true
  crossObjectiveComparisonSurfacePaid : Bool := true
  pointerObjectivityComparisonSurfacePaid : Bool := true
  operatorAlgebraGTPSCarrierPaid : Bool := true
  finiteGTPSFamilyMinimizerPaid : Bool := true

  physicalCPOSymmetryPaid : Bool := false
  physicalPointerWeldPaid : Bool := false
  physicalSearchDomainPaid : Bool := false
  heterogeneousSelectedTPSAtlasPaid : Bool := false
  chartCoherencePaid : Bool := false
  mutualInformationInequalitiesPaid : Bool := false
  sourceScramblingFunctionalPaid : Bool := false
  sourceInformationMetricPaid : Bool := false
  algebraSusceptibilityPaid : Bool := false
  ccmMetricAssumptionsPaid : Bool := false
  ccmMDSRealizationPaid : Bool := false
  sameObjectHolographicWeldPaid : Bool := false
  lorentzianSpacetimePromotionPaid : Bool := false
deriving Repr, DecidableEq

def canonicalStatus : Status := {}

theorem charted_finite_n_pair_extraction_paid :
    canonicalStatus.chartedFiniteNPairExtractionPaid = true := rfl

theorem operator_algebra_gtps_carrier_paid :
    canonicalStatus.operatorAlgebraGTPSCarrierPaid = true := rfl

theorem physical_pointer_weld_remains_open :
    canonicalStatus.physicalPointerWeldPaid = false := rfl

theorem ccm_mds_realization_remains_open :
    canonicalStatus.ccmMDSRealizationPaid = false := rfl

/-- Cross-module synthesis receipt only.  No external source is credited with
this exact scheduling decomposition. -/
def dashiSelectionGeometryTerminalReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI Lean"
  claim := "Terminal phase accounting for the current quantum-mereology branch: finite spectral/probability/information/selection/g-TPS infrastructure is separated from the remaining physical pointer, selected-TPS chart-coherence, MI inequality, source scrambling/metric, CCM MDS, same-object holographic and Lorentzian/spacetime producers. The ordering is dependency scheduling, not empirical authority."

end SelectionGeometryTerminalMaxCut
end QuantumMereology
