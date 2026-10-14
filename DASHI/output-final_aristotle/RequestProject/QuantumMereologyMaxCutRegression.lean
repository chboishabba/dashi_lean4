import RequestProject.QuantumMereologyMaxCut
import RequestProject.QuantumMereologyStandardBasisProjector
import RequestProject.QuantumMereologyFiniteHermitianCPO
import RequestProject.QuantumMereologyBornProbability
import RequestProject.QuantumMereologyVonNeumannInformation

namespace QuantumMereology
namespace MaxCutRegression

example :
    MaxCut.canonicalBoundary.sourceWrittenProducerCreatesSelection = false :=
  MaxCut.source_written_producer_does_not_create_selection

example :
    MaxCut.canonicalBoundary.selectedTPSCreatesGeometryWithoutPairRelation = false :=
  MaxCut.selected_tps_does_not_create_geometry_without_pair_relation

example :
    MaxCut.canonicalBoundary.spatialGeometryCreatesSpacetime = false :=
  MaxCut.spatial_geometry_does_not_create_spacetime

example :
    MaxCut.canonicalBoundary.geometryCriterionCollisionCreatesRefinementObligation = true :=
  MaxCut.geometry_collision_creates_refinement_obligation

example :
    MaxCut.canonicalBoundary.geometryConsumerObserverIsLeastSufficient = true :=
  MaxCut.geometry_consumer_observer_is_least_sufficient

example :
    MaxCut.canonicalBoundary.holographicBoundaryAdequacyIsConsumerRelative = true :=
  MaxCut.holographic_boundary_adequacy_is_consumer_relative

example :
    StandardBasisProjector.canonicalBoundary.standardBasisProjectorFamilyPaid = true :=
  StandardBasisProjector.standard_basis_projector_family_paid

example :
    StandardBasisProjector.canonicalBoundary.finiteHermitianSpectralBasisPaid = true :=
  StandardBasisProjector.finite_hermitian_spectral_basis_paid

example :
    StandardBasisProjector.canonicalBoundary.arbitrarySelectedCPOEigenbasisPaid = false :=
  StandardBasisProjector.arbitrary_selected_cpo_eigenbasis_not_paid

example :
    FiniteHermitianCPO.canonicalBoundary.typedSelectedCPORefinementCompilesHermitianMatrices = true :=
  FiniteHermitianCPO.typed_selected_cpo_refinement_compiles_hermitian_matrices

example :
    FiniteHermitianCPO.canonicalBoundary.genericAdmissibilityConstructsTypedSymmetry = false :=
  FiniteHermitianCPO.generic_admissibility_does_not_construct_typed_symmetry

example :
    BornProbability.canonicalBoundary.coordinateBornProbabilityNonnegativePaid = true :=
  BornProbability.coordinate_born_probability_nonnegative_paid

example :
    BornProbability.canonicalBoundary.coordinateBornProbabilityNormalizedPaid = true :=
  BornProbability.coordinate_born_probability_normalized_paid

example :
    BornProbability.canonicalBoundary.coordinateProbabilityCreatesPhysicalPointerIdentification = false :=
  BornProbability.coordinate_probability_does_not_create_physical_pointer_identification

example :
    VonNeumannInformation.canonicalBoundary.finiteVonNeumannEntropyDefined = true :=
  VonNeumannInformation.finite_von_neumann_entropy_defined

example :
    VonNeumannInformation.canonicalBoundary.bipartiteMutualInformationDefined = true :=
  VonNeumannInformation.bipartite_mutual_information_defined

example :
    VonNeumannInformation.canonicalBoundary.mutualInformationAutomaticallyCreatesMetric = false :=
  VonNeumannInformation.mutual_information_does_not_automatically_create_metric

example :
    VonNeumannInformation.canonicalBoundary.ccmDistanceAnsatzKeptSeparate = true :=
  VonNeumannInformation.ccm_distance_ansatz_kept_separate

end MaxCutRegression
end QuantumMereology
