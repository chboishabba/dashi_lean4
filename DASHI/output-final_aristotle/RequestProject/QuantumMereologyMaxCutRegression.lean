import RequestProject.QuantumMereologyMaxCut

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

end MaxCutRegression
end QuantumMereology
