import Integration.AntigravitySourceGeometryWeld

namespace AgdaMirror.AntigravitySourceGeometryWeld

open Integration.AntigravitySourceGeometryWeld

/-!
Parity surface for the current Agda antigravity max-cut.

This file does not assert proof-assistant identity.  It records the consumer
shape that Lean expects from the Agda source theorem.
-/

theorem four_diagonal_collapse_parity :
    ag3FourDiagonalCollapseCompiled = true := rfl

theorem local_repulsion_compiler_parity :
    ag4LocalRepulsionCompilerCompiled = true := rfl

theorem source_geometry_calibration_boundary_parity :
    ag5SourceGeometryCalibrationExplicit = true := rfl

theorem physical_einstein_factorization_parity :
    ag5PhysicalEinsteinFactorizationCompiled = true := rfl

theorem measured_g_authority_remains_parity :
    ag5MeasuredGCouplingAuthorityStillRequired = true := rfl

theorem canonical_wilson_gibbs_compiler_parity :
    ag7CanonicalWilsonGibbsCompilerClosed = true := rfl

theorem symmetric_metric_rechart_parity :
    ag7SymmetricMetricRechartClosed = true := rfl

theorem coordinate_round_trip_removed_parity :
    ag7CoordinateRoundTripStillRequired = false := rfl

theorem selected_source_equality_remains_parity :
    ag7SelectedCMP119SourceEqualityStillRequired = true := rfl

theorem physical_same_object_remains_parity :
    ag7CMP119PhysicalSameObjectStillRequired = true := rfl

theorem conditional_assembly_parity :
    ag8ConditionalAssemblyCompiled = true := rfl

end AgdaMirror.AntigravitySourceGeometryWeld
