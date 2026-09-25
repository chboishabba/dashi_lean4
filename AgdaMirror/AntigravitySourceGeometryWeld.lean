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

theorem physical_same_object_remains_parity :
    ag7CMP119PhysicalSameObjectStillRequired = true := rfl

theorem conditional_assembly_parity :
    ag8ConditionalAssemblyCompiled = true := rfl

end AgdaMirror.AntigravitySourceGeometryWeld
