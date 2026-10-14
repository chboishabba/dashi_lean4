import Integration.RationalAlbertNormUnitRigidityExact

namespace Integration.RationalAlbertCubicRigidityRegression
open Integration.RationalAlbertCubicRigidity

example : canonicalBoundary.traceRecoveredFromNorm = true := rfl
example : canonicalBoundary.tracePairRecoveredFromNorm = true := rfl
example : canonicalBoundary.adjointRecoveredFromNorm = true := rfl
example : canonicalBoundary.unitFixingNormSymmetryIsJordan = true := rfl

example : NormUnitRigidity := canonicalNormUnitRigidity

example (g : UnitFixingNormSymmetry) (X Y : A27) :
    g.forward (jordanProduct X Y) =
      jordanProduct (g.forward X) (g.forward Y) :=
  unitFixingNormSymmetry_map_jordan g X Y

end Integration.RationalAlbertCubicRigidityRegression
