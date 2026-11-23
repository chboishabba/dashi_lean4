import Integration.RationalAlbertNormUnitRigidityProof

namespace Integration.RationalAlbertCubicRigidityRegression
open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertNormUnitRigidityProof

example : canonicalBoundary.traceRecoveredFromNorm = true := rfl
example : canonicalBoundary.tracePairRecoveredFromNorm = true := rfl
example : canonicalBoundary.adjointRecoveredFromNorm = true := rfl
example : canonicalBoundary.unitFixingNormSymmetryIsJordan = true := rfl

example : NormUnitRigidity := canonicalNormUnitRigidity

example (g : UnitFixingNormSymmetry) (X Y : A27) :
    g.forward (jordanProduct X Y) =
      jordanProduct (g.forward X) (g.forward Y) :=
  (jordanAutomorphismOfNormUnitSymmetry g).map_jordan X Y

end Integration.RationalAlbertCubicRigidityRegression
