import Integration.F3E6PGSpGeneratorBridge

namespace DASHI.Integration.F3E6PGSpGeneratorBridgeRegression

open F3E6PGSpGeneratorBridge

example (i : Fin 6) : exteriorAction (pgspGenerator i) = e6ReducedGenerator i :=
  exteriorAction_pgspGenerator i

example (i : Fin 6) :
    Matrix.transpose (pgspGenerator i) * symplecticMatrix * pgspGenerator i = -symplecticMatrix :=
  pgspGenerator_is_antisymplectic i

example (i : Fin 6) :
    Matrix.transpose (e6ReducedGenerator i) * primitivePolarMatrix * e6ReducedGenerator i = primitivePolarMatrix :=
  e6ReducedGenerator_isometry i

example : generatorBridgeBoundary.sixGeneratorIntertwiningPaid = true := rfl
example : generatorBridgeBoundary.fullGeneratedGroupEqualityKernelPaid = false := rfl

end DASHI.Integration.F3E6PGSpGeneratorBridgeRegression
