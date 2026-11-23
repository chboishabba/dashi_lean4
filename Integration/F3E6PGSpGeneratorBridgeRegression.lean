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

example (i : Fin 6) : e6ReducedGenerator i * e6ReducedGenerator i = 1 :=
  e6ReducedGenerator_involutive i

example (w : List (Fin 6)) :
    wordAction pgspFiveGenerator w = wordAction e6ReducedGenerator w :=
  generatedFiveSpaceWordAction_eq w

example : generatorBridgeBoundary.sixGeneratorIntertwiningPaid = true := rfl
example : generatorBridgeBoundary.generatedFiveSpaceActionEqualityPaid = true := rfl
example : generatorBridgeBoundary.abstractPGSpQuotientWeylIsomorphismPaid = false := rfl

end DASHI.Integration.F3E6PGSpGeneratorBridgeRegression
