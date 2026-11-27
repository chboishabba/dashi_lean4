import Integration.F3E6PGSpSameObjectBridge

namespace DASHI.Integration.F3E6PGSpSameObjectBridgeRegression

open F3E6PGSpSameObjectBridge

example (q : Primitive5) :
    E6Bridge.standardQuadratic (primitiveToStandard q) = 2 * primitiveQuadratic q :=
  primitiveToStandard_scaled_isometry q

example (i : Fin 6) (z : E6Bridge.F3Five) :
    standardMatrixAct (e6StandardGenerator i) z =
      E6Weyl.reflectStandard (reflectionIndex i) z :=
  e6StandardGenerator_models_repo_action i z

example (i : Fin 6) :
    standardExteriorAction (pgspLift i) = e6StandardGenerator i :=
  exterior_pgspLift_eq_repoE6Generator i

example (w : List (Fin 6)) :
    wordAction pgspStandardFiveGenerator w = wordAction e6StandardGenerator w :=
  generatedRepoE6FiveSpaceAction_eq w

example : sameObjectBoundary.repoE6GeneratorIntertwiningPaid = true := rfl
example : sameObjectBoundary.generatedRepoE6FiveSpaceActionEqualityPaid = true := rfl
example : sameObjectBoundary.abstractPGSpQuotientWeylIsomorphismPaid = false := rfl

end DASHI.Integration.F3E6PGSpSameObjectBridgeRegression
