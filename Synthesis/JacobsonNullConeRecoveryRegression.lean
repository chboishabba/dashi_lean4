import Synthesis.JacobsonNullConeRecovery

namespace Synthesis.JacobsonNullConeRecoveryRegression

open Synthesis.JacobsonNullConeRecovery

universe u v w

example {Tensor : Type u} {NullDirection : Type v} {Scalar : Type w}
    (R : NullContractedFieldRelation Tensor NullDirection Scalar)
    (G : NullConeTensorRigidity R) :
    TensorEquationModuloMetric R G :=
  recoverTensorEquationModuloMetric R G

example : tensorRecoveryCompilerOwned = true := rfl
example : nullConeRigidityStillRequired = true := rfl
example : nullRelationAloneDoesNotFixCosmologicalTerm = true := rfl
example : stressEnergySameObjectStillRequired = true := rfl

end Synthesis.JacobsonNullConeRecoveryRegression
