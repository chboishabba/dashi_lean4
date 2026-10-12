import Synthesis.JacobsonFlat31RigidityAdapter

namespace Synthesis.JacobsonFlat31RigidityAdapterRegression

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonFlat31RigidityAdapter

example (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    ∃ λ : ℝ, T = metricMultiple λ := by
  exact nullConeRigidity T h

example (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    Synthesis.JacobsonNullConeRecovery.TensorEquationModuloMetric
      (flatNullRelation T h)
      (flatNullConeRigidity T h) :=
  recoverFlatTensorEquationModuloMetric T h

example : flat31GenericCompilerInstantiated = true := rfl

end Synthesis.JacobsonFlat31RigidityAdapterRegression
