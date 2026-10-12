import Synthesis.JacobsonNullConeRigidity

namespace Synthesis.JacobsonNullConeRigidityRegression

open Synthesis.JacobsonNullConeRigidity

example (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    ∃ λ : ℝ, T = metricMultiple λ :=
  nullConeRigidity T h

example : finiteLorentzianNullConeRigidityOwned = true := rfl
example : continuumFibrewiseTransportStillRequired = true := rfl

end Synthesis.JacobsonNullConeRigidityRegression
