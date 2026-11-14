import Synthesis.JacobsonBianchiCosmologicalConstancy

namespace Synthesis.JacobsonBianchiCosmologicalConstancyRegression

open Synthesis.JacobsonBianchiCosmologicalConstancy

example {Point Index : Type*} (D : BianchiConstancyData Point Index)
    (p : Point) (ν : Index) :
    D.gradScalarCurvature p ν / 2 - D.gradPhi p ν = 0 :=
  lambdaGradientZero D p ν

example : bianchiLambdaGradientCompilerOwned = true := rfl
example : zeroGradientToGlobalConstantStillRequired = true := rfl
example : physicalBianchiStressReceiptsStillRequired = true := rfl

end Synthesis.JacobsonBianchiCosmologicalConstancyRegression
