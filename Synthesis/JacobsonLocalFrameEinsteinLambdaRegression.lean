import Synthesis.JacobsonLocalFrameEinsteinLambda

namespace Synthesis.JacobsonLocalFrameEinsteinLambdaRegression

open Synthesis.JacobsonLocalFrameEinsteinLambda
open Synthesis.JacobsonLocalFrameFieldCompiler

example (ricci stress : Synthesis.JacobsonNullConeRigidity.SymTensor4)
    (C phi : ℝ)
    (h : Synthesis.JacobsonFlat31EinsteinCompiler.tensorSubScaled ricci C stress =
      Synthesis.JacobsonNullConeRigidity.metricMultiple phi) :
    einsteinPlusLambda ricci (scalarCurvatureFlat ricci / 2 - phi)
      = scaledTensor C stress :=
  einsteinLambda_of_metricAmbiguity ricci stress C phi h

example {Point : Type*} (D : LocalFrameJacobsonData Point) (p : Point) :
    einsteinPlusLambda (D.ricci p) (recoveredLambdaField D p)
      = scaledTensor (8 * Real.pi * D.G) (D.stress p) :=
  recoveredLambdaField_spec D p

example : localFrameEinsteinLambdaCompilerOwned = true := rfl
example : bianchiStressConservationStillRequired = true := rfl
example : recoveredLambdaRegularityStillRequired = true := rfl

end Synthesis.JacobsonLocalFrameEinsteinLambdaRegression
