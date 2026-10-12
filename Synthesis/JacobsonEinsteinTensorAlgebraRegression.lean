import Synthesis.JacobsonEinsteinTensorAlgebra

namespace Synthesis.JacobsonEinsteinTensorAlgebraRegression

open Synthesis.JacobsonEinsteinTensorAlgebra

example {ι : Type*} (D : RicciStressMetricData ι) (a b : ι) :
    einsteinTensor D a b + cosmologicalCoefficient D * D.metric a b
      = D.coupling * D.stress a b :=
  einsteinEquationPointwise D a b

example : einsteinTensorPointwiseAlgebraOwned = true := rfl
example : cosmologicalConstancyDifferentialReceiptStillRequired = true := rfl
example : contractedBianchiPhysicalReceiptStillRequired = true := rfl

end Synthesis.JacobsonEinsteinTensorAlgebraRegression
