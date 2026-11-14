import Synthesis.JacobsonFibrewiseFrameAssembly

namespace Synthesis.JacobsonFibrewiseFrameAssemblyRegression

open Synthesis.JacobsonNullConeRigidityTransport
open Synthesis.JacobsonFibrewiseFrameAssembly

universe u v w

example {Point : Type u} (D : FibrewiseLorentzData Point) (p : Point) :
    D.defect p = (D.frame p).metricMultipleV (recoveredPhi D p) :=
  defect_eq_metricMultiple_recoveredPhi D p

example : fibrewisePointwiseAssemblyOwned = true := rfl
example : physicalFrameFieldConstructionStillRequired = true := rfl
example : recoveredPhiSmoothnessStillRequired = true := rfl

end Synthesis.JacobsonFibrewiseFrameAssemblyRegression
