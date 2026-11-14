import Synthesis.JacobsonLocalFrameFieldCompiler

namespace Synthesis.JacobsonLocalFrameFieldCompilerRegression

open Synthesis.JacobsonLocalFrameFieldCompiler

example {Point : Type*} (D : LocalFrameJacobsonData Point) (p : Point) :
    ∃ phi : ℝ,
      Synthesis.JacobsonFlat31EinsteinCompiler.tensorSubScaled
        (D.ricci p) (8 * Real.pi * D.G) (D.stress p)
      = Synthesis.JacobsonNullConeRigidity.metricMultiple phi :=
  pointwiseRicciStressMetricAmbiguity D p

example {Point : Type*} (D : LocalFrameJacobsonData Point) (p : Point) :
    Synthesis.JacobsonFlat31EinsteinCompiler.tensorSubScaled
      (D.ricci p) (8 * Real.pi * D.G) (D.stress p)
      = Synthesis.JacobsonNullConeRigidity.metricMultiple
          (recoveredPhiField D p) :=
  recoveredPhiField_spec D p

example : localFrameFieldCompilerOwned = true := rfl
example : physicalLocalLorentzFrameIdentificationStillRequired = true := rfl
example : physicalClausiusSameObjectReceiptStillRequired = true := rfl
example : recoveredPhiRegularityStillRequired = true := rfl

end Synthesis.JacobsonLocalFrameFieldCompilerRegression
