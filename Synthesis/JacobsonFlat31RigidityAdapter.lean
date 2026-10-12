import Synthesis.JacobsonNullConeRecovery
import Synthesis.JacobsonNullConeRigidity

namespace Synthesis.JacobsonFlat31RigidityAdapter

open Synthesis.JacobsonNullConeRecovery
open Synthesis.JacobsonNullConeRigidity

abbrev FlatNullDirection := { v : Vec4 // minkowskiQuad v = 0 }

/-- The generic null-contracted relation instantiated on the concrete flat
3+1 symmetric-tensor carrier. -/
def flatNullRelation
    (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    NullContractedFieldRelation SymTensor4 FlatNullDirection ℝ where
  zero := 0
  defect := T
  nullContraction := fun candidate k => contract candidate k.1
  allNullDirections := fun k => h k.1 k.2

/-- The concrete flat 3+1 theorem supplies the geometric rigidity premise
required by the generic Jacobson null-cone compiler. -/
def flatNullConeRigidity
    (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    NullConeTensorRigidity (flatNullRelation T h) where
  MetricCoefficient := ℝ
  metricMultiple := metricMultiple
  rigidity := by
    intro candidate hcand
    exact nullConeRigidity candidate (fun v hv => hcand ⟨v, hv⟩)

/-- Same-object composition: for the concrete flat 3+1 carrier, the generic
compiler no longer needs an abstract rigidity hypothesis. -/
theorem recoverFlatTensorEquationModuloMetric
    (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    TensorEquationModuloMetric
      (flatNullRelation T h)
      (flatNullConeRigidity T h) :=
  recoverTensorEquationModuloMetric
    (flatNullRelation T h)
    (flatNullConeRigidity T h)

def flat31GenericCompilerInstantiated : Bool := true

def continuumPointwiseIdentificationStillRequired : Bool := true

def physicalStressEnergyIdentificationStillRequired : Bool := true

end Synthesis.JacobsonFlat31RigidityAdapter
