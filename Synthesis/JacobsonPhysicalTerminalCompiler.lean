import Mathlib
import Synthesis.JacobsonRecoveredLambdaConstancy

namespace Synthesis.JacobsonPhysicalTerminalCompiler

open Set
open Synthesis.JacobsonLocalFrameFieldCompiler
open Synthesis.JacobsonLocalFrameEinsteinLambda
open Synthesis.JacobsonRecoveredLambdaConstancy

/-- Terminal receipt on the selected domain.

At this point all remaining information is carried by one `LocalFrameJacobsonData`
object and one regularity/zero-derivative receipt for the exact Lambda field
constructed from it.  The result uses the same Ricci field, stress field,
Newton constant and recovered cosmological coefficient throughout. -/
structure TerminalEinsteinReceipt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : LocalFrameJacobsonData E)
    (C : RecoveredLambdaConstancyData D) where
  Lambda : ℝ
  lambdaConstant : ∀ x ∈ C.domain, recoveredLambdaField D x = Lambda
  einsteinEquation : ∀ x ∈ C.domain,
    einsteinPlusLambda (D.ricci x) Lambda
      = scaledTensor (8 * Real.pi * D.G) (D.stress x)

/-- Once the declared Jacobson authority/model data and the regularity/
zero-derivative data for its exact recovered Lambda field are supplied, the
constant-Lambda Einstein equation follows on that selected domain. -/
noncomputable def compileTerminalEinsteinReceipt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : LocalFrameJacobsonData E)
    (C : RecoveredLambdaConstancyData D) :
    TerminalEinsteinReceipt D C := by
  rcases recoveredLambda_constant C with ⟨Λ, hΛ⟩
  refine {
    Lambda := Λ
    lambdaConstant := hΛ
    einsteinEquation := ?_
  }
  intro x hx
  have hEq := recoveredLambdaField_spec D x
  have hSame := hΛ x hx
  rw [hSame] at hEq
  exact hEq

/-- Existential form convenient for downstream continuum/empirical consumers. -/
theorem terminalEinsteinEquation_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : LocalFrameJacobsonData E)
    (C : RecoveredLambdaConstancyData D) :
    ∃ Λ : ℝ,
      (∀ x ∈ C.domain, recoveredLambdaField D x = Λ) ∧
      (∀ x ∈ C.domain,
        einsteinPlusLambda (D.ricci x) Λ
          = scaledTensor (8 * Real.pi * D.G) (D.stress x)) := by
  let R := compileTerminalEinsteinReceipt D C
  exact ⟨R.Lambda, R.lambdaConstant, R.einsteinEquation⟩

/-- Formal max-cut status. There is no further scalar/tensor/constancy algebra
between the declared authority/model inputs and the constant-Lambda Einstein
equation on the selected domain. -/
def terminalConditionalEinsteinCompilerOwned : Bool := true

def noFurtherInternalJacobsonAlgebraDebt : Bool := true

/-- Terminal classification. The remaining activity is not an untyped bridge:
it is explicit source/model or authority-assumption instantiation, followed by
empirical calibration where a physical claim is desired. -/
def authorityInstantiationStillExternal : Bool := true

def sourceModelInstantiationStillExternal : Bool := true

def noUnclassifiedPhysicalWeldDebt : Bool := true

def empiricalValidationStillRequired : Bool := true

end Synthesis.JacobsonPhysicalTerminalCompiler
