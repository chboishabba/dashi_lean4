import Mathlib.Analysis.Calculus.MeanValue
import Synthesis.JacobsonLocalFrameEinsteinLambda
import Synthesis.JacobsonCosmologicalConstancyMathlib

namespace Synthesis.JacobsonRecoveredLambdaConstancy

open Set
open Synthesis.JacobsonLocalFrameFieldCompiler
open Synthesis.JacobsonLocalFrameEinsteinLambda
open Synthesis.JacobsonCosmologicalConstancyMathlib

/-- Same-object regularity/constancy package for the **exact** Lambda field
constructed by `JacobsonLocalFrameEinsteinLambda`.

This removes the previous identity seam between "the Lambda from the Jacobson
compiler" and "the scalar function fed to Mathlib's zero-derivative constancy
theorem".  The physical model still has to prove differentiability and zero
Fréchet derivative on its selected spacetime domain. -/
structure RecoveredLambdaConstancyData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : LocalFrameJacobsonData E) where
  domain : Set E
  domainOpen : IsOpen domain
  domainPreconnected : IsPreconnected domain
  lambdaDifferentiable : DifferentiableOn ℝ (recoveredLambdaField D) domain
  lambdaFDerivZero : domain.EqOn (fderiv ℝ (recoveredLambdaField D)) 0

/-- Direct specialization of the pinned Mathlib theorem to the very same
`recoveredLambdaField` produced by the point-indexed Jacobson compiler. -/
theorem recoveredLambda_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : LocalFrameJacobsonData E}
    (C : RecoveredLambdaConstancyData D) :
    ∃ Λ : ℝ, ∀ x ∈ C.domain, recoveredLambdaField D x = Λ := by
  exact lambda_constant_on_open_preconnected
    C.domain
    (recoveredLambdaField D)
    C.domainOpen
    C.domainPreconnected
    C.lambdaDifferentiable
    C.lambdaFDerivZero

/-- Bundled same-object constant-Lambda receipt. -/
structure RecoveredLambdaConstantReceipt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : LocalFrameJacobsonData E}
    (C : RecoveredLambdaConstancyData D) where
  Lambda : ℝ
  lambdaFieldConstant : ∀ x ∈ C.domain, recoveredLambdaField D x = Lambda

/-- Canonical receipt compiled from the exact recovered field and the supplied
regularity/zero-derivative premises. -/
noncomputable def canonicalRecoveredLambdaConstantReceipt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : LocalFrameJacobsonData E}
    (C : RecoveredLambdaConstancyData D) :
    RecoveredLambdaConstantReceipt C := by
  rcases recoveredLambda_constant C with ⟨Λ, hΛ⟩
  exact ⟨Λ, hΛ⟩

/-- Status boundary. -/
def recoveredLambdaSameObjectConstancyCompilerOwned : Bool := true

def separateLambdaIdentityWeldNoLongerRequired : Bool := true

def physicalBianchiToFDerivZeroStillRequired : Bool := true

def physicalStressConservationStillRequired : Bool := true

def physicalDifferentiabilityStillRequired : Bool := true

def physicalDomainChoiceStillRequired : Bool := true

def continuumSolutionAttachmentStillRequired : Bool := true

end Synthesis.JacobsonRecoveredLambdaConstancy
