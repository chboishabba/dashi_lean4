import Synthesis.JacobsonRecoveredLambdaConstancy

namespace Synthesis.JacobsonRecoveredLambdaConstancyRegression

open Synthesis.JacobsonRecoveredLambdaConstancy
open Synthesis.JacobsonLocalFrameFieldCompiler

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : LocalFrameJacobsonData E)
    (C : RecoveredLambdaConstancyData D) :
    ∃ Λ : ℝ, ∀ x ∈ C.domain,
      Synthesis.JacobsonLocalFrameEinsteinLambda.recoveredLambdaField D x = Λ :=
  recoveredLambda_constant C

example : recoveredLambdaSameObjectConstancyCompilerOwned = true := rfl
example : physicalBianchiToFDerivZeroStillRequired = true := rfl
example : physicalDifferentiabilityStillRequired = true := rfl
example : physicalDomainChoiceStillRequired = true := rfl

end Synthesis.JacobsonRecoveredLambdaConstancyRegression
