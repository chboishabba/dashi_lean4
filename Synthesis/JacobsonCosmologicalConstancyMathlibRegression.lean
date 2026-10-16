import Synthesis.JacobsonCosmologicalConstancyMathlib

namespace Synthesis.JacobsonCosmologicalConstancyMathlibRegression

open Set
open Synthesis.JacobsonCosmologicalConstancyMathlib

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (f : E → ℝ)
    (hs : IsOpen s) (hc : IsPreconnected s)
    (hf : DifferentiableOn ℝ f s)
    (hz : s.EqOn (fderiv ℝ f) 0) :
    ∃ Λ : ℝ, ∀ x ∈ s, f x = Λ :=
  lambda_constant_on_open_preconnected s f hs hc hf hz

example : mathlibZeroDerivativeConstancyOwned = true := rfl
example : physicalLambdaFDerivZeroStillRequired = true := rfl

end Synthesis.JacobsonCosmologicalConstancyMathlibRegression
