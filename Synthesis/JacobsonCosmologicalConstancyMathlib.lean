import Mathlib.Analysis.Calculus.MeanValue

namespace Synthesis.JacobsonCosmologicalConstancyMathlib

open Set

/-- Pinned-Mathlib specialization of the standard zero-Fréchet-derivative
constancy theorem.  This discharges the generic calculus step once the physical
lambda-field is identified with a differentiable scalar function on an open
preconnected domain and its fderiv is proved zero. -/
theorem lambda_constant_on_open_preconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (f : E → ℝ)
    (hs : IsOpen s) (hc : IsPreconnected s)
    (hf : DifferentiableOn ℝ f s)
    (hz : s.EqOn (fderiv ℝ f) 0) :
    ∃ Λ : ℝ, ∀ x ∈ s, f x = Λ :=
  hs.exists_is_const_of_fderiv_eq_zero hc hf hz

/-- Status boundary. -/
def mathlibZeroDerivativeConstancyOwned : Bool := true

def physicalLambdaFDerivZeroStillRequired : Bool := true

def physicalOpenPreconnectedDomainStillRequired : Bool := true

def physicalDifferentiabilityStillRequired : Bool := true

end Synthesis.JacobsonCosmologicalConstancyMathlib
