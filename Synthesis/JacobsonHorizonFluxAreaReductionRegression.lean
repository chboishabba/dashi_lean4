import Synthesis.JacobsonHorizonFluxAreaReduction

namespace Synthesis.JacobsonHorizonFluxAreaReductionRegression

open Synthesis.JacobsonHorizonFluxAreaReduction

example (κ λ Tkk : ℝ) :
    horizonHeatFluxDensity κ λ Tkk
      = λ * Synthesis.JacobsonClausiusNullAlgebra.heatFluxIntegrand κ Tkk :=
  horizonHeatFluxDensity_eq_factored κ λ Tkk

example (λ Rkk : ℝ) :
    linearizedAreaDensity λ Rkk
      = λ * Synthesis.JacobsonClausiusNullAlgebra.areaVariationIntegrand Rkk :=
  linearizedAreaDensity_eq_factored λ Rkk

example : horizonFluxReductionOwned = true := rfl
example : linearizedAreaReductionOwned = true := rfl
example : physicalBoostKillingIdentificationStillRequired = true := rfl
example : physicalHorizonMeasureStillRequired = true := rfl
example : continuumHigherOrderControlStillRequired = true := rfl

end Synthesis.JacobsonHorizonFluxAreaReductionRegression
