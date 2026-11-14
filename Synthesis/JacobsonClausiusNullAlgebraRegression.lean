import Synthesis.JacobsonClausiusNullAlgebra

namespace Synthesis.JacobsonClausiusNullAlgebraRegression

open Synthesis.JacobsonCouplingNormalization
open Synthesis.JacobsonClausiusNullAlgebra

example (ℏ κ η Tkk Rkk : ℝ) (hκ : κ ≠ 0)
    (hC : heatFluxIntegrand κ Tkk =
      unruhTemperature ℏ κ * entropyVariationIntegrand η Rkk) :
    Tkk = (ℏ * η / (2 * Real.pi)) * Rkk :=
  nullRelation_of_clausius ℏ κ η Tkk Rkk hκ hC

example (ℏ κ G Tkk Rkk : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hG : G ≠ 0)
    (hC : heatFluxIntegrand κ Tkk =
      unruhTemperature ℏ κ *
        entropyVariationIntegrand (bekensteinHawkingAreaDensity ℏ G) Rkk) :
    Rkk = 8 * Real.pi * G * Tkk :=
  einsteinNullRelation_of_clausius_bekensteinHawking
    ℏ κ G Tkk Rkk hℏ hκ hG hC

example : clausiusNullAlgebraOwned = true := rfl
example : geometricHeatFluxReceiptStillRequired = true := rfl
example : raychaudhuriAreaVariationReceiptStillRequired = true := rfl

end Synthesis.JacobsonClausiusNullAlgebraRegression
