import Synthesis.JacobsonUnruhNormalization

namespace Synthesis.JacobsonUnruhNormalizationRegression

open Synthesis.JacobsonUnruhNormalization
open Synthesis.JacobsonCouplingNormalization

example : wedgeBoostKMSPeriod = 2 * Real.pi := rfl

example (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) :
    (properTimeInverseTemperature ℏ κ)⁻¹ = unruhTemperature ℏ κ :=
  inverseProperTimeBeta_eq_unruhTemperature ℏ κ hℏ hκ

example : boostKMSNormalizationOwned = true := rfl
example : physicalBisognanoWichmannStillRequired = true := rfl
example : accelerationProperTimeIdentificationStillRequired = true := rfl

end Synthesis.JacobsonUnruhNormalizationRegression
