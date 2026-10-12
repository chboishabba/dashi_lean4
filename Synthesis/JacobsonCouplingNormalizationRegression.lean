import Synthesis.JacobsonCouplingNormalization

namespace Synthesis.JacobsonCouplingNormalizationRegression

open Synthesis.JacobsonCouplingNormalization

example (ℏ G : ℝ) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) :
    jacobsonNullCoupling ℏ (bekensteinHawkingAreaDensity ℏ G)
      = 8 * Real.pi * G :=
  jacobsonCoupling_eq_eightPiG ℏ G hℏ hG

example : jacobsonCouplingAlgebraOwned = true := rfl
example : unruhNormalizationPhysicalReceiptStillRequired = true := rfl
example : entropyAreaPhysicalReceiptStillRequired = true := rfl

end Synthesis.JacobsonCouplingNormalizationRegression
