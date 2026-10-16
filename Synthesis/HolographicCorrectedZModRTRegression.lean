import Synthesis.HolographicCorrectedZModRT

namespace Synthesis.HolographicCorrectedZModRTRegression

open Synthesis.HolographicCorrectedZModRT

example (k : ℕ)
    (x y : Fin (2 ^ k) × Fin (2 ^ k)) :
    correctedZModDensity k
      ((balancedZModFactorEquiv k).symm x)
      ((balancedZModFactorEquiv k).symm y)
      = Synthesis.HolographicMaxEntangledCutRT.maxEntangledSchmidtDensity k x y :=
  correctedZModDensity_pullback k x y

example (k : ℕ) :
    correctedZModReducedEntropy k =
      Synthesis.HolographicMaxEntangledCutRT.correctedCutEntropy k :=
  correctedZModRTEntropy k

example : correctedEntangledStateOnZModCarrierOwned = true := rfl
example : upstreamTreeContractionStillMustBeReplacedOrProvedEquivalent = true := rfl
example : geometricSubtreeIdentificationStillRequired = true := rfl

end Synthesis.HolographicCorrectedZModRTRegression
