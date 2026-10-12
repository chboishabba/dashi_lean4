import Synthesis.HolographicUnbalancedCorrectedRT

namespace Synthesis.HolographicUnbalancedCorrectedRTRegression

open Synthesis.HolographicUnbalancedCorrectedRT

example (k r : ℕ) (hkr : k ≤ r)
    (i j : Fin (2 ^ k)) :
    reducedDensityAUnbalanced k r hkr i j =
      if i = j then Synthesis.HolographicMaxEntangledCutRT.cutWeight k else 0 :=
  reducedDensityAUnbalanced_eq_uniformDiagonal k r hkr i j

example (k r : ℕ) (hkr : k ≤ r) :
    correctedUnbalancedReducedEntropy k r hkr =
      Synthesis.HolographicMaxEntangledCutRT.correctedCutEntropy k :=
  correctedUnbalancedRTEntropy k r hkr

example : correctedUnbalancedRTForAdequateComplementOwned = true := rfl
example : upstreamTreeContractionStillRequired = true := rfl
example : geometricSubtreeIdentificationStillRequired = true := rfl

end Synthesis.HolographicUnbalancedCorrectedRTRegression
