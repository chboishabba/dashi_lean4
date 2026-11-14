import Synthesis.HolographicMaxEntangledCutRT

namespace Synthesis.HolographicMaxEntangledCutRTRegression

open Synthesis.HolographicMaxEntangledCutRT

example (k : ℕ) (i j : Fin (cutDimension k)) :
    reducedDensityA k i j = if i = j then cutWeight k else 0 :=
  reducedDensityA_eq_uniformDiagonal k i j

example (k : ℕ) :
    reducedVonNeumannEntropy k = (k : ℝ) * Real.log 2 :=
  reducedEntropy_eq_kLogTwo k

example (k : ℕ) :
    correctedCutEntropy k = reducedVonNeumannEntropy k :=
  correctedRTSameObjectEntropy k

example : upstreamStateIdentificationStillRequired = true := rfl
example : minimalCutCarrierIdentificationStillRequired = true := rfl

end Synthesis.HolographicMaxEntangledCutRTRegression
