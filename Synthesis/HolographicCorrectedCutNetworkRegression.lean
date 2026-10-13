import Synthesis.HolographicCorrectedCutNetwork

namespace Synthesis.HolographicCorrectedCutNetworkRegression

open Synthesis.HolographicCorrectedCutNetwork

example (k : ℕ) : Fintype.card (CutBond k) = k := cutBond_card k

example (k : ℕ) :
    contractedDensity k =
      Synthesis.HolographicMaxEntangledCutRT.maxEntangledSchmidtDensity k :=
  contractedDensity_eq_correctedSchmidt k

example (k : ℕ) :
    networkEntropy k = geometricCutEntropy k :=
  correctedCutNetworkRT k

example : correctedReplacementNetworkOwned = true := rfl
example : upstreamCopyTreeDoesNotSupplyGeneralKBondCut = true := rfl

end Synthesis.HolographicCorrectedCutNetworkRegression
