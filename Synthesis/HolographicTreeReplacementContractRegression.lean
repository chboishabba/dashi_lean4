import Synthesis.HolographicTreeReplacementContract

namespace Synthesis.HolographicTreeReplacementContractRegression

open Synthesis.HolographicTreeReplacementContract

example (k : ℕ) (R : CorrectedTreeReplacement k) :
    R.actualEntropy = R.actualCutEntropy := correctedTreeReplacementRT R

example : sourceReplacementContractOwned = true := rfl
example : currentUpstreamDefinitionsDoNotInstantiateContract = true := rfl
example : noFurtherRTEntropyAlgebraRequired = true := rfl

end Synthesis.HolographicTreeReplacementContractRegression
