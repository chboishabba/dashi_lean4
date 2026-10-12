import Synthesis.HolographicContractEntropy

namespace Synthesis.HolographicContractEntropyRegression

open Synthesis.HolographicContractEntropy

example (n : ℕ) :
    uniformDiagonalVonNeumannEntropy n = (n : ℝ) * Real.log 2 :=
  fullContractVonNeumannEntropyIsNLogTwo n

example (n : ℕ) :
    fullDepthTreeEntropy n = uniformDiagonalVonNeumannEntropy n :=
  fullStateEntropyMatchesTreeEntropyAtFullDepth n

example : subsystemReducedDensityMatrixStillRequired = true := rfl
example : fullContractDoesNotByItselfProveDepthKSubsystemEntropy = true := rfl

end Synthesis.HolographicContractEntropyRegression
