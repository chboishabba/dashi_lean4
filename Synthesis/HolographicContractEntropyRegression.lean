import Synthesis.HolographicContractEntropy

namespace Synthesis.HolographicContractEntropyRegression

open Synthesis.HolographicContractEntropy

example (n : ℕ) :
    uniformDiagonalVonNeumannEntropy n = (n : ℝ) * Real.log 2 :=
  fullContractVonNeumannEntropyIsNLogTwo n

example (n : ℕ) :
    fullDepthTreeEntropy n = uniformDiagonalVonNeumannEntropy n :=
  fullStateEntropyMatchesTreeEntropyAtFullDepth n

example (k r : ℕ) :
    factorizedMarginalEigenvalue k r = uniformEigenvalue k :=
  uniformFactorizedMarginalEigenvalue k r

example (k r : ℕ) :
    factorizedReducedVonNeumannEntropy k r = (k : ℝ) * Real.log 2 :=
  depthKReducedEntropyIsKLogTwo k r

example : factorizedSubsystemRTClosed = true := rfl
example : subsystemReducedDensityMatrixStillRequired = true := rfl
example : upstreamZModSubsystemFactorizationStillRequired = true := rfl
example : fullContractDoesNotByItselfProveDepthKSubsystemEntropy = true := rfl

end Synthesis.HolographicContractEntropyRegression
