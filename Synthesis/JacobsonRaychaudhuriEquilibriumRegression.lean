import Synthesis.JacobsonRaychaudhuriEquilibrium

namespace Synthesis.JacobsonRaychaudhuriEquilibriumRegression

open Synthesis.JacobsonRaychaudhuriEquilibrium
open Synthesis.JacobsonClausiusNullAlgebra

example (Rkk : ℝ) :
    nullRaychaudhuriRHS 0 0 0 Rkk = -Rkk :=
  nullRaychaudhuri_at_local_equilibrium Rkk

example (Rkk : ℝ) :
    factoredLinearizedAreaVariation Rkk = areaVariationIntegrand Rkk :=
  factoredLinearizedAreaVariation_eq_clausius Rkk

example : equilibriumRaychaudhuriAlgebraOwned = true := rfl
example : physicalNullCongruenceEquationStillRequired = true := rfl
example : localEquilibriumIdentificationStillRequired = true := rfl

end Synthesis.JacobsonRaychaudhuriEquilibriumRegression
