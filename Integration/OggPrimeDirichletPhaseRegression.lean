import Integration.OggPrimeDirichletPhase

namespace Integration.OggPrimeDirichletPhaseRegression

open Integration.OggPrimeFourierWinding
open Integration.OggPrimeDirichletPhase

example : analysisPrimes.card = 20 := analysisPrimes_card

example (p : ℕ) : dirichletRotor 0 p = 1 := dirichletRotor_zero p

example (t : ℝ) (p : ℕ) :
    dirichletRotor (-t) p = Complex.conj (dirichletRotor t p) :=
  dirichletRotor_neg_eq_conj t p

example : dirichletContrast 0 = 0 := dirichletContrast_zero

example : multiplicativePhaseIdentifiedWithAdditivePrimeWinding = false := rfl
example : exhaustiveRelabellingRankClaimedExactPValue = false := rfl
example : heldOutMonsterSpecificAnomalyClaimed = false := rfl
example : riemannHypothesisEvidenceClaimed = false := rfl

end Integration.OggPrimeDirichletPhaseRegression
