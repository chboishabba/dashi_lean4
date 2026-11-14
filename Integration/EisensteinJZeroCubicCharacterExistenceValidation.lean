import Integration.EisensteinJZeroCubicCharacterExistenceExact

namespace Integration.EisensteinJZeroCubicCharacterExistenceValidation

open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCubicCharacterExistenceExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = 3 :=
  splitPrime_exists_orderThreeCharacter p hmod

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : MulChar F ℂ) (hψ : orderOf ψ = 3) :
    ψ (-1) = 1 :=
  orderThreeCharacter_negOne ψ hψ

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (cert : CubicCharacterCertificate F)
    (horder : orderOf cert.character = 3) :
    cubicJacobiTrace cert =
      -(jacobiSum cert.character quadraticCharComplex
        + jacobiSum (cert.character * cert.character) quadraticCharComplex) :=
  cubicJacobiTrace_eq_neg_unweightedPair cert horder

end Integration.EisensteinJZeroCubicCharacterExistenceValidation
