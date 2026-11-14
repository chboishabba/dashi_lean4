import Integration.EisensteinDivisorCharacterProductExact

namespace Dashi.EisensteinDivisorCharacterProductValidation

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinDivisorCharacterProductExact

example (n : Nat) (hn : n ≠ 0) :
    chiMinus3DivisorSum n
      = ∏ p ∈ n.primeFactors,
          chiMinus3PrimePowerFactor p (n.factorization p) :=
  chiMinus3DivisorSum_factorization n hn

example (n : Nat) (hn : 0 < n) :
    0 < chiMinus3DivisorSum n ↔
      Dashi.EisensteinRepresentationCriterionExact.InertEvenCondition n :=
  chiMinus3DivisorSum_pos_iff_inert_even n hn

example (n : Nat) (hn : 0 < n) :
    signedEisensteinDivisorShellCount n = 6 * chiMinus3DivisorSum n :=
  signedShell_eq_six_mul_character_sum n hn.ne'

end Dashi.EisensteinDivisorCharacterProductValidation
