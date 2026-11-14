import Integration.EisensteinAssociateClassCountExact

namespace Dashi.EisensteinAssociateClassCountValidation

open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinAssociateClassCountExact

example
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype.card (NormAssociateClass n hn H)
      = ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) :=
  card_normAssociateClass n hn H

end Dashi.EisensteinAssociateClassCountValidation
