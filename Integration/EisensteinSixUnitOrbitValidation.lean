import Integration.EisensteinSixUnitOrbitExact

namespace Dashi.EisensteinSixUnitOrbitValidation

open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinSixUnitOrbitExact

example
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype.card (PositiveNormFiber n hn H)
      = 6 * ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) :=
  card_positiveNormFiber n hn H

end Dashi.EisensteinSixUnitOrbitValidation
