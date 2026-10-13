import Integration.EisensteinRepresentationCriterionExact

namespace Dashi.EisensteinRepresentationCriterionValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact

example (n : Nat) (hn : 0 < n) :
    (∃ z : EisensteinQA, QuadraticAlgebra.norm z = n)
      ↔ InertEvenCondition n :=
  norm_representable_iff_inert_even n hn

end Dashi.EisensteinRepresentationCriterionValidation
