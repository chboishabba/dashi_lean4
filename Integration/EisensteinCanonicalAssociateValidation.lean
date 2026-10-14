import Integration.EisensteinCanonicalAssociateExact

namespace Dashi.EisensteinCanonicalAssociateValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact
open Dashi.EisensteinCanonicalAssociateExact

/-- Every positive norm-n element must be associated to the canonical
representative selected by its split-exponent observer. -/
example
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n) :
    Associated z
      (choiceRepresentative n
        ((norm_representable_iff_inert_even n hn).1 ⟨z, hz⟩)
        (splitChoiceOfRepresentation z n hn hz)) :=
  represented_element_associated_to_choiceRepresentative z n hn hz

end Dashi.EisensteinCanonicalAssociateValidation
