import Integration.EisensteinNormFactorEquationExact

namespace Dashi.EisensteinNormFactorEquationValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinNormFactorEquationExact

/-- The decisive UFD same-object identity. -/
example (z : EisensteinQA) :
    (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
      = (Associates.mk z).factors + (Associates.mk (star z)).factors :=
  norm_factors_eq_element_add_conjugate z

/-- Prime multiplicities therefore add between a point and its conjugate. -/
example (z : EisensteinQA) (hz : z ≠ 0)
    (q : Associates EisensteinQA) (hq : Irreducible q) :
    Associates.count q
        (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
      = Associates.count q (Associates.mk z).factors
        + Associates.count q (Associates.mk (star z)).factors :=
  norm_prime_count_eq_add z hz q hq

end Dashi.EisensteinNormFactorEquationValidation
