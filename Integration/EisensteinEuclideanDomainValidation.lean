import Integration.EisensteinEuclideanDomainExact

namespace Dashi.EisensteinEuclideanDomainValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact

/-- The standard Eisenstein quadratic-algebra carrier must now expose a literal
Euclidean-domain instance, not merely a norm and multiplication law. -/
example : EuclideanDomain EisensteinQA := inferInstance

/-- Hence the factorization machinery needed by the representation theorem is
available on the same carrier. -/
example : UniqueFactorizationMonoid EisensteinQA := inferInstance

/-- Euclidean remainder strictly lowers the Eisenstein norm away from zero. -/
example (x : EisensteinQA) {y : EisensteinQA} (hy : y ≠ 0) :
    QuadraticAlgebra.norm (x % y) < QuadraticAlgebra.norm y :=
  norm_mod_lt x hy

/-- Concrete smoke test: reduction modulo the ramified norm-three element
actually produces a strictly smaller norm. -/
example :
    QuadraticAlgebra.norm
      (asQuadraticAlgebra 7 2 % asQuadraticAlgebra 1 (-1))
      < 3 := by
  native_decide

end Dashi.EisensteinEuclideanDomainValidation
