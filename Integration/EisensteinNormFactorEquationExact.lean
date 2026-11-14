import Integration.EisensteinPrimeClassificationExact
import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

namespace Dashi.EisensteinNormFactorEquationExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact

------------------------------------------------------------------------
-- The same-object UFD identity behind the representation formula.
------------------------------------------------------------------------

/-- The embedded integer norm is literally the product of the element and its
quadratic conjugate. -/
theorem intCast_norm_eq_mul_star (z : EisensteinQA) :
    (QuadraticAlgebra.norm z : EisensteinQA) = z * star z := by
  simpa using QuadraticAlgebra.algebraMap_norm_eq_mul_star z

/-- At the unique-factorization level, the norm factorization is the sum of the
factorizations of an element and its conjugate. -/
theorem norm_factors_eq_element_add_conjugate (z : EisensteinQA) :
    (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
      = (Associates.mk z).factors + (Associates.mk (star z)).factors := by
  calc
    (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
        = (Associates.mk (z * star z)).factors := by
            rw [intCast_norm_eq_mul_star]
    _ = (Associates.mk z * Associates.mk (star z)).factors := by
          rw [Associates.mk_mul_mk]
    _ = (Associates.mk z).factors + (Associates.mk (star z)).factors := by
          rw [Associates.factors_mul]

/-- The same identity after replacing the norm by a concrete positive natural
number. -/
theorem nat_norm_factors_eq_element_add_conjugate
    (z : EisensteinQA) (n : Nat)
    (hz : QuadraticAlgebra.norm z = n) :
    (Associates.mk (n : EisensteinQA)).factors
      = (Associates.mk z).factors + (Associates.mk (star z)).factors := by
  rw [← hz]
  exact norm_factors_eq_element_add_conjugate z

/-- Every irreducible-associate multiplicity in the norm is the sum of its
multiplicities in `z` and `star z`. -/
theorem norm_prime_count_eq_add
    (z : EisensteinQA) (hz : z ≠ 0)
    (q : Associates EisensteinQA) (hq : Irreducible q) :
    Associates.count q
        (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
      = Associates.count q (Associates.mk z).factors
        + Associates.count q (Associates.mk (star z)).factors := by
  classical
  have hzmk : Associates.mk z ≠ 0 := Associates.mk_ne_zero.mpr hz
  have hzstar : star z ≠ 0 := by
    intro h
    apply hz
    apply star_involutive.injective
    simpa using h
  have hzstarmk : Associates.mk (star z) ≠ 0 :=
    Associates.mk_ne_zero.mpr hzstar
  calc
    Associates.count q
        (Associates.mk (QuadraticAlgebra.norm z : EisensteinQA)).factors
      = Associates.count q
          (Associates.mk z * Associates.mk (star z)).factors := by
          rw [norm_factors_eq_element_add_conjugate, Associates.factors_mul]
    _ = Associates.count q (Associates.mk z).factors
        + Associates.count q (Associates.mk (star z)).factors :=
          Associates.count_mul hzmk hzstarmk hq

/-- Natural-norm version consumed by the shell-count classifier. -/
theorem nat_norm_prime_count_eq_add
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n)
    (q : Associates EisensteinQA) (hq : Irreducible q) :
    Associates.count q (Associates.mk (n : EisensteinQA)).factors
      = Associates.count q (Associates.mk z).factors
        + Associates.count q (Associates.mk (star z)).factors := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
    omega
  simpa [hz] using norm_prime_count_eq_add z hz0 q hq

structure EisensteinNormFactorEquationBoundary where
  normAsElementTimesConjugatePaid : Bool := true
  factorMultisetEquationPaid : Bool := true
  irreducibleMultiplicityEquationPaid : Bool := true
  inertParityConsumerReady : Bool := true
  splitExponentDistributionConsumerReady : Bool := true
  globalCardinalityFormulaPaid : Bool := false

def canonicalBoundary : EisensteinNormFactorEquationBoundary := {}

end Dashi.EisensteinNormFactorEquationExact
