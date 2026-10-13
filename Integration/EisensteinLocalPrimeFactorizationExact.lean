import Integration.EisensteinRepresentationCriterionExact
import Integration.EisensteinSixUnitsExact
import Integration.EisensteinPrimeNormIrreducibleExact

namespace Dashi.EisensteinLocalPrimeFactorizationExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinRamifiedThreeExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinPrimeNormIrreducibleExact

/-- The selected factor over a split rational prime gives the literal
factorization `p = π * star π`. -/
theorem split_prime_factorization
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    (p : EisensteinQA)
      = splitPrimeRepresentative p hp hmod *
          star (splitPrimeRepresentative p hp hmod) := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp [splitPrimeRepresentative_norm]

/-- Both factors in the split factorization are irreducible. -/
theorem split_prime_left_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    Irreducible (splitPrimeRepresentative p hp hmod) :=
  irreducible_of_norm_nat_prime _ p hp
    (splitPrimeRepresentative_norm p hp hmod)

theorem split_prime_right_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    Irreducible (star (splitPrimeRepresentative p hp hmod)) := by
  exact (split_prime_left_irreducible p hp hmod).map
    (starRingAut (R := EisensteinQA))

/-- Exact element-level ramification of `3`; the final factor is the explicit
unit `-ω²`. -/
theorem three_eq_ramified_square_times_unit :
    (3 : EisensteinQA)
      = ramifiedPrime * ramifiedPrime * unitNegOmegaSquared := by
  native_decide

/-- The norm-three ramified factor is irreducible. -/
theorem ramifiedPrime_irreducible : Irreducible ramifiedPrime :=
  irreducible_of_norm_nat_prime ramifiedPrime 3 (by norm_num)
    ramifiedPrime_norm_three

/-- The unit appearing in the ramification factorization is certified. -/
theorem ramifiedUnit_isUnit : IsUnit unitNegOmegaSquared :=
  unitNegOmegaSquared_isUnit

structure EisensteinLocalPrimeFactorizationBoundary where
  splitElementFactorizationPaid : Bool := true
  splitFactorsIrreduciblePaid : Bool := true
  ramifiedElementFactorizationPaid : Bool := true
  ramifiedFactorIrreduciblePaid : Bool := true
  localPrimeSupportClassificationReady : Bool := true
  globalAssociateNormalFormPaid : Bool := false

def canonicalBoundary : EisensteinLocalPrimeFactorizationBoundary := {}

end Dashi.EisensteinLocalPrimeFactorizationExact
