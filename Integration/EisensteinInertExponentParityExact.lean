import Integration.EisensteinRationalPrimeFactorCountExact
import Integration.EisensteinNormFactorEquationExact
import Integration.EisensteinConjugateFactorCountExact

namespace Dashi.EisensteinInertExponentParityExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinPrimeClassificationExact
open Dashi.EisensteinNormFactorEquationExact
open Dashi.EisensteinConjugateFactorCountExact
open Dashi.EisensteinRationalPrimeFactorCountExact

/-- Any positive norm represented by an Eisenstein integer has even valuation
at every inert rational prime `p ≡ 2 (mod 3)`.  This is the global form of the
local inert-prime obstruction. -/
theorem represented_norm_has_even_inert_exponent
    (z : EisensteinQA) (n p : Nat)
    (hn : 0 < n) (hz : QuadraticAlgebra.norm z = n)
    (hp : p.Prime) (hmod : p % 3 = 2) :
    Even (n.factorization p) := by
  classical
  let q : EisensteinQA := (p : EisensteinQA)
  let qA : Associates EisensteinQA := Associates.mk q
  have hq : Irreducible q := by
    simpa [q] using inert_prime_irreducible p hp hmod
  have hqA : Irreducible qA := Associates.irreducible_mk.mpr hq
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
    omega
  have hnormCount :=
    nat_norm_prime_count_eq_add z n hn hz qA hqA
  have hleft :
      Associates.count qA (Associates.mk (n : EisensteinQA)).factors
        = n.factorization p := by
    simpa [q, qA] using
      rational_prime_count_eq_factorization n p hn hp hq
  have hstar :
      Associates.count qA (Associates.mk (star z)).factors
        = Associates.count qA (Associates.mk z).factors := by
    have htransport := conjugate_prime_count z hz0 q hq
    simpa [q, qA] using htransport
  rw [hleft, hstar] at hnormCount
  refine ⟨Associates.count qA (Associates.mk z).factors, ?_⟩
  omega

structure EisensteinInertExponentParityBoundary where
  localInertObstructionPaid : Bool := true
  ufdCountNatFactorizationWeldPaid : Bool := true
  conjugationFixesRationalPrimeCountPaid : Bool := true
  representedNormForcesEvenInertExponent : Bool := true
  converseConstructionPaid : Bool := false
  globalCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinInertExponentParityBoundary := {}

end Dashi.EisensteinInertExponentParityExact
