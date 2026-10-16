import Integration.EisensteinLocalPrimeFactorizationExact
import Integration.EisensteinPrimeClassificationExact
import Mathlib.Algebra.BigOperators.Associated

namespace Dashi.EisensteinIrreducibleSupportExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinPrimeClassificationExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinLocalPrimeFactorizationExact
open Dashi.EisensteinSplitPrimeFactorCountExact
open Dashi.EisensteinRamifiedThreeExact

/-- Embedded natural numbers factor in the Eisenstein ring along the ordinary
natural prime factorization. -/
theorem natCast_eq_prod_primeFactors
    (n : Nat) (hn : n ≠ 0) :
    (n : EisensteinQA)
      = ∏ p ∈ n.primeFactors, (p : EisensteinQA) ^ (n.factorization p) := by
  have hnat :
      n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
    exact (Nat.prod_factorization_pow_eq_self hn).symm
  exact_mod_cast hnat

/-- An irreducible divisor of an embedded positive natural lies above at least
one ordinary rational prime divisor. -/
theorem irreducible_dvd_natCast_lies_over_prime
    (q : EisensteinQA) (hq : Irreducible q)
    (n : Nat) (hn : n ≠ 0)
    (hqn : q ∣ (n : EisensteinQA)) :
    ∃ p ∈ n.primeFactors, q ∣ (p : EisensteinQA) := by
  have hprime : Prime q := hq.prime
  rw [natCast_eq_prod_primeFactors n hn] at hqn
  rcases (hprime.dvd_finsetProd_iff _).1 hqn with ⟨p, hpMem, hpow⟩
  refine ⟨p, hpMem, ?_⟩
  exact (Prime.dvd_pow_iff_dvd hprime).1 hpow

/-- Local classification of an irreducible factor above one rational prime. -/
theorem irreducible_above_rational_prime
    (q : EisensteinQA) (hq : Irreducible q)
    (p : Nat) (hp : p.Prime)
    (hqp : q ∣ (p : EisensteinQA)) :
    (p = 3 ∧ Associated q ramifiedPrime)
      ∨ (∃ h1 : p % 3 = 1,
          Associated q (splitPi p hp h1)
            ∨ Associated q (splitPiBar p hp h1))
      ∨ (p % 3 = 2 ∧ Associated q (p : EisensteinQA)) := by
  by_cases h3 : p = 3
  · left
    refine ⟨h3, ?_⟩
    subst p
    have hdiv : q ∣ ramifiedPrime * ramifiedPrime * unitNegOmegaSquared := by
      simpa [three_eq_ramified_square_times_unit] using hqp
    rcases hq.prime.dvd_or_dvd hdiv with hsquare | hunit
    · rcases hq.prime.dvd_or_dvd hsquare with hram | hram
      · exact hq.associated_of_dvd ramifiedPrime_irreducible hram
      · exact hq.associated_of_dvd ramifiedPrime_irreducible hram
    · exact (hq.not_isUnit (isUnit_of_dvd_unit hunit ramifiedUnit_isUnit)).elim
  · have hmod_ne_zero : p % 3 ≠ 0 := by
      intro h0
      have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
      rcases (Nat.dvd_prime hp).1 h3dvd with h31 | h3p
      · norm_num at h31
      · exact h3 h3p.symm
    have hcases : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hcases with h1 | h2
    · right; left
      refine ⟨h1, ?_⟩
      have hsplit :
          q ∣ splitPi p hp h1 * splitPiBar p hp h1 := by
        simpa [natCast_split_factorization p hp h1] using hqp
      rcases hq.prime.dvd_or_dvd hsplit with hl | hr
      · exact Or.inl (hq.associated_of_dvd (splitPi_irreducible p hp h1) hl)
      · exact Or.inr (hq.associated_of_dvd (splitPiBar_irreducible p hp h1) hr)
    · right; right
      refine ⟨h2, ?_⟩
      exact hq.associated_of_dvd (inert_prime_irreducible p hp h2) hqp

/-- Every irreducible factor occurring in a represented element lies in the
explicit ramified/inert/split support over a prime dividing its norm.  The
primality proof is returned explicitly so downstream dependent terms do not
rely on proof-search through nested existential binders. -/
theorem irreducible_factor_of_norm_classified
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n)
    (q : EisensteinQA) (hq : Irreducible q)
    (hqz : q ∣ z) :
    ∃ p, ∃ hpMem : p ∈ n.primeFactors, ∃ hp : p.Prime,
      (p = 3 ∧ Associated q ramifiedPrime)
        ∨ (∃ h1 : p % 3 = 1,
            Associated q (splitPi p hp h1)
              ∨ Associated q (splitPiBar p hp h1))
        ∨ (p % 3 = 2 ∧ Associated q (p : EisensteinQA)) := by
  have hqn : q ∣ (n : EisensteinQA) := by
    have hprod : (n : EisensteinQA) = z * star z := by
      rw [← hz]
      exact QuadraticAlgebra.algebraMap_norm_eq_mul_star z
    rw [hprod]
    exact hqz.mul_right (star z)
  obtain ⟨p, hpMem, hqp⟩ :=
    irreducible_dvd_natCast_lies_over_prime q hq n hn.ne' hqn
  let hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  refine ⟨p, hpMem, hp, ?_⟩
  exact irreducible_above_rational_prime q hq p hp hqp

structure EisensteinIrreducibleSupportBoundary where
  embeddedNaturalFactorizationPaid : Bool := true
  irreducibleLiesOverRationalPrimePaid : Bool := true
  localAbovePrimeClassificationPaid : Bool := true
  normFactorSupportClassified : Bool := true
  associateNormalFormSurjectionReady : Bool := true
  finalCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinIrreducibleSupportBoundary := {}

end Dashi.EisensteinIrreducibleSupportExact
