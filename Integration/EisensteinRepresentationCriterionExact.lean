import Integration.EisensteinInertExponentParityExact
import Integration.EisensteinSplitPrimeExact
import Integration.EisensteinRamifiedThreeExact
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Nat.Even

namespace Dashi.EisensteinRepresentationCriterionExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeExact
open Dashi.EisensteinRamifiedThreeExact
open Dashi.EisensteinInertExponentParityExact

/-- The exact local obstruction condition for positive Eisenstein norms. -/
def InertEvenCondition (n : Nat) : Prop :=
  ∀ p : Nat, p.Prime → p % 3 = 2 → Even (n.factorization p)

------------------------------------------------------------------------
-- Canonical local factors selected from the already-proved prime trichotomy.
------------------------------------------------------------------------

noncomputable def splitPrimeRepresentative
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) : EisensteinQA :=
  Classical.choose (split_prime_has_norm_witness p hp hmod)

theorem splitPrimeRepresentative_norm
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (splitPrimeRepresentative p hp hmod) = p :=
  Classical.choose_spec (split_prime_has_norm_witness p hp hmod)

/-- One factor representing the complete rational prime power occurring in
`n`.  Split primes use a chosen norm-p factor, the ramified prime uses `1-ω`,
and inert primes with even exponent use the embedded rational half-power. -/
noncomputable def localPrimePowerRepresentative
    (n : Nat) (H : InertEvenCondition n) (p : Nat) : EisensteinQA :=
  if hp : p.Prime then
    if h3 : p = 3 then
      ramifiedPrime ^ (n.factorization p)
    else if h1 : p % 3 = 1 then
      splitPrimeRepresentative p hp h1 ^ (n.factorization p)
    else
      (p : EisensteinQA) ^ ((n.factorization p) / 2)
  else
    1

/-- Every local factor has precisely the corresponding rational prime-power
norm. -/
theorem localPrimePowerRepresentative_norm
    (n : Nat) (H : InertEvenCondition n)
    (p : Nat) (hp : p.Prime) :
    QuadraticAlgebra.norm (localPrimePowerRepresentative n H p)
      = (p : Int) ^ (n.factorization p) := by
  by_cases h3 : p = 3
  · subst p
    simp [localPrimePowerRepresentative, hp, ramifiedPrime_norm_three]
  · by_cases h1 : p % 3 = 1
    · simp [localPrimePowerRepresentative, hp, h3, h1,
        splitPrimeRepresentative_norm]
    · have hmod_lt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hmod_ne_zero : p % 3 ≠ 0 := by
        intro h0
        have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
        rcases (Nat.dvd_prime hp).1 h3dvd with h31 | h3p
        · norm_num at h31
        · exact h3 h3p.symm
      have h2 : p % 3 = 2 := by omega
      have heven : Even (n.factorization p) := H p hp h2
      simp [localPrimePowerRepresentative, hp, h3, h1,
        QuadraticAlgebra.norm_natCast, map_pow]
      rw [pow_mul, Nat.two_mul_div_two_of_even heven]

------------------------------------------------------------------------
-- Multiply the local prime-power representatives.
------------------------------------------------------------------------

noncomputable def representationElement
    (n : Nat) (H : InertEvenCondition n) : EisensteinQA :=
  ∏ p ∈ n.primeFactors, localPrimePowerRepresentative n H p

theorem representationElement_norm
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    QuadraticAlgebra.norm (representationElement n H) = n := by
  classical
  calc
    QuadraticAlgebra.norm (representationElement n H)
        = ∏ p ∈ n.primeFactors,
            QuadraticAlgebra.norm (localPrimePowerRepresentative n H p) := by
              simp [representationElement, map_prod]
    _ = ∏ p ∈ n.primeFactors,
            (p : Int) ^ (n.factorization p) := by
              apply Finset.prod_congr rfl
              intro p hpMem
              exact localPrimePowerRepresentative_norm
                n H p (Nat.prime_of_mem_primeFactors hpMem)
    _ = n := by
      have hnat :
          (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n := by
        rw [← Nat.prod_factorization_eq_prod_primeFactors]
        exact Nat.prod_factorization_pow_eq_self hn.ne'
      exact_mod_cast hnat

/-- Constructive-in-principle converse: the local parity condition builds a
literal Eisenstein integer of norm `n`. -/
theorem inert_even_constructs_norm_representation
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    ∃ z : EisensteinQA, QuadraticAlgebra.norm z = n :=
  ⟨representationElement n H, representationElement_norm n hn H⟩

/-- Exact positive-n representability criterion. -/
theorem norm_representable_iff_inert_even
    (n : Nat) (hn : 0 < n) :
    (∃ z : EisensteinQA, QuadraticAlgebra.norm z = n)
      ↔ InertEvenCondition n := by
  constructor
  · rintro ⟨z, hz⟩ p hp hmod
    exact represented_norm_has_even_inert_exponent z n p hn hz hp hmod
  · exact inert_even_constructs_norm_representation n hn

structure EisensteinRepresentationCriterionBoundary where
  ramifiedPrimePowerConstructorPaid : Bool := true
  splitPrimePowerConstructorPaid : Bool := true
  inertEvenPrimePowerConstructorPaid : Bool := true
  finitePrimeFactorProductConstructorPaid : Bool := true
  positiveRepresentabilityIffInertEvenPaid : Bool := true
  exactRepresentationCardinalityPaid : Bool := false
  divisorCharacterFormulaPaid : Bool := false

def canonicalBoundary : EisensteinRepresentationCriterionBoundary := {}

end Dashi.EisensteinRepresentationCriterionExact
