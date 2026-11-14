import Integration.EisensteinChoiceRecoveryExact
import Integration.EisensteinIrreducibleSupportExact
import Integration.EisensteinRationalPrimeFactorCountExact
import Integration.EisensteinConjugateFactorCountExact

namespace Dashi.EisensteinCanonicalAssociateExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitPrimeFactorCountExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact
open Dashi.EisensteinChoiceRecoveryExact
open Dashi.EisensteinIrreducibleSupportExact
open Dashi.EisensteinNormFactorEquationExact
open Dashi.EisensteinConjugateFactorCountExact
open Dashi.EisensteinRationalPrimeFactorCountExact
open Dashi.EisensteinInertExponentParityExact
open Dashi.EisensteinLocalPrimeFactorizationExact
open Dashi.EisensteinRamifiedThreeExact

------------------------------------------------------------------------
-- Fixed local multiplicities for the ramified and inert primes.
------------------------------------------------------------------------

theorem ramified_count_three :
    Associates.count (Associates.mk ramifiedPrime)
        (Associates.mk (3 : EisensteinQA)).factors = 2 := by
  classical
  let q : Associates EisensteinQA := Associates.mk ramifiedPrime
  have hq : Irreducible q :=
    Associates.irreducible_mk.mpr ramifiedPrime_irreducible
  have hpi0 : q ≠ 0 :=
    Associates.mk_ne_zero.mpr ramifiedPrime_irreducible.ne_zero
  have hu0 : Associates.mk unitNegOmegaSquared ≠ 0 :=
    Associates.mk_ne_zero.mpr ramifiedUnit_isUnit.ne_zero
  have hucount :
      Associates.count q (Associates.mk unitNegOmegaSquared).factors = 0 := by
    by_contra hc
    have hle := Associates.le_of_count_ne_zero hu0 hq hc
    have hdvd : ramifiedPrime ∣ unitNegOmegaSquared := by
      rw [← Associates.mk_le_mk_iff_dvd]
      exact hle
    exact ramifiedPrime_irreducible.not_isUnit
      (isUnit_of_dvd_unit hdvd ramifiedUnit_isUnit)
  rw [three_eq_ramified_square_times_unit]
  simp only [Associates.mk_mul_mk]
  rw [Associates.count_mul (mul_ne_zero hpi0 hpi0) hu0 hq]
  rw [Associates.count_mul hpi0 hpi0 hq]
  simp [Associates.count_self, hq, hucount]

/-- A ramified Eisenstein prime cannot occur in a different rational prime. -/
theorem ramified_count_other_natPrime_zero
    (p : Nat) (hp : p.Prime) (hp3 : p ≠ 3) :
    Associates.count (Associates.mk ramifiedPrime)
        (Associates.mk (p : EisensteinQA)).factors = 0 := by
  classical
  let q : Associates EisensteinQA := Associates.mk ramifiedPrime
  have hq : Irreducible q :=
    Associates.irreducible_mk.mpr ramifiedPrime_irreducible
  have hp0 : Associates.mk (p : EisensteinQA) ≠ 0 := by
    apply Associates.mk_ne_zero.mpr
    exact_mod_cast hp.ne_zero
  by_contra hc
  have hle := Associates.le_of_count_ne_zero hp0 hq hc
  have hdvd : ramifiedPrime ∣ (p : EisensteinQA) := by
    rw [← Associates.mk_le_mk_iff_dvd]
    exact hle
  have hnormDvd : (3 : Int) ∣ QuadraticAlgebra.norm (p : EisensteinQA) :=
    norm_prime_dvd_norm_of_dvd ramifiedPrime (p : EisensteinQA) 3
      ramifiedPrime_norm_three hdvd
  simp only [QuadraticAlgebra.norm_natCast] at hnormDvd
  have h3nat : 3 ∣ p ^ 2 := by exact_mod_cast hnormDvd
  have h3p : 3 ∣ p :=
    (Prime.dvd_pow_iff_dvd (by norm_num : Nat.Prime 3)).1 h3nat
  rcases (Nat.dvd_prime hp).1 h3p with h31 | h3eqp
  · norm_num at h31
  · exact hp3 h3eqp.symm

/-- In an embedded positive natural, the ramified prime occurs with twice the
ordinary 3-adic exponent. -/
theorem ramified_count_natCast
    (n : Nat) (hn : 0 < n) :
    Associates.count (Associates.mk ramifiedPrime)
        (Associates.mk (n : EisensteinQA)).factors
      = 2 * n.factorization 3 := by
  classical
  rw [natCast_eq_prod_primeFactors n hn.ne']
  rw [← Associates.finsetProd_mk]
  have hq : Irreducible (Associates.mk ramifiedPrime) :=
    Associates.irreducible_mk.mpr ramifiedPrime_irreducible
  rw [count_finset_prod n.primeFactors
    (fun p => Associates.mk ((p : EisensteinQA) ^ (n.factorization p)))
    (fun p hpMem => by
      apply Associates.mk_ne_zero.mpr
      exact pow_ne_zero _ (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hpMem).ne_zero))
    (Associates.mk ramifiedPrime) hq]
  by_cases h3mem : 3 ∈ n.primeFactors
  · rw [Finset.sum_eq_single 3]
    · rw [Associates.mk_pow]
      rw [Associates.count_pow
        (Associates.mk_ne_zero.mpr (by norm_num : (3 : EisensteinQA) ≠ 0)) hq]
      rw [ramified_count_three]
      omega
    · intro p hpMem hpne
      rw [Associates.mk_pow]
      rw [Associates.count_pow
        (Associates.mk_ne_zero.mpr (by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hpMem).ne_zero)) hq]
      rw [ramified_count_other_natPrime_zero p
        (Nat.prime_of_mem_primeFactors hpMem) hpne.symm]
      simp
    · exact h3mem
  · have hfac3 : n.factorization 3 = 0 := by
      simpa [Nat.mem_primeFactors, hn.ne'] using h3mem
    rw [hfac3]
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro p hpMem
    have hpne : p ≠ 3 := by
      intro h
      subst p
      exact h3mem hpMem
    rw [Associates.mk_pow]
    rw [Associates.count_pow
      (Associates.mk_ne_zero.mpr (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hpMem).ne_zero)) hq]
    rw [ramified_count_other_natPrime_zero p
      (Nat.prime_of_mem_primeFactors hpMem) hpne]
    simp

/-- Every representation of a positive norm has exactly the ordinary 3-adic
exponent many ramified Eisenstein factors. -/
theorem ramified_count_of_representation
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n) :
    Associates.count (Associates.mk ramifiedPrime) (Associates.mk z).factors
      = n.factorization 3 := by
  classical
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
    omega
  have hq : Irreducible (Associates.mk ramifiedPrime) :=
    Associates.irreducible_mk.mpr ramifiedPrime_irreducible
  have hnorm := nat_norm_prime_count_eq_add z n hn hz
    (Associates.mk ramifiedPrime) hq
  rw [ramified_count_natCast n hn] at hnorm
  have hstarPiI : Irreducible (star ramifiedPrime) :=
    star_irreducible ramifiedPrime_irreducible
  have hpiDvd3 : ramifiedPrime ∣ (3 : EisensteinQA) := by
    refine ⟨ramifiedPrime * unitNegOmegaSquared, ?_⟩
    simpa [mul_assoc] using three_eq_ramified_square_times_unit
  have hstarDvd3 : star ramifiedPrime ∣ (3 : EisensteinQA) := by
    have h := (star_dvd_star_iff ramifiedPrime (3 : EisensteinQA)).2 hpiDvd3
    simpa using h
  have hstarAssoc : Associated (star ramifiedPrime) ramifiedPrime := by
    rcases irreducible_above_rational_prime
      (star ramifiedPrime) hstarPiI 3 (by norm_num) hstarDvd3 with h | h | h
    · exact h.2
    · rcases h with ⟨hmod, _⟩
      norm_num at hmod
    · rcases h with ⟨hmod, _⟩
      norm_num at hmod
  have hstarCount :
      Associates.count (Associates.mk ramifiedPrime)
          (Associates.mk (star z)).factors
        = Associates.count (Associates.mk ramifiedPrime)
          (Associates.mk z).factors := by
    have ht := conjugate_prime_count z hz0 ramifiedPrime ramifiedPrime_irreducible
    have hmk : Associates.mk (star ramifiedPrime) = Associates.mk ramifiedPrime :=
      Associates.quot_mk_eq_mk_iff.mpr hstarAssoc
    simpa [hmk] using ht
  rw [hstarCount] at hnorm
  omega

/-- Inert rational-prime multiplicity in any representation is exactly half
its (necessarily even) ordinary exponent. -/
theorem inert_count_of_representation
    (z : EisensteinQA) (n p : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n)
    (hp : p.Prime) (hmod : p % 3 = 2) :
    Associates.count (Associates.mk (p : EisensteinQA))
        (Associates.mk z).factors
      = n.factorization p / 2 := by
  classical
  have hq : Irreducible (p : EisensteinQA) :=
    inert_prime_irreducible p hp hmod
  have hqA : Irreducible (Associates.mk (p : EisensteinQA)) :=
    Associates.irreducible_mk.mpr hq
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
    omega
  have hnorm := nat_norm_prime_count_eq_add z n hn hz
    (Associates.mk (p : EisensteinQA)) hqA
  have hleft := rational_prime_count_eq_factorization n p hn hp hq
  rw [hleft] at hnorm
  have hstar := conjugate_prime_count z hz0 (p : EisensteinQA) hq
  have hstarEq :
      Associates.count (Associates.mk (p : EisensteinQA))
          (Associates.mk (star z)).factors
        = Associates.count (Associates.mk (p : EisensteinQA))
          (Associates.mk z).factors := by
    simpa using hstar
  rw [hstarEq] at hnorm
  rcases represented_norm_has_even_inert_exponent z n p hn hz hp hmod with ⟨k, hk⟩
  omega

------------------------------------------------------------------------
-- Canonical associate normal form.
------------------------------------------------------------------------

/-- If an irreducible associate does not divide the embedded norm, its factor
multiplicity vanishes in every representation of that norm. -/
theorem count_zero_of_not_dvd_natNorm
    (z : EisensteinQA) (n : Nat) (hz : QuadraticAlgebra.norm z = n)
    (q : EisensteinQA) (hq : Irreducible q)
    (hqn : ¬ q ∣ (n : EisensteinQA)) :
    Associates.count (Associates.mk q) (Associates.mk z).factors = 0 := by
  classical
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have hn0 : n = 0 := by simpa using hz.symm
    subst n
    exact hqn (dvd_zero q)
  have hqA : Irreducible (Associates.mk q) :=
    Associates.irreducible_mk.mpr hq
  by_contra hc
  have hle := Associates.le_of_count_ne_zero
    (Associates.mk_ne_zero.mpr hz0) hqA hc
  have hqz : q ∣ z := by
    rw [← Associates.mk_le_mk_iff_dvd]
    exact hle
  apply hqn
  have hprod : (n : EisensteinQA) = z * star z := by
    rw [← hz]
    exact QuadraticAlgebra.algebraMap_norm_eq_mul_star z
  rw [hprod]
  exact dvd_mul_of_dvd_left hqz _

/-- Every represented positive norm is associated to the canonical product
selected by its split-exponent observer.  Thus the split choices are complete
invariants for associate classes. -/
theorem represented_element_associated_to_choiceRepresentative
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n) :
    Associated z
      (choiceRepresentative n
        ((norm_representable_iff_inert_even n hn).1 ⟨z, hz⟩)
        (splitChoiceOfRepresentation z n hn hz)) := by
  classical
  let H : InertEvenCondition n :=
    (norm_representable_iff_inert_even n hn).1 ⟨z, hz⟩
  let c : SplitChoice n := splitChoiceOfRepresentation z n hn hz
  let w : EisensteinQA := choiceRepresentative n H c
  have hwNorm : QuadraticAlgebra.norm w = n :=
    choiceRepresentative_norm n hn H c
  have hz0 : Associates.mk z ≠ 0 := by
    apply Associates.mk_ne_zero.mpr
    intro h
    subst z
    simp at hz
    omega
  have hw0 : Associates.mk w ≠ 0 := by
    apply Associates.mk_ne_zero.mpr
    intro h
    subst w
    simp at hwNorm
    omega
  have hmk : Associates.mk z = Associates.mk w := by
    apply Associates.eq_of_eq_counts hz0 hw0
    intro q hq
    rcases Associates.mk_surjective q with ⟨q0, rfl⟩
    have hq0 : Irreducible q0 := Associates.irreducible_mk.mp hq
    by_cases hqn : q0 ∣ (n : EisensteinQA)
    · obtain ⟨p, hpMem, hqp⟩ :=
        irreducible_dvd_natCast_lies_over_prime q0 hq0 n hn.ne' hqn
      let hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      rcases irreducible_above_rational_prime q0 hq0 p hp hqp with
          hram | hsplit | hinert
      · rcases hram with ⟨hp3, hassoc⟩
        subst p
        have hqeq : Associates.mk q0 = Associates.mk ramifiedPrime :=
          Associates.quot_mk_eq_mk_iff.mpr hassoc
        rw [hqeq]
        exact (ramified_count_of_representation z n hn hz).trans
          (ramified_count_of_representation w n hn hwNorm).symm
      · rcases hsplit with ⟨h1, hleft | hright⟩
        · have hqeq : Associates.mk q0 = Associates.mk (splitPi p hp h1) :=
            Associates.quot_mk_eq_mk_iff.mpr hleft
          rw [hqeq]
          let idx : {p // p ∈ splitPrimeFactors n} :=
            ⟨p, Finset.mem_filter.mpr ⟨hpMem, h1⟩⟩
          change
            Associates.count (Associates.mk (splitPi p hp h1))
                (Associates.mk z).factors
              = Associates.count (Associates.mk (splitPi p hp h1))
                (Associates.mk w).factors
          have hzCount :
              Associates.count (Associates.mk (splitPi p hp h1))
                  (Associates.mk z).factors = (c idx).val := by
            rfl
          have hwCount :
              Associates.count (Associates.mk (splitPi p hp h1))
                  (Associates.mk w).factors = (c idx).val := by
            simpa [w, idx] using
              splitPi_count_choiceRepresentative n hn H c p idx.2
          exact hzCount.trans hwCount.symm
        · have hqeq : Associates.mk q0 = Associates.mk (splitPiBar p hp h1) :=
            Associates.quot_mk_eq_mk_iff.mpr hright
          rw [hqeq]
          let idx : {p // p ∈ splitPrimeFactors n} :=
            ⟨p, Finset.mem_filter.mpr ⟨hpMem, h1⟩⟩
          have hzSum := split_exponent_sum z n p hn hz hp h1
          have hwSum := split_exponent_sum w n p hn hwNorm hp h1
          have hzLeft :
              Associates.count (Associates.mk (splitPi p hp h1))
                  (Associates.mk z).factors = (c idx).val := by
            rfl
          have hwLeft :
              Associates.count (Associates.mk (splitPi p hp h1))
                  (Associates.mk w).factors = (c idx).val := by
            simpa [w, idx] using
              splitPi_count_choiceRepresentative n hn H c p idx.2
          rw [hzLeft] at hzSum
          rw [hwLeft] at hwSum
          omega
      · rcases hinert with ⟨h2, hassoc⟩
        have hqeq : Associates.mk q0 = Associates.mk (p : EisensteinQA) :=
          Associates.quot_mk_eq_mk_iff.mpr hassoc
        rw [hqeq]
        exact (inert_count_of_representation z n p hn hz hp h2).trans
          (inert_count_of_representation w n p hn hwNorm hp h2).symm
    · rw [count_zero_of_not_dvd_natNorm z n hz q0 hq0 hqn]
      rw [count_zero_of_not_dvd_natNorm w n hwNorm q0 hq0 hqn]
  exact Associates.quot_mk_eq_mk_iff.mp hmk

structure EisensteinCanonicalAssociateBoundary where
  ramifiedMultiplicityPaid : Bool := true
  inertMultiplicityPaid : Bool := true
  splitMultiplicityPaid : Bool := true
  irreducibleSupportClassificationReused : Bool := true
  everyNormElementAssociatedToCanonicalChoicePaid : Bool := true
  splitChoicesCompleteForAssociateClassesPaid : Bool := true
  literalSixUnitOrbitCardinalityPaid : Bool := false
  geometricShellCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinCanonicalAssociateBoundary := {}

end Dashi.EisensteinCanonicalAssociateExact
