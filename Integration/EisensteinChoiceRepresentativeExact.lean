import Integration.EisensteinSplitExponentChoiceExact
import Integration.EisensteinRepresentationCriterionExact
import Integration.EisensteinSplitConjugateNonassociateExact

namespace Dashi.EisensteinChoiceRepresentativeExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitPrimeFactorCountExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinRamifiedThreeExact
open Dashi.EisensteinEuclideanDomainExact

/-- Index a split prime divisor as a coordinate of `SplitChoice`. -/
def splitIndex (n p : Nat) (hpMem : p ∈ n.primeFactors)
    (h1 : p % 3 = 1) : {p // p ∈ splitPrimeFactors n} :=
  ⟨p, Finset.mem_filter.mpr ⟨hpMem, h1⟩⟩

/-- Local prime-power block with the requested split exponent distribution. -/
noncomputable def localChoiceBlock
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) (hpMem : p ∈ n.primeFactors) : EisensteinQA :=
  let hp := Nat.prime_of_mem_primeFactors hpMem
  let e := n.factorization p
  if h3 : p = 3 then
    ramifiedPrime ^ e
  else if h1 : p % 3 = 1 then
    let k := (c (splitIndex n p hpMem h1)).val
    splitPi p hp h1 ^ k * splitPiBar p hp h1 ^ (e - k)
  else
    (p : EisensteinQA) ^ (e / 2)

/-- Every block has exactly norm `p^v_p(n)`. -/
theorem localChoiceBlock_norm
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) (hpMem : p ∈ n.primeFactors) :
    QuadraticAlgebra.norm (localChoiceBlock n H c p hpMem)
      = (p : Int) ^ (n.factorization p) := by
  let hp := Nat.prime_of_mem_primeFactors hpMem
  let e := n.factorization p
  by_cases h3 : p = 3
  · subst p
    simp [localChoiceBlock, hp, e, ramifiedPrime_norm_three]
  · by_cases h1 : p % 3 = 1
    · let k := (c (splitIndex n p hpMem h1)).val
      have hk : k ≤ e := by
        exact Nat.le_of_lt_succ (c (splitIndex n p hpMem h1)).isLt
      simp [localChoiceBlock, hp, e, h3, h1, k,
        map_mul, map_pow, splitPi_norm]
      rw [← pow_add]
      congr 1
      omega
    · have h0 : p % 3 ≠ 0 := by
        intro hm
        have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hm
        rcases (Nat.dvd_prime hp).1 h3dvd with h31 | h3p
        · norm_num at h31
        · exact h3 h3p.symm
      have h2 : p % 3 = 2 := by omega
      have heven : Even e := H p hp h2
      simp [localChoiceBlock, hp, e, h3, h1,
        QuadraticAlgebra.norm_natCast, map_pow]
      rw [pow_mul, Nat.two_mul_div_two_of_even heven]

/-- Canonical element for a split-exponent choice. -/
noncomputable def choiceRepresentative
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n) : EisensteinQA :=
  ∏ p ∈ n.primeFactors, localChoiceBlock n H c p ‹p ∈ n.primeFactors›

/-- Every canonical choice representative lies in the norm-n fibre. -/
theorem choiceRepresentative_norm
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n) :
    QuadraticAlgebra.norm (choiceRepresentative n H c) = n := by
  classical
  calc
    QuadraticAlgebra.norm (choiceRepresentative n H c)
      = ∏ p ∈ n.primeFactors,
          QuadraticAlgebra.norm (localChoiceBlock n H c p ‹p ∈ n.primeFactors›) := by
            simp [choiceRepresentative, map_prod]
    _ = ∏ p ∈ n.primeFactors, (p : Int) ^ (n.factorization p) := by
          apply Finset.prod_congr rfl
          intro p hpMem
          exact localChoiceBlock_norm n H c p hpMem
    _ = n := by
      have hnat :
          (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n :=
        Nat.prod_factorization_pow_eq_self hn.ne'
      exact_mod_cast hnat

/-- Divisibility transfers through norm: a norm-p element dividing x forces p
dividing the integer norm of x. -/
theorem norm_prime_dvd_norm_of_dvd
    (pi x : EisensteinQA) (p : Nat)
    (hpi : QuadraticAlgebra.norm pi = p)
    (hdvd : pi ∣ x) :
    (p : Int) ∣ QuadraticAlgebra.norm x := by
  rcases hdvd with ⟨y, rfl⟩
  refine ⟨QuadraticAlgebra.norm y, ?_⟩
  rw [map_mul, hpi]

/-- A selected split factor over p cannot divide a local block over a different
rational prime r. -/
theorem splitPi_not_dvd_other_block
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p r : Nat) (hp : p.Prime) (h1 : p % 3 = 1)
    (hrMem : r ∈ n.primeFactors) (hpr : p ≠ r) :
    ¬ splitPi p hp h1 ∣ localChoiceBlock n H c r hrMem := by
  intro hdvd
  have hnormDvd : (p : Int) ∣
      QuadraticAlgebra.norm (localChoiceBlock n H c r hrMem) :=
    norm_prime_dvd_norm_of_dvd _ _ p (splitPi_norm p hp h1) hdvd
  rw [localChoiceBlock_norm n H c r hrMem] at hnormDvd
  have hpnat : p ∣ r ^ (n.factorization r) := by exact_mod_cast hnormDvd
  have hprdvd : p ∣ r := (Prime.dvd_pow_iff_dvd hp.prime).1 hpnat
  have hr := Nat.prime_of_mem_primeFactors hrMem
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 hprdvd)

/-- The chosen π_p multiplicity of its own local split block is exactly k. -/
theorem splitPi_count_own_block
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) (hpMem : p ∈ splitPrimeFactors n) :
    let hpPrimeMem := (Finset.mem_filter.mp hpMem).1
    let h1 := (Finset.mem_filter.mp hpMem).2
    let hp := Nat.prime_of_mem_primeFactors hpPrimeMem
    Associates.count (Associates.mk (splitPi p hp h1))
      (Associates.mk (localChoiceBlock n H c p hpPrimeMem)).factors
      = (c ⟨p, hpMem⟩).val := by
  classical
  dsimp
  let hpPrimeMem := (Finset.mem_filter.mp hpMem).1
  let h1 := (Finset.mem_filter.mp hpMem).2
  let hp := Nat.prime_of_mem_primeFactors hpPrimeMem
  let pi := splitPi p hp h1
  let pib := splitPiBar p hp h1
  let k := (c ⟨p, hpMem⟩).val
  let e := n.factorization p
  have hp3 : p ≠ 3 := by
    intro h; subst p; norm_num at h1
  have hpiI : Irreducible (Associates.mk pi) :=
    Associates.irreducible_mk.mpr (splitPi_irreducible p hp h1)
  have hpibI : Irreducible (Associates.mk pib) :=
    Associates.irreducible_mk.mpr (splitPiBar_irreducible p hp h1)
  have hne : Associates.mk pi ≠ Associates.mk pib :=
    split_mk_ne_star_mk p hp h1 pi (splitPi_norm p hp h1)
  have hpi0 : Associates.mk pi ≠ 0 := by
    exact Associates.mk_ne_zero.mpr (splitPi_irreducible p hp h1).ne_zero
  have hpib0 : Associates.mk pib ≠ 0 := by
    exact Associates.mk_ne_zero.mpr (splitPiBar_irreducible p hp h1).ne_zero
  simp [localChoiceBlock, hp, hpPrimeMem, hp3, h1, pi, pib, k, e,
    Associates.factors_mul, Associates.count_mul, hpi0, hpib0,
    hpiI, hpibI, Associates.count_pow, Associates.count_self,
    Associates.count_eq_zero_of_ne hpiI hpibI hne]

structure EisensteinChoiceRepresentativeBoundary where
  canonicalChoiceProductConstructed : Bool := true
  everyChoiceHasNormN : Bool := true
  otherPrimeBlocksDoNotContaminateSplitValuation : Bool := true
  ownSplitBlockCountPaid : Bool := true
  fullProductChoiceRecoveryPaid : Bool := false
  associateClassEquivalencePaid : Bool := false

def canonicalBoundary : EisensteinChoiceRepresentativeBoundary := {}

end Dashi.EisensteinChoiceRepresentativeExact
