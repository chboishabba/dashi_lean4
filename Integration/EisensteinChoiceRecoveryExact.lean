import Integration.EisensteinChoiceRepresentativeExact

namespace Dashi.EisensteinChoiceRecoveryExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitPrimeFactorCountExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact

------------------------------------------------------------------------
-- Generic finite-product multiplicity plumbing.
------------------------------------------------------------------------

/-- Irreducible multiplicity is additive across a finite product of nonzero
associates.  This is the exact finite-product form needed for the canonical
prime-block product below. -/
theorem count_finset_prod
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Associates EisensteinQA)
    (hf : ∀ i ∈ s, f i ≠ 0)
    (q : Associates EisensteinQA) (hq : Irreducible q) :
    Associates.count q (∏ i ∈ s, f i).factors
      = ∑ i ∈ s, Associates.count q (f i).factors := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hq]
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
      have hfs : ∏ i ∈ s, f i ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Associates.count_mul hfa hfs hq]
      rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

------------------------------------------------------------------------
-- Totalized local block, so the finite product has a proof-irrelevant API.
------------------------------------------------------------------------

noncomputable def localChoiceAssociate
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) : Associates EisensteinQA :=
  if hp : p ∈ n.primeFactors then
    Associates.mk (localChoiceBlock n H c p hp)
  else
    1

theorem localChoiceBlock_ne_zero
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) (hpMem : p ∈ n.primeFactors) :
    localChoiceBlock n H c p hpMem ≠ 0 := by
  intro hzero
  have hnorm := localChoiceBlock_norm n H c p hpMem
  rw [hzero] at hnorm
  simp only [map_zero] at hnorm
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hp0 : (p : Int) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact (pow_ne_zero (n.factorization p) hp0) hnorm.symm

theorem localChoiceAssociate_ne_zero
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p : Nat) : localChoiceAssociate n H c p ≠ 0 := by
  classical
  by_cases hpMem : p ∈ n.primeFactors
  · simp only [localChoiceAssociate, dif_pos hpMem]
    exact Associates.mk_ne_zero.mpr
      (localChoiceBlock_ne_zero n H c p hpMem)
  · simp [localChoiceAssociate, hpMem]

/-- The element-level canonical product agrees with the proof-irrelevant
associate-level product. -/
theorem mk_choiceRepresentative
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n) :
    Associates.mk (choiceRepresentative n H c)
      = ∏ p ∈ n.primeFactors, localChoiceAssociate n H c p := by
  classical
  simp [choiceRepresentative, localChoiceAssociate, map_prod]

------------------------------------------------------------------------
-- Exact recovery of every split coordinate.
------------------------------------------------------------------------

/-- A selected split prime has zero multiplicity in every local block lying
over a different rational prime. -/
theorem splitPi_count_other_block_zero
    (n : Nat) (H : InertEvenCondition n) (c : SplitChoice n)
    (p r : Nat) (hp : p.Prime) (h1 : p % 3 = 1)
    (hrMem : r ∈ n.primeFactors) (hpr : p ≠ r) :
    Associates.count (Associates.mk (splitPi p hp h1))
        (Associates.mk (localChoiceBlock n H c r hrMem)).factors
      = 0 := by
  classical
  let q : Associates EisensteinQA := Associates.mk (splitPi p hp h1)
  have hq : Irreducible q :=
    Associates.irreducible_mk.mpr (splitPi_irreducible p hp h1)
  have hb0 : Associates.mk (localChoiceBlock n H c r hrMem) ≠ 0 :=
    Associates.mk_ne_zero.mpr (localChoiceBlock_ne_zero n H c r hrMem)
  by_contra hcount
  have hle : q ≤ Associates.mk (localChoiceBlock n H c r hrMem) :=
    Associates.le_of_count_ne_zero hb0 hq hcount
  have hdvd : splitPi p hp h1 ∣ localChoiceBlock n H c r hrMem := by
    rw [← Associates.mk_le_mk_iff_dvd]
    exact hle
  exact splitPi_not_dvd_other_block n H c p r hp h1 hrMem hpr hdvd

/-- In the full canonical product, the selected `π_p` multiplicity is exactly
the requested split coordinate. -/
theorem splitPi_count_choiceRepresentative
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n)
    (p : Nat) (hpMem : p ∈ splitPrimeFactors n) :
    let hpPrimeMem := (Finset.mem_filter.mp hpMem).1
    let h1 := (Finset.mem_filter.mp hpMem).2
    let hp := Nat.prime_of_mem_primeFactors hpPrimeMem
    Associates.count (Associates.mk (splitPi p hp h1))
        (Associates.mk (choiceRepresentative n H c)).factors
      = (c ⟨p, hpMem⟩).val := by
  classical
  dsimp
  let hpPrimeMem := (Finset.mem_filter.mp hpMem).1
  let h1 := (Finset.mem_filter.mp hpMem).2
  let hp := Nat.prime_of_mem_primeFactors hpPrimeMem
  let q : Associates EisensteinQA := Associates.mk (splitPi p hp h1)
  have hq : Irreducible q :=
    Associates.irreducible_mk.mpr (splitPi_irreducible p hp h1)
  rw [mk_choiceRepresentative]
  rw [count_finset_prod n.primeFactors
    (localChoiceAssociate n H c)
    (fun r _ => localChoiceAssociate_ne_zero n H c r)
    q hq]
  rw [Finset.sum_eq_single p]
  · simp [localChoiceAssociate, hpPrimeMem]
    exact splitPi_count_own_block n H c p hpMem
  · intro r hrMem hne
    have hrPrimeMem : r ∈ n.primeFactors := hrMem
    simp only [localChoiceAssociate, dif_pos hrPrimeMem]
    exact splitPi_count_other_block_zero n H c p r hp h1 hrPrimeMem hne.symm
  · exact hpPrimeMem

/-- Canonical representatives recover exactly the split-exponent choice used
to construct them. -/
theorem splitChoice_choiceRepresentative
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n) :
    splitChoiceOfRepresentation
        (choiceRepresentative n H c) n hn
        (choiceRepresentative_norm n hn H c)
      = c := by
  funext p
  apply Fin.ext
  change
    Associates.count
        (Associates.mk
          (splitPi p.1
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp p.2).1)
            (Finset.mem_filter.mp p.2).2))
        (Associates.mk (choiceRepresentative n H c)).factors
      = (c p).val
  exact splitPi_count_choiceRepresentative n hn H c p.1 p.2

/-- Distinct split choices yield distinct associate classes.  This is the
injective half of the norm-fibre / split-choice classification. -/
theorem choiceRepresentative_not_associated_of_ne
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c d : SplitChoice n) (hcd : c ≠ d) :
    ¬ Associated (choiceRepresentative n H c) (choiceRepresentative n H d) := by
  intro hassoc
  apply hcd
  have hsame := splitChoiceOfRepresentation_eq_of_associated
    (choiceRepresentative n H c) (choiceRepresentative n H d)
    n hn
    (choiceRepresentative_norm n hn H c)
    (choiceRepresentative_norm n hn H d)
    hassoc
  simpa [splitChoice_choiceRepresentative n hn H] using hsame

structure EisensteinChoiceRecoveryBoundary where
  finiteProductMultiplicityPaid : Bool := true
  ownSplitMultiplicityRecovered : Bool := true
  otherPrimeContaminationExcluded : Bool := true
  canonicalChoiceRoundTripPaid : Bool := true
  distinctChoicesDistinctAssociateClassesPaid : Bool := true
  everyNormElementAssociatedToCanonicalChoicePaid : Bool := false
  exactAssociateClassCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinChoiceRecoveryBoundary := {}

end Dashi.EisensteinChoiceRecoveryExact
