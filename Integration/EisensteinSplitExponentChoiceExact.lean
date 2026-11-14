import Integration.EisensteinSplitPrimeFactorCountExact
import Integration.EisensteinNormFactorEquationExact
import Integration.EisensteinConjugateFactorCountExact

namespace Dashi.EisensteinSplitExponentChoiceExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeFactorCountExact
open Dashi.EisensteinNormFactorEquationExact
open Dashi.EisensteinConjugateFactorCountExact

/-- Split rational prime divisors of `n`. -/
def splitPrimeFactors (n : Nat) : Finset Nat :=
  n.primeFactors.filter fun p => p % 3 = 1

/-- One independent exponent choice `0 <= k <= v_p(n)` for every split prime
factor of `n`. -/
def SplitChoice (n : Nat) :=
  (p : {p // p ∈ splitPrimeFactors n}) → Fin (n.factorization p.1 + 1)

noncomputable instance splitChoiceFintype (n : Nat) : Fintype (SplitChoice n) :=
  inferInstance

/-- The parameter space has the expected product cardinality. -/
theorem card_splitChoice (n : Nat) :
    Fintype.card (SplitChoice n)
      = ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) := by
  classical
  simp [SplitChoice, splitPrimeFactors]

/-- For a represented positive norm, the two conjugate split-factor
multiplicities add to the rational p-adic exponent. -/
theorem split_exponent_sum
    (z : EisensteinQA) (n p : Nat)
    (hn : 0 < n) (hz : QuadraticAlgebra.norm z = n)
    (hp : p.Prime) (hmod : p % 3 = 1) :
    Associates.count (Associates.mk (splitPi p hp hmod))
        (Associates.mk z).factors
      + Associates.count (Associates.mk (splitPiBar p hp hmod))
        (Associates.mk z).factors
      = n.factorization p := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
    omega
  let q := splitPi p hp hmod
  let qA : Associates EisensteinQA := Associates.mk q
  have hq : Irreducible q := splitPi_irreducible p hp hmod
  have hqA : Irreducible qA := Associates.irreducible_mk.mpr hq
  have hnorm := nat_norm_prime_count_eq_add z n hn hz qA hqA
  have hleft :
      Associates.count qA (Associates.mk (n : EisensteinQA)).factors
        = n.factorization p := by
    simpa [q, qA] using
      splitPi_count_in_natCast_eq_factorization n p hn hp hmod
  have hstar :
      Associates.count qA (Associates.mk (star z)).factors
        = Associates.count (Associates.mk (splitPiBar p hp hmod))
            (Associates.mk z).factors := by
    have ht := conjugate_prime_count z hz0 q hq
    simpa [q, qA, splitPiBar] using ht
  rw [hleft, hstar] at hnorm
  omega

/-- The selected split exponent is automatically in the finite choice range. -/
noncomputable def splitChoiceOfRepresentation
    (z : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n) : SplitChoice n :=
  fun p =>
    let prime := p.1
    have hpMem : prime ∈ n.primeFactors := (Finset.mem_filter.mp p.2).1
    have hmod : prime % 3 = 1 := (Finset.mem_filter.mp p.2).2
    have hp : prime.Prime := Nat.prime_of_mem_primeFactors hpMem
    let k := Associates.count (Associates.mk (splitPi prime hp hmod))
      (Associates.mk z).factors
    ⟨k, by
      have hsum := split_exponent_sum z n prime hn hz hp hmod
      omega⟩

/-- Associate elements have identical split-exponent choices. -/
theorem splitChoiceOfRepresentation_eq_of_associated
    (z w : EisensteinQA) (n : Nat) (hn : 0 < n)
    (hz : QuadraticAlgebra.norm z = n)
    (hw : QuadraticAlgebra.norm w = n)
    (hassoc : Associated z w) :
    splitChoiceOfRepresentation z n hn hz
      = splitChoiceOfRepresentation w n hn hw := by
  funext p
  apply Fin.ext
  change Associates.count _ (Associates.mk z).factors
    = Associates.count _ (Associates.mk w).factors
  have hmk : Associates.mk z = Associates.mk w :=
    Associates.quot_mk_eq_mk_iff.mpr hassoc
  rw [hmk]

structure EisensteinSplitExponentChoiceBoundary where
  splitExponentSumPaid : Bool := true
  finiteChoiceTypeConstructed : Bool := true
  exactChoiceCardinalityPaid : Bool := true
  choiceInvariantUnderUnitsPaid : Bool := true
  choiceCompletenessForAssociateClassesPaid : Bool := false
  normFiberCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinSplitExponentChoiceBoundary := {}

end Dashi.EisensteinSplitExponentChoiceExact
