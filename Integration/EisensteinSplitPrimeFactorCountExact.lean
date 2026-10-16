import Integration.EisensteinSplitConjugateNonassociateExact
import Integration.EisensteinLocalPrimeFactorizationExact
import Integration.EisensteinRationalPrimeFactorCountExact
import Mathlib.RingTheory.Coprime.Basic

namespace Dashi.EisensteinSplitPrimeFactorCountExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinLocalPrimeFactorizationExact
open Dashi.EisensteinSplitConjugateNonassociateExact
open Dashi.EisensteinRationalPrimeFactorCountExact

noncomputable def splitPi
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) : EisensteinQA :=
  splitPrimeRepresentative p hp hmod

noncomputable def splitPiBar
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) : EisensteinQA :=
  star (splitPi p hp hmod)

theorem splitPi_norm
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (splitPi p hp hmod) = p :=
  splitPrimeRepresentative_norm p hp hmod

theorem splitPi_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    Irreducible (splitPi p hp hmod) :=
  split_prime_left_irreducible p hp hmod

theorem splitPiBar_irreducible
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    Irreducible (splitPiBar p hp hmod) :=
  split_prime_right_irreducible p hp hmod

theorem splitPi_not_associated_bar
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Associated (splitPi p hp hmod) (splitPiBar p hp hmod) := by
  exact split_norm_prime_not_associated_star p hp hmod
    (splitPi p hp hmod) (splitPi_norm p hp hmod)

theorem splitPi_coprime_bar
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    IsCoprime (splitPi p hp hmod) (splitPiBar p hp hmod) := by
  apply (splitPi_irreducible p hp hmod).coprime_iff_not_dvd.mpr
  intro hdvd
  exact splitPi_not_associated_bar p hp hmod
    ((splitPi_irreducible p hp hmod).associated_of_dvd
      (splitPiBar_irreducible p hp hmod) hdvd)

/-- The exact selected split factorization. -/
theorem natCast_split_factorization
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    (p : EisensteinQA) = splitPi p hp hmod * splitPiBar p hp hmod :=
  split_prime_factorization p hp hmod

/-- For rational integers, divisibility by `π^k` is equivalent to divisibility
by `p^k`.  The nontrivial direction uses conjugation plus coprimality of the two
split factors. -/
theorem splitPi_pow_dvd_natCast_iff
    (n p k : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    splitPi p hp hmod ^ k ∣ (n : EisensteinQA) ↔ p ^ k ∣ n := by
  constructor
  · intro hpi
    have hbar : splitPiBar p hp hmod ^ k ∣ (n : EisensteinQA) := by
      rcases hpi with ⟨c, hc⟩
      refine ⟨star c, ?_⟩
      have hs := congrArg star hc
      simpa [splitPiBar, map_pow] using hs
    have hcop : IsCoprime
        (splitPi p hp hmod ^ k) (splitPiBar p hp hmod ^ k) := by
      exact (splitPi_coprime_bar p hp hmod).pow k k
    have hprod :
        splitPi p hp hmod ^ k * splitPiBar p hp hmod ^ k
          ∣ (n : EisensteinQA) :=
      hcop.mul_dvd hpi hbar
    have hpPowE : (p : EisensteinQA) ^ k ∣ (n : EisensteinQA) := by
      rw [natCast_split_factorization p hp hmod, mul_pow]
      exact hprod
    exact (natPrimePow_dvd_natCast_iff p k n).1 hpPowE
  · intro hpPow
    have hpPowE : (p : EisensteinQA) ^ k ∣ (n : EisensteinQA) :=
      (natPrimePow_dvd_natCast_iff p k n).2 hpPow
    have hpiPow : splitPi p hp hmod ^ k ∣ (p : EisensteinQA) ^ k := by
      rw [natCast_split_factorization p hp hmod, mul_pow]
      exact dvd_mul_right _ _
    exact hpiPow.trans hpPowE

/-- The UFD multiplicity of either chosen split prime above `p` in an embedded
positive integer `n` is exactly the ordinary p-adic exponent. -/
theorem splitPi_count_in_natCast_eq_factorization
    (n p : Nat) (hn : 0 < n) (hp : p.Prime) (hmod : p % 3 = 1) :
    Associates.count (Associates.mk (splitPi p hp hmod))
        (Associates.mk (n : EisensteinQA)).factors
      = n.factorization p := by
  classical
  let q := splitPi p hp hmod
  have hq : Irreducible q := splitPi_irreducible p hp hmod
  have hqA : Irreducible (Associates.mk q) := Associates.irreducible_mk.mpr hq
  have hnE : Associates.mk (n : EisensteinQA) ≠ 0 := by
    apply Associates.mk_ne_zero.mpr
    exact_mod_cast hn.ne'
  apply Nat.le_antisymm
  · let k := Associates.count (Associates.mk q)
      (Associates.mk (n : EisensteinQA)).factors
    have hkA : (Associates.mk q) ^ k ≤ Associates.mk (n : EisensteinQA) :=
      (Associates.prime_pow_dvd_iff_le hnE hqA).2 le_rfl
    have hkE : q ^ k ∣ (n : EisensteinQA) := by
      rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
      exact hkA
    have hkNat : p ^ k ∣ n := by
      simpa [q] using
        (splitPi_pow_dvd_natCast_iff n p k hp hmod).1 hkE
    exact (hp.pow_dvd_iff_le_factorization hn.ne').1 hkNat
  · let k := n.factorization p
    have hkNat : p ^ k ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
    have hkE : q ^ k ∣ (n : EisensteinQA) := by
      simpa [q] using
        (splitPi_pow_dvd_natCast_iff n p k hp hmod).2 hkNat
    have hkA : (Associates.mk q) ^ k ≤ Associates.mk (n : EisensteinQA) := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hkE
    exact (Associates.prime_pow_dvd_iff_le hnE hqA).1 hkA

structure EisensteinSplitPrimeFactorCountBoundary where
  splitConjugatesCoprimePaid : Bool := true
  splitPowDivisibilityCharacterized : Bool := true
  splitFactorCountEqualsNatValuationPaid : Bool := true
  exponentSumEquationReady : Bool := true
  associateNormalFormCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinSplitPrimeFactorCountBoundary := {}

end Dashi.EisensteinSplitPrimeFactorCountExact
