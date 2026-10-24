import Integration.EisensteinLatticeCounting
import Integration.EisensteinCharacterLocalFactorsExact
import Integration.EisensteinRepresentationCriterionExact
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Dashi.EisensteinDivisorCharacterProductExact

open Finset
open Nat
open ArithmeticFunction
open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinCharacterLocalFactorsExact
open Dashi.EisensteinRepresentationCriterionExact

local instance : Fact (3 : Nat).Prime := ⟨by norm_num⟩

------------------------------------------------------------------------
-- The literal mod-3 character as a multiplicative arithmetic function.
------------------------------------------------------------------------

def chiMinus3AF : ArithmeticFunction Int where
  toFun n := legendreSym 3 n
  map_zero' := by simp

theorem chiMinus3Int_eq_legendre (n : Nat) :
    chiMinus3Int n = legendreSym 3 n := by
  rw [legendreSym.mod]
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 3 <;>
    simp [chiMinus3Int, h]

theorem chiMinus3AF_apply (n : Nat) :
    chiMinus3AF n = chiMinus3Int n := by
  simpa [chiMinus3AF] using (chiMinus3Int_eq_legendre n).symm

theorem chiMinus3AF_multiplicative : chiMinus3AF.IsMultiplicative := by
  constructor
  · simp [chiMinus3AF]
  · intro m n _
    simp [chiMinus3AF, legendreSym.mul]

/-- Divisor-character sum as a Dirichlet convolution with zeta. -/
noncomputable def chiMinus3DivisorAF : ArithmeticFunction Int :=
  (ζ : ArithmeticFunction Int) * chiMinus3AF

/-- This convolution is multiplicative. -/
theorem chiMinus3DivisorAF_multiplicative :
    chiMinus3DivisorAF.IsMultiplicative :=
  isMultiplicative_zeta.intCast.mul chiMinus3AF_multiplicative

/-- Canonical divisor-character sum.  This definition deliberately reuses the
signed sum already owned by the counting module. -/
def chiMinus3DivisorSum (n : Nat) : Int :=
  signedChiMinus3DivisorSum n

------------------------------------------------------------------------
-- Bridge the original finite positive-divisor enumerator to Mathlib divisors.
------------------------------------------------------------------------

theorem positiveDivisors_eq_divisors (n : Nat) (hn : n ≠ 0) :
    positiveDivisors n = n.divisors := by
  ext d
  simp only [positiveDivisors, Finset.mem_filter, Finset.mem_range,
    Nat.mem_divisors, and_iff_right hn]
  constructor
  · rintro ⟨hdlt, hdpos, hdvd⟩
    exact ⟨hdvd, hdpos.ne'⟩
  · rintro ⟨hdvd, hd0⟩
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    exact ⟨Nat.lt_succ_of_le hdle, hdpos, hdvd⟩

theorem chiMinus3DivisorAF_apply (n : Nat) (hn : n ≠ 0) :
    chiMinus3DivisorAF n = chiMinus3DivisorSum n := by
  unfold chiMinus3DivisorAF chiMinus3DivisorSum
  rw [coe_zeta_mul_apply]
  rw [positiveDivisors_eq_divisors n hn]
  apply Finset.sum_congr rfl
  intro d hd
  simp [chiMinus3AF_apply]

------------------------------------------------------------------------
-- Prime-power factors and global Euler product.
------------------------------------------------------------------------

def chiMinus3PrimePowerFactor (p e : Nat) : Int :=
  ∑ i ∈ Finset.range (e + 1), (chiMinus3Int p) ^ i

theorem chiMinus3DivisorAF_prime_pow
    {p : Nat} (hp : p.Prime) (e : Nat) :
    chiMinus3DivisorAF (p ^ e) = chiMinus3PrimePowerFactor p e := by
  rw [chiMinus3DivisorAF_apply _ (pow_ne_zero e hp.ne_zero)]
  unfold chiMinus3DivisorSum signedChiMinus3DivisorSum
  rw [positiveDivisors_eq_divisors _ (pow_ne_zero e hp.ne_zero), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chiMinus3Int_eq_legendre, Nat.cast_pow, legendreSym.mul]
  induction i with
  | zero => simp [chiMinus3PrimePowerFactor]
  | succ i ih =>
      simp [chiMinus3Int_eq_legendre, pow_succ]

/-- The character divisor sum factors as the product of its local prime-power
factors. -/
theorem chiMinus3DivisorSum_factorization
    (n : Nat) (hn : n ≠ 0) :
    chiMinus3DivisorSum n
      = ∏ p ∈ n.primeFactors,
          chiMinus3PrimePowerFactor p (n.factorization p) := by
  have hfactor :=
    chiMinus3DivisorAF_multiplicative.multiplicative_factorization n hn
  rw [chiMinus3DivisorAF_apply n hn] at hfactor
  rw [← Nat.support_factorization] at hfactor
  simpa [chiMinus3DivisorAF_prime_pow] using hfactor

------------------------------------------------------------------------
-- Exact local values.
------------------------------------------------------------------------

theorem chiMinus3PrimePowerFactor_ramified
    {p e : Nat} (hmod : p % 3 = 0) :
    chiMinus3PrimePowerFactor p e = 1 := by
  simp [chiMinus3PrimePowerFactor, chiMinus3Int, hmod]

theorem chiMinus3PrimePowerFactor_split
    {p e : Nat} (hmod : p % 3 = 1) :
    chiMinus3PrimePowerFactor p e = e + 1 := by
  simp [chiMinus3PrimePowerFactor, chiMinus3Int, hmod]

theorem chiMinus3PrimePowerFactor_inert
    {p e : Nat} (hmod : p % 3 = 2) :
    chiMinus3PrimePowerFactor p e = if Even e then 1 else 0 := by
  simp [chiMinus3PrimePowerFactor, chiMinus3Int, hmod,
    localFactor_neg_one]

/-- Positivity of the global character sum is exactly the inert-even criterion. -/
theorem chiMinus3DivisorSum_pos_iff_inert_even
    (n : Nat) (hn : 0 < n) :
    0 < chiMinus3DivisorSum n ↔ InertEvenCondition n := by
  rw [chiMinus3DivisorSum_factorization n hn.ne']
  constructor
  · intro hpos p hp hmod
    have hpMem : p ∈ n.primeFactors := by
      by_contra hnot
      have hfac0 : n.factorization p = 0 := by
        simpa [Nat.mem_primeFactors, hp, hn.ne'] using hnot
      exact Even.zero
    have hlocal_nonzero :
        chiMinus3PrimePowerFactor p (n.factorization p) ≠ 0 := by
      intro hz
      have hprod0 :
          (∏ q ∈ n.primeFactors,
            chiMinus3PrimePowerFactor q (n.factorization q)) = 0 :=
        Finset.prod_eq_zero hpMem hz
      rw [hprod0] at hpos
      omega
    rw [chiMinus3PrimePowerFactor_inert hmod] at hlocal_nonzero
    split at hlocal_nonzero
    · assumption
    · simp at hlocal_nonzero
  · intro H
    apply Finset.prod_pos
    intro p hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hmod : p % 3
    · rw [chiMinus3PrimePowerFactor_ramified hmod]
      norm_num
    · rw [chiMinus3PrimePowerFactor_split hmod]
      exact_mod_cast Nat.succ_pos (n.factorization p)
    · rw [chiMinus3PrimePowerFactor_inert hmod, if_pos (H p hp hmod)]
      norm_num

/-- The canonical signed shell is exactly six times the multiplicative
character sum. -/
theorem signedShell_eq_six_mul_character_sum
    (n : Nat) (_hn : n ≠ 0) :
    signedEisensteinDivisorShellCount n = 6 * chiMinus3DivisorSum n := rfl

structure EisensteinDivisorCharacterProductBoundary where
  characterAsArithmeticFunctionPaid : Bool := true
  characterMultiplicativePaid : Bool := true
  divisorConvolutionMultiplicativePaid : Bool := true
  globalPrimePowerProductPaid : Bool := true
  localRamifiedFactorPaid : Bool := true
  localSplitFactorPaid : Bool := true
  localInertFactorPaid : Bool := true
  positivityIffRepresentabilityCriterionPaid : Bool := true
  geometricCardinalityEqualityPaid : Bool := false

def canonicalBoundary : EisensteinDivisorCharacterProductBoundary := {}

end Dashi.EisensteinDivisorCharacterProductExact
