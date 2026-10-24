import Integration.EisensteinConjugateFactorCountExact
import Integration.EisensteinPrimeClassificationExact
import Mathlib.Data.Nat.Factorization.Basic

namespace Dashi.EisensteinRationalPrimeFactorCountExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeExact

/-- Divisibility between embedded natural numbers in the Eisenstein ring is
exactly ordinary natural-number divisibility. -/
theorem natCast_dvd_natCast_iff (m n : Nat) :
    (m : EisensteinQA) ∣ (n : EisensteinQA) ↔ m ∣ n := by
  rw [natCast_dvd_iff_coordinates]
  simp [Int.natCast_dvd_natCast]

/-- Powers of an embedded natural prime satisfy the same divisibility relation
as the corresponding natural prime power. -/
theorem natPrimePow_dvd_natCast_iff (p k n : Nat) :
    (p : EisensteinQA) ^ k ∣ (n : EisensteinQA) ↔ p ^ k ∣ n := by
  simpa using natCast_dvd_natCast_iff (p ^ k) n

/-- If the embedded rational prime is irreducible in the Eisenstein UFD, its
factor-set multiplicity in an embedded positive natural is exactly the usual
`Nat.factorization` exponent. -/
theorem rational_prime_count_eq_factorization
    (n p : Nat) (hn : 0 < n) (hp : p.Prime)
    (hirr : Irreducible (p : EisensteinQA)) :
    Associates.count (Associates.mk (p : EisensteinQA))
        (Associates.mk (n : EisensteinQA)).factors
      = n.factorization p := by
  classical
  have hnE : Associates.mk (n : EisensteinQA) ≠ 0 := by
    apply Associates.mk_ne_zero.mpr
    exact_mod_cast hn.ne'
  have hpA : Irreducible (Associates.mk (p : EisensteinQA)) :=
    Associates.irreducible_mk.mpr hirr
  apply Nat.le_antisymm
  · let k := Associates.count (Associates.mk (p : EisensteinQA))
      (Associates.mk (n : EisensteinQA)).factors
    have hkA :
        (Associates.mk (p : EisensteinQA)) ^ k
          ≤ Associates.mk (n : EisensteinQA) := by
      apply (Associates.prime_pow_dvd_iff_le hnE hpA).2
      exact le_rfl
    have hkE : (p : EisensteinQA) ^ k ∣ (n : EisensteinQA) := by
      rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
      exact hkA
    have hkNat : p ^ k ∣ n :=
      (natPrimePow_dvd_natCast_iff p k n).1 hkE
    exact (hp.pow_dvd_iff_le_factorization hn.ne').1 hkNat
  · let k := n.factorization p
    have hkNat : p ^ k ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
    have hkE : (p : EisensteinQA) ^ k ∣ (n : EisensteinQA) :=
      (natPrimePow_dvd_natCast_iff p k n).2 hkNat
    have hkA :
        (Associates.mk (p : EisensteinQA)) ^ k
          ≤ Associates.mk (n : EisensteinQA) := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hkE
    exact (Associates.prime_pow_dvd_iff_le hnE hpA).1 hkA

structure EisensteinRationalPrimeFactorCountBoundary where
  natCastDivisibilityWeldPaid : Bool := true
  primePowerDivisibilityWeldPaid : Bool := true
  ufdCountEqualsNatFactorizationPaid : Bool := true
  inertParityReady : Bool := true
  globalShellCardinalityPaid : Bool := false

def canonicalBoundary : EisensteinRationalPrimeFactorCountBoundary := {}

end Dashi.EisensteinRationalPrimeFactorCountExact
