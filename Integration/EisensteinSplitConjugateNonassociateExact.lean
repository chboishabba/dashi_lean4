import Integration.EisensteinSixUnitsExact
import Integration.EisensteinPrimeNormIrreducibleExact
import Mathlib.Data.Nat.Prime.Int

namespace Dashi.EisensteinSplitConjugateNonassociateExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinSplitPrimeExact
open Dashi.EisensteinSixUnitsExact

/-- A rational prime cannot itself be a nontrivial integer square. -/
theorem nat_prime_not_int_square
    (p : Nat) (hp : p.Prime) (a : Int) :
    (a * a : Int) ≠ p := by
  intro h
  have hsquare : IsSquare (p : Int) := ⟨a, by simpa [pow_two] using h.symm⟩
  exact (Nat.prime_iff_prime_int.mp hp).not_isSquare hsquare

/-- If `3*a^2` is a rational prime, that prime must be `3`; this is excluded
for split primes `p ≡ 1 mod 3`. -/
theorem three_mul_square_ne_split_prime
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) (a : Int) :
    (3 * a * a : Int) ≠ p := by
  intro h
  have h3dvdInt : (3 : Int) ∣ (p : Int) := by
    refine ⟨a * a, ?_⟩
    simpa [mul_assoc] using h.symm
  have h3dvd : 3 ∣ p := by exact_mod_cast h3dvdInt
  rcases (Nat.dvd_prime hp).1 h3dvd with h31 | h3p
  · norm_num at h31
  · subst p
    norm_num at hmod

/-- For a split rational prime, an Eisenstein norm-p factor and its conjugate
are genuinely different associate classes.  The proof exhausts the six units;
the only possible fixed-axis equations force either `p=a^2` or `p=3a^2`. -/
theorem split_norm_prime_not_associated_star
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    ¬ Associated z (star z) := by
  intro hassoc
  rcases hassoc with ⟨u, hu⟩
  have huClass := unit_classification (u : EisensteinQA) u.isUnit
  rcases z with ⟨a, b⟩
  have hzQ : eisensteinNorm a b = p := by
    simpa [norm_eq_coordinate_norm] using hz
  rcases huClass with h | h | h | h | h | h
  · have heq := hu
    simp [h, unitOne, asQuadraticAlgebra] at heq
    have hb : b = 0 := by omega
    rw [hb] at hzQ
    simp [eisensteinNorm] at hzQ
    exact nat_prime_not_int_square p hp a (by simpa [pow_two] using hzQ)
  · have heq := hu
    simp [h, unitNegOne, asQuadraticAlgebra] at heq
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simp [ha, hb, eisensteinNorm] at hzQ
    exact hp.ne_zero (by exact_mod_cast hzQ.symm)
  · have heq := hu
    simp [h, unitOmega, asQuadraticAlgebra] at heq
    have hab : a = b := by omega
    rw [hab] at hzQ
    simp [eisensteinNorm] at hzQ
    exact nat_prime_not_int_square p hp b (by simpa [pow_two] using hzQ)
  · have heq := hu
    simp [h, unitNegOmega, asQuadraticAlgebra] at heq
    have hab : a = -b := by omega
    rw [hab] at hzQ
    simp [eisensteinNorm] at hzQ
    exact three_mul_square_ne_split_prime p hp hmod b (by nlinarith [hzQ])
  · have heq := hu
    simp [h, unitOmegaSquared, asQuadraticAlgebra] at heq
    have ha : a = 0 := by omega
    rw [ha] at hzQ
    simp [eisensteinNorm] at hzQ
    exact nat_prime_not_int_square p hp b (by simpa [pow_two] using hzQ)
  · have heq := hu
    simp [h, unitNegOmegaSquared, asQuadraticAlgebra] at heq
    have hab : a = 2 * b := by omega
    rw [hab] at hzQ
    simp [eisensteinNorm] at hzQ
    exact three_mul_square_ne_split_prime p hp hmod b (by nlinarith [hzQ])

/-- Associate-class form used by the exponent-choice encoder. -/
theorem split_mk_ne_star_mk
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    Associates.mk z ≠ Associates.mk (star z) := by
  intro hmk
  exact split_norm_prime_not_associated_star p hp hmod z hz
    (Associates.quot_mk_eq_mk_iff.mp hmk)

structure EisensteinSplitConjugateBoundary where
  sixUnitCasesExhausted : Bool := true
  squareCollapseExcluded : Bool := true
  ramifiedAxisCollapseExcludedForSplitPrime : Bool := true
  splitFactorDistinctFromConjugateUpToUnits : Bool := true
  exponentChoiceInjectionReady : Bool := true
  exponentChoiceSurjectionPaid : Bool := false

def canonicalBoundary : EisensteinSplitConjugateBoundary := {}

end Dashi.EisensteinSplitConjugateNonassociateExact
