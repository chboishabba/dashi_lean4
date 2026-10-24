import Integration.EisensteinLatticeCounting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Dashi.EisensteinLegendreModThreeExact

open Nat
open ZMod
open Dashi.EisensteinLatticeCounting

/-- For every odd prime `p`, quadratic reciprocity collapses the discriminant
character to the prime-three character:

`(-3 / p) = (p / 3)`.

The two reciprocity signs cancel exactly. -/
theorem legendre_neg_three_eq_legendre_three
    (p : Nat) [Fact p.Prime] [Fact (3 : Nat).Prime]
    (hp2 : p ≠ 2) :
    legendreSym p (-3) = legendreSym 3 p := by
  have hodd : p % 2 = 1 :=
    (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp2
  rw [legendreSym.at_neg hp2, χ₄_eq_neg_one_pow hodd]
  simpa using
    (legendreSym.quadratic_reciprocity'
      (p := p) (q := 3) hp2 (by norm_num)).symm

/-- Odd primes congruent to `1 mod 3` see `-3` as a quadratic residue. -/
theorem legendre_neg_three_eq_one_of_mod_three_one
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 1) :
    legendreSym p (-3) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (3 : Nat).Prime := ⟨by norm_num⟩
  rw [legendre_neg_three_eq_legendre_three p hp2, legendreSym.mod]
  rw_mod_cast [hmod]
  norm_num

/-- Odd primes congruent to `2 mod 3` see `-3` as a quadratic non-residue. -/
theorem legendre_neg_three_eq_neg_one_of_mod_three_two
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 2) :
    legendreSym p (-3) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (3 : Nat).Prime := ⟨by norm_num⟩
  rw [legendre_neg_three_eq_legendre_three p hp2, legendreSym.mod]
  rw_mod_cast [hmod]
  norm_num

/-- On odd primes away from the ramified prime `3`, the Legendre symbol is
literally the repository's signed `chi_-3` character. -/
theorem legendre_neg_three_eq_chiMinus3Int
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    legendreSym p (-3) = chiMinus3Int p := by
  have hmod_ne_zero : p % 3 ≠ 0 := by
    intro hzero
    have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
    rcases (Nat.dvd_prime hp).1 h3dvd with h31 | h3p
    · norm_num at h31
    · exact hp3 h3p.symm
  have hcases : p % 3 = 1 ∨ p % 3 = 2 := by
    omega
  rcases hcases with h1 | h2
  · rw [legendre_neg_three_eq_one_of_mod_three_one p hp hp2 h1]
    simp [chiMinus3Int, h1]
  · rw [legendre_neg_three_eq_neg_one_of_mod_three_two p hp hp2 h2]
    simp [chiMinus3Int, h2]

structure LegendreModThreeBoundary where
  reciprocityCollapsePaid : Bool := true
  oddSplitResidueClassPaid : Bool := true
  oddInertResidueClassPaid : Bool := true
  oddPrimeCharacterIdentificationPaid : Bool := true
  primeTwoHandledSeparately : Bool := false
  splitPrimeFactorConstructed : Bool := false
  eisensteinUFDCountingPaid : Bool := false

def canonicalBoundary : LegendreModThreeBoundary := {}

end Dashi.EisensteinLegendreModThreeExact
