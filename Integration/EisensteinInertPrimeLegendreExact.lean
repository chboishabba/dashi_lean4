import Integration.EisensteinLatticeCountingMaxCut
import Integration.EisensteinLegendreModThreeExact
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Dashi.EisensteinInertPrimeLegendreExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut
open Dashi.EisensteinLegendreModThreeExact

/-- The norm equation is a binary quadratic equation of discriminant `-3`:
`4 Q(a,b) = (2a-b)^2 - (-3)b^2`. -/
theorem transformed_norm_identity (a b : Int) :
    (2 * a - b) ^ 2 - (-3 : Int) * b ^ 2 = 4 * eisensteinNorm a b := by
  simp [eisensteinNorm]
  ring

/-- If `-3` is a quadratic non-residue mod a prime `p`, then divisibility of an
Eisenstein norm by `p` forces the transformed coordinates to vanish mod `p`.
This is the exact binary-quadratic-form core of inert-prime obstruction. -/
theorem legendre_neg_three_forces_transformed_coordinates
    (p : Nat) (hp : Nat.Prime p)
    (hleg : legendreSym p (-3) = -1)
    {a b : Int}
    (hdiv : (p : Int) ∣ eisensteinNorm a b) :
    (p : Int) ∣ (2 * a - b) ∧ (p : Int) ∣ b := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hfour :
      (p : Int) ∣ (2 * a - b) ^ 2 - (-3 : Int) * b ^ 2 := by
    rcases hdiv with ⟨k, hk⟩
    refine ⟨4 * k, ?_⟩
    rw [transformed_norm_identity, hk]
    ring
  exact legendreSym.prime_dvd_of_eq_neg_one hleg hfour

/-- The abstract Legendre hypothesis above is discharged for every odd inert
prime directly from the residue class `p ≡ 2 mod 3`. -/
theorem odd_prime_mod_three_two_forces_transformed_coordinates
    (p : Nat) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hmod : p % 3 = 2)
    {a b : Int}
    (hdiv : (p : Int) ∣ eisensteinNorm a b) :
    (p : Int) ∣ (2 * a - b) ∧ (p : Int) ∣ b := by
  exact legendre_neg_three_forces_transformed_coordinates
    p hp
    (legendre_neg_three_eq_neg_one_of_mod_three_two p hp hp2 hmod)
    hdiv

/-- The exceptional inert prime `2` is handled directly on the quadratic form:
if `2` divides `Q(a,b)`, then both coordinates are even. -/
theorem two_dvd_norm_forces_coordinates
    {a b : Int}
    (hdiv : (2 : Int) ∣ eisensteinNorm a b) :
    (2 : Int) ∣ a ∧ (2 : Int) ∣ b := by
  have hq : eisensteinNorm a b % 2 = 0 :=
    Int.dvd_iff_emod_eq_zero.mp hdiv
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · exact ⟨Int.dvd_of_emod_eq_zero ha, Int.dvd_of_emod_eq_zero hb⟩
  all_goals
    exfalso
    simp [eisensteinNorm, Int.add_emod, Int.sub_emod, Int.mul_emod, ha, hb] at hq

/-- After the reciprocity and prime-two cuts, the inert-prime obstruction is no
longer conditional on an unexplained Legendre value.  What remains for the full
representation theorem is split-prime construction and global Eisenstein
factorization/counting. -/
structure InertPrimeBoundary where
  discriminantMinusThreeIdentityPaid : Bool := true
  genericNonresidueDivisibilityPaid : Bool := true
  negThreeLegendreClassifiedByModThree : Bool := true
  oddInertPrimeTransformedCoordinatesPaid : Bool := true
  primeTwoCoordinateObstructionPaid : Bool := true
  ramifiedPrimeThreeClassified : Bool := true
  splitPrimeFactorsConstructed : Bool := false
  eisensteinUFDCountingPaid : Bool := false
  universalPositiveRepresentationFormulaPaid : Bool := false

def canonicalBoundary : InertPrimeBoundary := {}

end Dashi.EisensteinInertPrimeLegendreExact
