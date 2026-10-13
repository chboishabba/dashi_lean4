import Integration.EisensteinLatticeCountingMaxCut
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Dashi.EisensteinInertPrimeLegendreExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut

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

/-- The universal representation formula has therefore been reduced below the
raw quadratic-form layer.  A complete proof must additionally identify
`legendreSym p (-3)` from `p mod 3`, handle the ramified prime `3`, construct
split-prime factors for `p ≡ 1 (mod 3)`, and count them using a genuine
factorization/UFD theorem. -/
structure InertPrimeBoundary where
  discriminantMinusThreeIdentityPaid : Bool := true
  genericNonresidueDivisibilityPaid : Bool := true
  negThreeLegendreClassifiedByModThree : Bool := false
  oddInertPrimeCoordinatesRecovered : Bool := false
  ramifiedPrimeThreeClassified : Bool := false
  splitPrimeFactorsConstructed : Bool := false
  eisensteinUFDCountingPaid : Bool := false
  universalPositiveRepresentationFormulaPaid : Bool := false

def canonicalBoundary : InertPrimeBoundary := {}

end Dashi.EisensteinInertPrimeLegendreExact
