import Integration.EisensteinLatticeCounting
import Mathlib.Algebra.Ring.GeomSum

namespace Dashi.EisensteinCharacterLocalFactorsExact

open Finset
open Dashi.EisensteinLatticeCounting

/-- Local prime-power Dirichlet factor `1 + χ + ... + χ^e`. -/
def localCharacterFactor (χ : Int) (e : Nat) : Int :=
  ∑ j ∈ Finset.range (e + 1), χ ^ j

/-- Ramified-character local factor: `χ = 0` contributes exactly `1`. -/
theorem localCharacterFactor_zero (e : Nat) :
    localCharacterFactor 0 e = 1 := by
  simp [localCharacterFactor]

/-- Split-character local factor: `χ = +1` contributes `e+1`. -/
theorem localCharacterFactor_one (e : Nat) :
    localCharacterFactor 1 e = (e + 1 : Nat) := by
  simp [localCharacterFactor]

/-- Inert-character local factor is the alternating geometric sum.  It vanishes
exactly when the number of terms `e+1` is even, i.e. when the exponent `e` is
odd; otherwise it is one. -/
theorem localCharacterFactor_neg_one (e : Nat) :
    localCharacterFactor (-1) e = if Even (e + 1) then 0 else 1 := by
  simpa [localCharacterFactor] using
    (neg_one_geom_sum (R := Int) (n := e + 1))

/-- Local factor selected directly by the repository's literal `χ₋₃`. -/
def localChiMinus3PrimeFactor (p e : Nat) : Int :=
  localCharacterFactor (chiMinus3Int p) e

theorem localChiMinus3PrimeFactor_mod_zero
    (p e : Nat) (h : p % 3 = 0) :
    localChiMinus3PrimeFactor p e = 1 := by
  simp [localChiMinus3PrimeFactor, chiMinus3Int, h, localCharacterFactor_zero]

theorem localChiMinus3PrimeFactor_mod_one
    (p e : Nat) (h : p % 3 = 1) :
    localChiMinus3PrimeFactor p e = (e + 1 : Nat) := by
  simp [localChiMinus3PrimeFactor, chiMinus3Int, h, localCharacterFactor_one]

theorem localChiMinus3PrimeFactor_mod_two
    (p e : Nat) (h : p % 3 = 2) :
    localChiMinus3PrimeFactor p e = if Even (e + 1) then 0 else 1 := by
  simp [localChiMinus3PrimeFactor, chiMinus3Int, h, localCharacterFactor_neg_one]

/-- The divisor-character side is now locally explicit.  The remaining global
arithmetic seam is to transport these local factors through the prime
factorization of `n` and match them to the independently classified Eisenstein
norm representations. -/
structure LocalFactorBoundary where
  ramifiedCharacterFactorPaid : Bool := true
  splitCharacterFactorPaid : Bool := true
  inertAlternatingFactorPaid : Bool := true
  residueSelectsCharacterPaid : Bool := true
  globalDivisorMultiplicativityWeldPaid : Bool := false
  normPrimeSplittingClassificationPaid : Bool := false
  globalRepresentationCountPaid : Bool := false

def canonicalBoundary : LocalFactorBoundary := {}

end Dashi.EisensteinCharacterLocalFactorsExact
