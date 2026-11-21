import Integration.EisensteinJZeroPointCMExact
import Integration.EisensteinLatticeCounting
import Mathlib.Data.ZMod.Basic

namespace Dashi.EisensteinJZeroLocalEulerExact

open Dashi.EisensteinLatticeCounting

/-- Literal affine `F₅` point count for the reduction of `y²=x³+1`. -/
def affinePointCount5 : Nat :=
  ((Finset.univ : Finset (ZMod 5 × ZMod 5)).filter fun xy =>
    xy.2 ^ 2 = xy.1 ^ 3 + 1).card

/-- Add the unique projective point at infinity. -/
def projectivePointCount5 : Nat := affinePointCount5 + 1

/-- `a₅ = 5 + 1 - #E(F₅)`, kept signed to avoid truncated subtraction. -/
def frobeniusTrace5 : Int := 6 - (projectivePointCount5 : Int)

/-- Coefficients `(1,-a₅,5)` of the local Euler polynomial
`1 - a₅ T + 5 T²`. -/
def localEulerAt5 : Int × Int × Int := (1, -frobeniusTrace5, 5)

theorem affinePointCount5_eq_five : affinePointCount5 = 5 := by
  native_decide

theorem projectivePointCount5_eq_six : projectivePointCount5 = 6 := by
  native_decide

/-- The exact inert-prime trace-zero row on the same `j=0` cubic. -/
theorem inertFiveTraceZero : frobeniusTrace5 = 0 := by
  native_decide

/-- The corresponding local polynomial is exactly `1 + 5T²`. -/
theorem inertFiveLocalFactor : localEulerAt5 = (1, 0, 5) := by
  native_decide

/-- The prime used by the exact finite row is in the inert mod-three residue
class. -/
theorem five_is_inert_residue : 5 % 3 = 2 := by
  native_decide

/-- The same residue is seen by the already-owned quadratic character. -/
theorem chiMinus3_five : chiMinus3Int 5 = -1 := by
  native_decide

/-- Claim-strength boundary: one literal inert Euler row is paid.  The theorem
for every inert prime, split-prime traces, Hecke-character normalization and the
infinite Euler product remain distinct arithmetic obligations. -/
structure LocalEulerBoundary where
  literalF5PointEnumerationPaid : Bool := true
  inertResidueSamePrimePaid : Bool := true
  inertTraceZeroAtFivePaid : Bool := true
  allInertPrimeTraceZeroPaid : Bool := false
  splitPrimeTraceFormulaPaid : Bool := false
  heckeCharacterNormalizationPaid : Bool := false
  globalEllipticHeckeLSeriesIdentityPaid : Bool := false

/-- Exact current local-Euler frontier. -/
def canonicalBoundary : LocalEulerBoundary := {}

end Dashi.EisensteinJZeroLocalEulerExact
