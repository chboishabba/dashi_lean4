import Integration.EisensteinJZeroInertPrimeEulerExact
import Integration.EisensteinLatticeCounting

namespace Dashi.EisensteinJZeroSplitSevenExact

open Dashi.EisensteinJZeroInertPrimeEulerExact
open Dashi.EisensteinLatticeCounting

/-- Exact affine point count on the same `j=0` cubic at the first split prime. -/
theorem splitSevenAffineCount : Fintype.card (JZeroAffinePoint 7) = 11 := by
  native_decide

/-- Add the unique point at infinity. -/
def splitSevenProjectiveCount : Nat := Fintype.card (JZeroAffinePoint 7) + 1

/-- `a₇ = 8 - #E(F₇)`. -/
def splitSevenFrobeniusTrace : Int := 8 - (splitSevenProjectiveCount : Int)

/-- Coefficients of `1 - a₇ T + 7T²`. -/
def splitSevenLocalEulerPolynomial : Int × Int × Int :=
  (1, -splitSevenFrobeniusTrace, 7)

theorem splitSevenProjectiveCount_eq_twelve : splitSevenProjectiveCount = 12 := by
  native_decide

theorem splitSevenFrobeniusTrace_eq_neg_four : splitSevenFrobeniusTrace = -4 := by
  native_decide

theorem splitSevenLocalEulerPolynomial_exact :
    splitSevenLocalEulerPolynomial = (1, 4, 7) := by
  native_decide

/-- Field trace of `a+bω` from `Q(ω)` to `Q`, in the integral coefficient
basis: `(a+bω)+(a+bω²)=2a-b`. -/
def eisensteinFieldTrace (a b : Int) : Int := 2 * a - b

/-- A norm-seven factor whose trace is exactly the Frobenius trace selected by
this concrete `j=0` curve. -/
theorem normalizedSevenNorm : eisensteinNorm (-3) (-2) = 7 := by
  native_decide

theorem normalizedSevenTrace : eisensteinFieldTrace (-3) (-2) = -4 := by
  native_decide

theorem normalizedSevenMatchesFrobeniusTrace :
    eisensteinNorm (-3) (-2) = 7 ∧
      eisensteinFieldTrace (-3) (-2) = splitSevenFrobeniusTrace := by
  constructor <;> native_decide

/-- Another norm-seven Eisenstein element has a different field trace.  Thus
`N(π)=p` is not enough to recover `a_p`; the unit/conductor normalization is
additional arithmetic data. -/
theorem alternateSevenNorm : eisensteinNorm 3 1 = 7 := by
  native_decide

theorem alternateSevenTrace : eisensteinFieldTrace 3 1 = 5 := by
  native_decide

theorem normSevenDoesNotDetermineTrace :
    eisensteinNorm (-3) (-2) = eisensteinNorm 3 1 ∧
      eisensteinFieldTrace (-3) (-2) ≠ eisensteinFieldTrace 3 1 := by
  constructor <;> native_decide

/-- The first split row therefore exhibits both sides of the CM boundary:
there exists a correctly normalized norm-p factor, but norm and splitting data
alone do not canonically select it. -/
structure SplitSevenBoundary where
  literalSplitPrimePointCountPaid : Bool := true
  literalSplitPrimeTracePaid : Bool := true
  matchingNormTraceWitnessPaid : Bool := true
  normAloneInsufficientReceiptPaid : Bool := true
  canonicalUnitNormalizationPaid : Bool := false
  allSplitPrimeTraceFormulaPaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticHeckeLSeriesIdentityPaid : Bool := false

/-- Exact split-prime frontier. -/
def canonicalBoundary : SplitSevenBoundary := {}

end Dashi.EisensteinJZeroSplitSevenExact
