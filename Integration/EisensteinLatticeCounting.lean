import Mathlib

namespace Dashi.EisensteinLatticeCounting

/-!
# Eisenstein lattice counting

One triangular/A₂-style carrier supports several different observables.  This
owner keeps graph-radius counts, wedge counts, Pascal path multiplicities and
quadratic-norm shell counts distinct.

The arithmetic shell function is the constructive divisor-side formula

`6 * ∑_{d ∣ n} χ₋₃(d)`

implemented as the difference between divisors congruent to `1` and `2`
modulo `3`.
-/

------------------------------------------------------------------------
-- Triangular / hex graph-radius observables.
------------------------------------------------------------------------

def triangularNumber : Nat → Nat
  | 0 => 0
  | n + 1 => triangularNumber n + (n + 1)

def hexShellCount : Nat → Nat
  | 0 => 1
  | n + 1 => 6 * (n + 1)

def hexBallCount (k : Nat) : Nat := 1 + 6 * triangularNumber k

def wedgeRowCount (k : Nat) : Nat := k + 1

def wedgeTriangleCount (k : Nat) : Nat := triangularNumber (k + 1)

def binaryPathTotal : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * binaryPathTotal n

------------------------------------------------------------------------
-- χ₋₃ divisor shell law.
------------------------------------------------------------------------

def positiveDivisors (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter fun d => 0 < d ∧ d ∣ n

def chiMinus3Positive (d : Nat) : Nat :=
  if d % 3 = 1 then 1 else 0

def chiMinus3Negative (d : Nat) : Nat :=
  if d % 3 = 2 then 1 else 0

def chiMinus3PositiveDivisorCount (n : Nat) : Nat :=
  ∑ d ∈ positiveDivisors n, chiMinus3Positive d

def chiMinus3NegativeDivisorCount (n : Nat) : Nat :=
  ∑ d ∈ positiveDivisors n, chiMinus3Negative d

def chiMinus3DivisorBalance (n : Nat) : Nat :=
  chiMinus3PositiveDivisorCount n - chiMinus3NegativeDivisorCount n

def eisensteinDivisorShellCount (n : Nat) : Nat :=
  6 * chiMinus3DivisorBalance n

------------------------------------------------------------------------
-- Independent finite geometric producer.
--
-- This literally counts integer pairs in the square [-n,n]^2 satisfying
-- Q(a,b)=a^2-a*b+b^2=n.  It is intentionally separate from the divisor
-- formula.  The first ten shells are then checked independently below.
------------------------------------------------------------------------

def eisensteinNorm (a b : Int) : Int := a * a - a * b + b * b

def geometricNormShellCount (n : Nat) : Nat :=
  let r : Int := n
  let coords : Finset Int := Finset.Icc (-r) r
  ((coords.product coords).filter fun p => eisensteinNorm p.1 p.2 = r).card

------------------------------------------------------------------------
-- Exact finite parity and non-collapse receipts.
------------------------------------------------------------------------

theorem triangularTen : triangularNumber 10 = 55 := by native_decide

theorem hexBallThree : hexBallCount 3 = 37 := by native_decide

theorem wedgeThroughThree : wedgeTriangleCount 3 = 10 := by native_decide

theorem pascalFourTwo : Nat.choose 4 2 = 6 := by native_decide

theorem divisorShellOneToTen :
    [eisensteinDivisorShellCount 1,
     eisensteinDivisorShellCount 2,
     eisensteinDivisorShellCount 3,
     eisensteinDivisorShellCount 4,
     eisensteinDivisorShellCount 5,
     eisensteinDivisorShellCount 6,
     eisensteinDivisorShellCount 7,
     eisensteinDivisorShellCount 8,
     eisensteinDivisorShellCount 9,
     eisensteinDivisorShellCount 10]
    = [6, 0, 6, 6, 0, 0, 12, 0, 6, 0] := by
  native_decide

theorem geometricShellOneToTen :
    [geometricNormShellCount 1,
     geometricNormShellCount 2,
     geometricNormShellCount 3,
     geometricNormShellCount 4,
     geometricNormShellCount 5,
     geometricNormShellCount 6,
     geometricNormShellCount 7,
     geometricNormShellCount 8,
     geometricNormShellCount 9,
     geometricNormShellCount 10]
    = [6, 0, 6, 6, 0, 0, 12, 0, 6, 0] := by
  native_decide

theorem geometricDivisorParityOneToTen :
    [geometricNormShellCount 1,
     geometricNormShellCount 2,
     geometricNormShellCount 3,
     geometricNormShellCount 4,
     geometricNormShellCount 5,
     geometricNormShellCount 6,
     geometricNormShellCount 7,
     geometricNormShellCount 8,
     geometricNormShellCount 9,
     geometricNormShellCount 10]
    = [eisensteinDivisorShellCount 1,
       eisensteinDivisorShellCount 2,
       eisensteinDivisorShellCount 3,
       eisensteinDivisorShellCount 4,
       eisensteinDivisorShellCount 5,
       eisensteinDivisorShellCount 6,
       eisensteinDivisorShellCount 7,
       eisensteinDivisorShellCount 8,
       eisensteinDivisorShellCount 9,
       eisensteinDivisorShellCount 10] := by
  native_decide

theorem geometricZeroIsOne : geometricNormShellCount 0 = 1 := by
  native_decide

theorem divisorZeroIsZero : eisensteinDivisorShellCount 0 = 0 := by
  native_decide

theorem zeroIsExceptional :
    geometricNormShellCount 0 ≠ eisensteinDivisorShellCount 0 := by
  native_decide

theorem hexShell_ne_normShell_at_two :
    hexShellCount 2 ≠ eisensteinDivisorShellCount 2 := by
  native_decide

theorem wedgeTriangle_ne_binaryPathTotal_at_three :
    wedgeTriangleCount 3 ≠ binaryPathTotal 3 := by
  native_decide

------------------------------------------------------------------------
-- General same-object bridge obligation, correctly scoped to n >= 1.
------------------------------------------------------------------------

structure EisensteinNormRepresentationBridge where
  representationCount : Nat → Nat
  representationCount_eq_divisorLaw_positive :
    ∀ n, representationCount (n + 1) = eisensteinDivisorShellCount (n + 1)

structure CountingBoundary where
  triangularAndHexExecutable : Bool := true
  pascalPathExecutable : Bool := true
  chiMinus3DivisorShellExecutable : Bool := true
  independentFiniteNormEnumeratorExecutable : Bool := true
  graphRadiusShellEqualsNormShell : Bool := false
  wedgeTriangleEqualsPascalPathTotal : Bool := false
  positiveNGeometricDivisorRepresentationPaid : Bool := false
  zeroNormHandledByPositiveDivisorLaw : Bool := false
  ternaryCountImpliesExceptionalGroupIdentification : Bool := false
  modularEisensteinSeriesIdentifiedWithIntegerShells : Bool := false

/-- Canonical claim-strength receipt for this owner. -/
def canonicalBoundary : CountingBoundary := {}

end Dashi.EisensteinLatticeCounting
