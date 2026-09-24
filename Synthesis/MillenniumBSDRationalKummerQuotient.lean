import Synthesis.MillenniumBSDRationalSquareClassQuotient
import Mathlib.Tactic

/-!
# Rational Kummer map into the literal square-class quotient

This is the quotient-level counterpart of the Agda map for
`E : y² = x³ - x`.  On the ordinary affine locus `x ≠ 0,1` it sends

`(x,y) ↦ ([x],[x-1])`

in the actual Lean quotient `(ℚ*/ℚ*²)²`.  The three exceptional projective
points receive the standard representatives used by the Agda torsion
dictionary.
-/

namespace Synthesis.Millennium.BSD

structure RationalAffinePoint where
  x : ℚ
  y : ℚ
  onCurve : y ^ 2 = x ^ 3 - x

structure OrdinaryKummerPoint extends RationalAffinePoint where
  x_ne_zero : x ≠ 0
  x_ne_one : x ≠ 1

def ordinaryKummer
    (p : OrdinaryKummerPoint) :
    RatSquareClass × RatSquareClass :=
  ( squareClassOf ⟨p.x, p.x_ne_zero⟩
  , squareClassOf ⟨p.x - 1, sub_ne_zero.mpr p.x_ne_one⟩ )

inductive RationalTwoTorsionPoint
  | infinity
  | zero
  | one
  | negOne
deriving DecidableEq

def torsionKummer :
    RationalTwoTorsionPoint →
    RatSquareClass × RatSquareClass
  | .infinity => (squareClassOf oneNZ, squareClassOf oneNZ)
  | .zero => (squareClassOf negOneNZ, squareClassOf negOneNZ)
  | .one => (squareClassOf oneNZ, squareClassOf twoNZ)
  | .negOne => (squareClassOf negOneNZ, squareClassOf negTwoNZ)

def finiteSeedBits :
    RationalTwoTorsionPoint → Bool × ZMod 2
  | .infinity => (false, 0)
  | .zero => (true, 0)
  | .one => (false, 1)
  | .negOne => (true, 1)

def quotientBits
    (pair : RatSquareClass × RatSquareClass) :
    Bool × ZMod 2 :=
  (squareClassSignBit pair.1, squareClassV2Parity pair.2)

theorem torsionKummer_bits
    (p : RationalTwoTorsionPoint) :
    quotientBits (torsionKummer p) = finiteSeedBits p := by
  cases p <;>
    simp [quotientBits, torsionKummer, finiteSeedBits,
      oneNZ, negOneNZ, twoNZ, negTwoNZ,
      signBit_one, signBit_neg_one,
      v2Parity_one, v2Parity_neg_one,
      v2Parity_two, v2Parity_neg_two]

def minusOnePoint : OrdinaryKummerPoint where
  x := -1
  y := 0
  onCurve := by norm_num
  x_ne_zero := by norm_num
  x_ne_one := by norm_num

theorem minusOne_ordinary_matches_torsion :
    ordinaryKummer minusOnePoint = torsionKummer .negOne := by
  rfl

end Synthesis.Millennium.BSD
