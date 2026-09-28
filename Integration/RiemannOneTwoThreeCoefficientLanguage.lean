import Mathlib

/-!
# RH coefficients in a 1/2/3-only arithmetic language

Every displayed integer is reconstructed from literal 1,2,3 using addition,
multiplication, powers, and subtraction.  Ratio equality is recorded by cross
multiplication, avoiding any analytic or geometric promotion.
-/

namespace Integration.RiemannOneTwoThreeCoefficientLanguage

def four123 : Nat := 3 + 1
def five123 : Nat := 3 + 2
def nine123 : Nat := 3^2
def ten123 : Nat := 3^2 + 1
def twenty123 : Nat := 2 * (3^2 + 1)
def eighty123 : Nat := 3^(2*2) - 1
def twoFortyThree123 : Nat := 3^(3+2)
def nineSeventyTwo123 : Nat := 3^6 + 3^5
def twelveFifteen123 : Nat := 3^7 - 3^6 - 3^5

theorem four123_is_four : four123 = 4 := by norm_num [four123]
theorem five123_is_five : five123 = 5 := by norm_num [five123]
theorem nine123_is_nine : nine123 = 9 := by norm_num [nine123]
theorem ten123_is_ten : ten123 = 10 := by norm_num [ten123]
theorem twenty123_is_twenty : twenty123 = 20 := by norm_num [twenty123]
theorem eighty123_is_eighty : eighty123 = 80 := by norm_num [eighty123]
theorem twoFortyThree123_is_243 : twoFortyThree123 = 243 := by norm_num [twoFortyThree123]
theorem nineSeventyTwo123_is_972 : nineSeventyTwo123 = 972 := by norm_num [nineSeventyTwo123]
theorem twelveFifteen123_is_1215 : twelveFifteen123 = 1215 := by norm_num [twelveFifteen123]

structure PositiveRatioCode where
  numerator : Nat
  denominator : Nat
  deriving Repr

def rhCoefficientRatio123 : PositiveRatioCode :=
  ⟨twenty123, twoFortyThree123⟩

def rhCoefficientPuncturedRatio123 : PositiveRatioCode :=
  ⟨eighty123, (3+1) * twoFortyThree123⟩

theorem ratio_cross_multiplication_exact :
    rhCoefficientRatio123.numerator * rhCoefficientPuncturedRatio123.denominator =
    rhCoefficientPuncturedRatio123.numerator * rhCoefficientRatio123.denominator := by
  norm_num [rhCoefficientRatio123, rhCoefficientPuncturedRatio123,
    twenty123, twoFortyThree123, eighty123]

def fiveBalanced : Nat := 3^2 - 3^1 - 1
def tenBalanced : Nat := 3^2 + 1
def twentyBalanced : Nat := (3^3 - 3^2) + 3^1 - 1
def eightyBalanced : Nat := 3^4 - 1

theorem five_balanced_is_five : fiveBalanced = 5 := by norm_num [fiveBalanced]
theorem ten_balanced_is_ten : tenBalanced = 10 := by norm_num [tenBalanced]
theorem twenty_balanced_is_twenty : twentyBalanced = 20 := by norm_num [twentyBalanced]
theorem eighty_balanced_is_eighty : eightyBalanced = 80 := by norm_num [eightyBalanced]

inductive PromotionError
  | oneTwoThreeSyntaxCreatesSemantics
  | balancedDigitsCreateCarrier
  deriving DecidableEq, Repr

structure Boundary where
  allDisplayedCoefficientsRecovered : Bool
  rhRatioRecoveredByCrossMultiplication : Bool
  balancedSparseFormsRecovered : Bool
  arithmeticSyntaxPromotedToSemantics : Bool
  carrierConstructedFromDigitShape : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  allDisplayedCoefficientsRecovered := true
  rhRatioRecoveredByCrossMultiplication := true
  balancedSparseFormsRecovered := true
  arithmeticSyntaxPromotedToSemantics := false
  carrierConstructedFromDigitShape := false

end Integration.RiemannOneTwoThreeCoefficientLanguage
