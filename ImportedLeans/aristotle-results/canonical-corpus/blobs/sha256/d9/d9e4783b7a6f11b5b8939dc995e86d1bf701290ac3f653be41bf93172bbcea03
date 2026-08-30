import Mathlib

/-!
# Mirror of `DASHI/Analysis/CanonicalRationalMetric.agda`

The rational metric and its additive fast-Cauchy operations are constructed
concretely over `ℚ`.  No quotient-realization, multiplication, reciprocal, or
completeness authority is asserted here.
-/

namespace AgdaMirror.Analysis

/-- The genuinely dyadic error radius `(1/2)^n`. -/
def dyadicQ (n : Nat) : ℚ := (1 / 2 : ℚ) ^ n

@[simp] theorem dyadicQ_zero : dyadicQ 0 = 1 := by simp [dyadicQ]
@[simp] theorem dyadicQ_succ (n : Nat) : dyadicQ (n + 1) = (1 / 2 : ℚ) * dyadicQ n := by
  simp [dyadicQ, pow_succ, mul_comm]

theorem subSelfℚ (q : ℚ) : q - q = 0 := by ring

theorem absZeroℚ : |(0 : ℚ)| = 0 := abs_zero

theorem differenceSymmetry (x y : ℚ) : x - y = -(y - x) := by ring

theorem absDifferenceSymmetry (x y : ℚ) : |x - y| = |y - x| := by
  rw [differenceSymmetry, abs_neg]

theorem differenceSplit (x y z : ℚ) : x - z = (x - y) + (y - z) := by ring

theorem absDifferenceTriangle (x y z : ℚ) : |x - z| ≤ |x - y| + |y - z| := by
  rw [differenceSplit]
  exact abs_add_le _ _

theorem halfNonnegative : (0 : ℚ) ≤ 1 / 2 := by norm_num

theorem oneNonnegative : (0 : ℚ) ≤ 1 := by norm_num

theorem dyadicQNonnegative (n : Nat) : 0 ≤ dyadicQ n := by
  exact pow_nonneg (by norm_num) n

theorem zeroBelowDyadicQSum (m n : Nat) : 0 ≤ dyadicQ m + dyadicQ n := by
  exact add_nonneg (dyadicQNonnegative m) (dyadicQNonnegative n)

theorem halfDouble (q : ℚ) : (1 / 2 : ℚ) * q + (1 / 2 : ℚ) * q = q := by ring

theorem dyadicDoubleStepℚ (n : Nat) :
    dyadicQ (n + 1) + dyadicQ (n + 1) = dyadicQ n := by
  rw [dyadicQ_succ]
  exact halfDouble _

theorem dyadicOneStep (n : Nat) : dyadicQ (n + 1) ≤ dyadicQ n := by
  rw [dyadicQ_succ]
  nlinarith [dyadicQNonnegative n]

theorem dyadicBelowOne (n : Nat) : dyadicQ n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num)

theorem dyadicAntitoneℚ {m n : Nat} (h : m ≤ n) : dyadicQ n ≤ dyadicQ m := by
  exact antitone_nat_of_succ_le dyadicOneStep h

/-- Canonical fast rational representatives, using the metric from the Agda authority. -/
structure FastCauchyReal where
  approximate : Nat → ℚ
  fastCauchy : ∀ m n,
    |approximate m - approximate n| ≤ dyadicQ m + dyadicQ n

/-- The canonical rational embedding as a constant fast representative. -/
def canonicalRationalEmbedding (q : ℚ) : FastCauchyReal where
  approximate := fun _ => q
  fastCauchy := by
    intro m n
    simp only [sub_self, abs_zero]
    exact zeroBelowDyadicQSum m n

/-- A named receipt that all fields of the rational metric authority have been
constructed, rather than postulated. -/
structure RationalMetricAuthorityReceipt where
  subSelf : ∀ q : ℚ, q - q = 0
  absZero : |(0 : ℚ)| = 0
  absSymmetricDifference : ∀ x y : ℚ, |x - y| = |y - x|
  absTriangleDifference : ∀ x y z : ℚ, |x - z| ≤ |x - y| + |y - z|
  dyadicPositive : ∀ n, 0 ≤ dyadicQ n
  zeroBelowDyadicSum : ∀ m n, 0 ≤ dyadicQ m + dyadicQ n
  dyadicAntitone : ∀ {m n}, m ≤ n → dyadicQ n ≤ dyadicQ m
  dyadicDoubleStep : ∀ n, dyadicQ (n + 1) + dyadicQ (n + 1) = dyadicQ n

/-- Concrete canonical rational metric authority. -/
def canonicalRationalMetricAuthority : RationalMetricAuthorityReceipt where
  subSelf := subSelfℚ
  absZero := absZeroℚ
  absSymmetricDifference := absDifferenceSymmetry
  absTriangleDifference := absDifferenceTriangle
  dyadicPositive := dyadicQNonnegative
  zeroBelowDyadicSum := zeroBelowDyadicQSum
  dyadicAntitone := dyadicAntitoneℚ
  dyadicDoubleStep := dyadicDoubleStepℚ

theorem negDifference (a b : ℚ) : (-a) - (-b) = -(a - b) := by ring

theorem negDifferenceAbsℚ (a b : ℚ) : |(-a) - (-b)| = |a - b| := by
  rw [negDifference, abs_neg]

theorem addDifference (a b c d : ℚ) :
    (a + b) - (c + d) = (a - c) + (b - d) := by ring

theorem addDifferenceBoundℚ (a b c d : ℚ) :
    |(a + b) - (c + d)| ≤ |a - c| + |b - d| := by
  rw [addDifference]
  exact abs_add_le _ _

theorem doublePairDyadic (m n : Nat) :
    (dyadicQ (m + 1) + dyadicQ (n + 1)) +
      (dyadicQ (m + 1) + dyadicQ (n + 1)) =
    dyadicQ m + dyadicQ n := by
  rw [add_add_add_comm, dyadicDoubleStepℚ, dyadicDoubleStepℚ]

/-- Receipt for the exact additive estimates used below. -/
structure FastCauchyAdditiveLaws where
  negDifferenceAbs : ∀ a b : ℚ, |(-a) - (-b)| = |a - b|
  addDifferenceBound : ∀ a b c d : ℚ,
    |(a + b) - (c + d)| ≤ |a - c| + |b - d|
  doublePairError : ∀ m n,
    (dyadicQ (m + 1) + dyadicQ (n + 1)) +
      (dyadicQ (m + 1) + dyadicQ (n + 1)) = dyadicQ m + dyadicQ n

def canonicalFastCauchyAdditiveLaws : FastCauchyAdditiveLaws where
  negDifferenceAbs := negDifferenceAbsℚ
  addDifferenceBound := addDifferenceBoundℚ
  doublePairError := doublePairDyadic

def canonicalFastZero : FastCauchyReal := canonicalRationalEmbedding 0

def canonicalFastOne : FastCauchyReal := canonicalRationalEmbedding 1

def canonicalFastNeg (x : FastCauchyReal) : FastCauchyReal where
  approximate n := -x.approximate n
  fastCauchy m n := by
    rw [negDifferenceAbsℚ]
    exact x.fastCauchy m n

def canonicalFastAdd (x y : FastCauchyReal) : FastCauchyReal where
  approximate n := x.approximate (n + 1) + y.approximate (n + 1)
  fastCauchy m n := by
    apply le_trans (addDifferenceBoundℚ _ _ _ _)
    calc
      |x.approximate (m + 1) - x.approximate (n + 1)| +
          |y.approximate (m + 1) - y.approximate (n + 1)|
          ≤ (dyadicQ (m + 1) + dyadicQ (n + 1)) +
            (dyadicQ (m + 1) + dyadicQ (n + 1)) :=
            add_le_add (x.fastCauchy _ _) (y.fastCauchy _ _)
      _ = dyadicQ m + dyadicQ n := doublePairDyadic m n

def canonicalFastSub (x y : FastCauchyReal) : FastCauchyReal :=
  canonicalFastAdd x (canonicalFastNeg y)

end AgdaMirror.Analysis
