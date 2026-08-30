import Mathlib
import AgdaMirror.GodelLattice

/-!
# Lean mirror of `DASHI/Statistics/Vec15Order.agda` (genuine, fully proved)

Order, selection and threshold-mask helpers for the 15-lane `Nat` carrier:
insertion sort on the concrete 15-element list view, indexed selection,
threshold masks, rank counts, and the small clamp / absolute-difference helpers
with their genuine `≤` lemmas.  All constructive and fully proved.
-/

namespace AgdaMirror.Vec15Order

open AgdaMirror.GodelLattice

/-- The 15-lane natural-number carrier. -/
abbrev PrimeCarrier15 : Type := Vec15 Nat

/-- The all-zero carrier. -/
def zeroCarrier15 : PrimeCarrier15 := replicate 0

/-- A demo carrier whose lanes are already `0,1,…,14`. -/
def demoSortedCarrier15 : PrimeCarrier15 :=
  ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14⟩

/-- The concrete 15-element list view, in prime order. -/
def toList15 (v : PrimeCarrier15) : List Nat :=
  [v.e2, v.e3, v.e5, v.e7, v.e11, v.e13, v.e17, v.e19, v.e23, v.e29,
   v.e31, v.e41, v.e47, v.e59, v.e71]

/-- Insert `x` into an ascending list, keeping it ascending. -/
def insertAsc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertAsc x ys

/-- Insertion sort, ascending. -/
def sortAsc : List Nat → List Nat
  | [] => []
  | x :: xs => insertAsc x (sortAsc xs)

theorem sortAsc_demoSortedCarrier15 :
    sortAsc (toList15 demoSortedCarrier15) = toList15 demoSortedCarrier15 := by
  decide

/-- Indexed lookup returning `0` past the end. -/
def nthOrZero : Nat → List Nat → Nat
  | _, [] => 0
  | 0, x :: _ => x
  | (n+1), _ :: xs => nthOrZero n xs

/-- Select the `n`-th smallest lane. -/
def selectAt15 (n : Nat) (v : PrimeCarrier15) : Nat :=
  nthOrZero n (sortAsc (toList15 v))

theorem selectAt15_demoSortedCarrier15_7 :
    selectAt15 7 demoSortedCarrier15 = 7 := by decide

theorem selectAt15_demoSortedCarrier15_14 :
    selectAt15 14 demoSortedCarrier15 = 14 := by decide

/-- Lower quartile = 4th order statistic. -/
def lowerQuartile15 : PrimeCarrier15 → Nat := selectAt15 3

/-- Median = 8th order statistic. -/
def median15 : PrimeCarrier15 → Nat := selectAt15 7

/-- Upper quartile = 12th order statistic. -/
def upperQuartile15 : PrimeCarrier15 → Nat := selectAt15 11

/-- Boolean `≤`. -/
def natLeqBool (x y : Nat) : Bool := decide (x ≤ y)

/-- Threshold mask: `true` exactly where the lane is `≤ threshold`. -/
def selectMask15 (threshold : Nat) (v : PrimeCarrier15) : Vec15 Bool :=
  ⟨natLeqBool v.e2 threshold, natLeqBool v.e3 threshold, natLeqBool v.e5 threshold,
   natLeqBool v.e7 threshold, natLeqBool v.e11 threshold, natLeqBool v.e13 threshold,
   natLeqBool v.e17 threshold, natLeqBool v.e19 threshold, natLeqBool v.e23 threshold,
   natLeqBool v.e29 threshold, natLeqBool v.e31 threshold, natLeqBool v.e41 threshold,
   natLeqBool v.e47 threshold, natLeqBool v.e59 threshold, natLeqBool v.e71 threshold⟩

theorem selectMask15_demoSortedCarrier15_7 :
    selectMask15 7 demoSortedCarrier15 =
      ⟨true, true, true, true, true, true, true, true,
       false, false, false, false, false, false, false⟩ := by decide

/-- `1` for `true`, `0` for `false`. -/
def countBool : Bool → Nat
  | false => 0
  | true => 1

/-- Count the `true` lanes of a Boolean mask. -/
def countMask15 (b : Vec15 Bool) : Nat :=
  countBool b.e2 + countBool b.e3 + countBool b.e5 + countBool b.e7 + countBool b.e11 +
  countBool b.e13 + countBool b.e17 + countBool b.e19 + countBool b.e23 + countBool b.e29 +
  countBool b.e31 + countBool b.e41 + countBool b.e47 + countBool b.e59 + countBool b.e71

/-- Rank = number of lanes `≤ threshold`. -/
def rank15 (threshold : Nat) (v : PrimeCarrier15) : Nat :=
  countMask15 (selectMask15 threshold v)

theorem rank15_demoSortedCarrier15_7 :
    rank15 7 demoSortedCarrier15 = 8 := by decide

/-- Absolute difference on `Nat`. -/
def absDiffNat (x y : Nat) : Nat := if x ≤ y then y - x else x - y

/-- Pointwise map on the carrier. -/
def map15 (f : Nat → Nat) (v : PrimeCarrier15) : PrimeCarrier15 := map f v

/-- Clamp `n` to `[lo, hi]`. -/
def clampNat (lo hi n : Nat) : Nat :=
  if lo ≤ n then (if n ≤ hi then n else hi) else lo

theorem clampNat_le_hi (lo hi n : Nat) (h : lo ≤ hi) : clampNat lo hi n ≤ hi := by
  unfold clampNat
  by_cases h1 : lo ≤ n <;> by_cases h2 : n ≤ hi <;> simp [h1, h2, h]

theorem clampNat_ge_lo (lo hi n : Nat) (h : lo ≤ hi) : lo ≤ clampNat lo hi n := by
  unfold clampNat
  by_cases h1 : lo ≤ n <;> by_cases h2 : n ≤ hi <;> simp [h1, h2, h]

end AgdaMirror.Vec15Order
