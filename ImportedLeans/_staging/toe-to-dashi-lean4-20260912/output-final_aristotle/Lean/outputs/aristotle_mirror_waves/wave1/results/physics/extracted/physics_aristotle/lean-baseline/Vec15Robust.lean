import Mathlib
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Order
import AgdaMirror.Vec15Descriptive

/-!
# Lean mirror of `DASHI/Statistics/Vec15Robust.agda` (genuine, fully proved)

The robust / outlier surface for the 15-prime carrier: IQR-based fences, Tukey
and Hampel masks, winsorization, a trimmed mean on the sorted middle block, and
the median absolute deviation.  The honest robust summaries (`tukeySummary15`,
`hampelSummary15`, `winsorizedSummary15`) are concrete aliases over the real
operators, and we prove the genuine `zeroCarrier` collapse lemmas plus the
constant-carrier sanity lemmas (`max15`, `min15`, fences, `mad`).
-/

namespace AgdaMirror.Vec15Robust

open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Order
open AgdaMirror.Vec15Descriptive

/-- The constant carrier with every lane equal to `n`. -/
def constant15 (n : Nat) : PrimeCarrier15 := replicate n

/-- Interquartile range. -/
def iqr15 (v : PrimeCarrier15) : Nat := upperQuartile15 v - lowerQuartile15 v

/-- A Tukey fence: lower and upper bound. -/
structure TukeyFence15 where
  lowerFence15 : Nat
  upperFence15 : Nat

/-- A lightweight Tukey-style fence based on the IQR. -/
def tukeyFence15 (v : PrimeCarrier15) : TukeyFence15 :=
  ⟨lowerQuartile15 v - iqr15 v, upperQuartile15 v + iqr15 v⟩

/-- Boolean negation. -/
def notBool : Bool → Bool
  | true => false
  | false => true

/-- Boolean conjunction (matching the Agda `andBool`). -/
def andBool : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

/-- Boolean `≤`. -/
def leqNatBool (x y : Nat) : Bool := decide (x ≤ y)

/-- Mask the lanes that fall *outside* the `[lo, hi]` fence. -/
def outsideFenceMask15 (lo hi : Nat) (v : PrimeCarrier15) : Vec15 Bool :=
  let f := fun a => notBool (andBool (leqNatBool lo a) (leqNatBool a hi))
  ⟨f v.e2, f v.e3, f v.e5, f v.e7, f v.e11, f v.e13, f v.e17, f v.e19,
   f v.e23, f v.e29, f v.e31, f v.e41, f v.e47, f v.e59, f v.e71⟩

/-- Median absolute deviation. -/
def mad15 (v : PrimeCarrier15) : Nat := median15 (map15 (absDiffNat (median15 v)) v)

/-- Tukey outlier mask. -/
def tukeyOutlierMask15 (v : PrimeCarrier15) : Vec15 Bool :=
  outsideFenceMask15 (tukeyFence15 v).lowerFence15 (tukeyFence15 v).upperFence15 v

/-- The Hampel fence is centered on the median and scaled by `3 * MAD`. -/
def hampelOutlierMask15 (v : PrimeCarrier15) : Vec15 Bool :=
  outsideFenceMask15 (median15 v - 3 * mad15 v) (median15 v + 3 * mad15 v) v

/-- Winsorize: clamp every lane into the Tukey fence. -/
def winsorize15 (v : PrimeCarrier15) : PrimeCarrier15 :=
  map15 (clampNat (tukeyFence15 v).lowerFence15 (tukeyFence15 v).upperFence15) v

/-- Sum of the middle 11 entries of a length-15 sorted list. -/
def middle11Sum : List Nat → Nat
  | _x1 :: _x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: _x14 :: _x15 :: [] =>
      x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13
  | _ => 0

/-- Trimmed mean over the sorted middle block. -/
def trimmedMean15 (v : PrimeCarrier15) : Nat :=
  middle11Sum (sortAsc (toList15 v)) / 11

/-! ### Constant-carrier sanity lemmas -/

theorem max15_constant (n : Nat) : max15 (constant15 n) = n := by
  simp [max15, constant15, replicate]

theorem min15_constant (n : Nat) : min15 (constant15 n) = n := by
  simp [min15, constant15, replicate]

theorem lowerQuartile15_constant (n : Nat) : lowerQuartile15 (constant15 n) = n := by
  simp [lowerQuartile15, selectAt15, constant15, replicate, toList15, sortAsc, insertAsc,
    nthOrZero]

theorem median15_constant (n : Nat) : median15 (constant15 n) = n := by
  simp [median15, selectAt15, constant15, replicate, toList15, sortAsc, insertAsc, nthOrZero]

theorem upperQuartile15_constant (n : Nat) : upperQuartile15 (constant15 n) = n := by
  simp [upperQuartile15, selectAt15, constant15, replicate, toList15, sortAsc, insertAsc,
    nthOrZero]

theorem range15_constant_zero (n : Nat) : range15 (constant15 n) = 0 := by
  simp [range15, max15_constant, min15_constant]

theorem absDiffNat_self (n : Nat) : absDiffNat n n = 0 := by
  unfold absDiffNat; split <;> omega

theorem tukeyFence15_constant (n : Nat) : tukeyFence15 (constant15 n) = ⟨n, n⟩ := by
  simp [tukeyFence15, iqr15, lowerQuartile15_constant, upperQuartile15_constant]

theorem winsorize15_constant (n : Nat) : winsorize15 (constant15 n) = constant15 n := by
  unfold winsorize15
  rw [tukeyFence15_constant]
  simp [map15, constant15, replicate, map, clampNat]

theorem mad15_constant_zero (n : Nat) : mad15 (constant15 n) = 0 := by
  unfold mad15
  rw [median15_constant]
  have hmap : map15 (absDiffNat n) (constant15 n) = constant15 0 := by
    simp [map15, constant15, replicate, map, absDiffNat_self]
  rw [hmap, median15_constant]

/-! ### Honest robust summaries -/

def tukeySummary15 : PrimeCarrier15 → Nat := range15
def hampelSummary15 : PrimeCarrier15 → Nat := mad15
def winsorizedSummary15 (v : PrimeCarrier15) : Nat := sum15 (winsorize15 v)

/-! ### Zero-carrier collapse lemmas -/

theorem selectMask15_zeroCarrier (threshold : Nat) :
    selectMask15 threshold zeroCarrier15 =
      ⟨true, true, true, true, true, true, true, true, true, true, true, true, true, true, true⟩ := by
  simp [selectMask15, zeroCarrier15, replicate, natLeqBool]

theorem rank15_zeroCarrier (threshold : Nat) : rank15 threshold zeroCarrier15 = 15 := by
  simp [rank15, selectMask15_zeroCarrier, countMask15, countBool]

theorem countNonZero15_zeroCarrier : countNonZero15 zeroCarrier15 = 0 := by decide

theorem tukeyOutlierMask15_zeroCarrier : tukeyOutlierMask15 zeroCarrier15 =
    ⟨false, false, false, false, false, false, false, false, false, false, false, false, false, false, false⟩ := by
  decide

theorem hampelOutlierMask15_zeroCarrier : hampelOutlierMask15 zeroCarrier15 =
    ⟨false, false, false, false, false, false, false, false, false, false, false, false, false, false, false⟩ := by
  decide

theorem winsorize15_zeroCarrier : winsorize15 zeroCarrier15 = zeroCarrier15 := by decide

theorem mad15_zeroCarrier : mad15 zeroCarrier15 = 0 := by decide

theorem tukeySummary15_zeroCarrier : tukeySummary15 zeroCarrier15 = 0 := by decide

theorem hampelSummary15_zeroCarrier : hampelSummary15 zeroCarrier15 = 0 := by decide

theorem winsorizedSummary15_zeroCarrier : winsorizedSummary15 zeroCarrier15 = 0 := by decide

end AgdaMirror.Vec15Robust
