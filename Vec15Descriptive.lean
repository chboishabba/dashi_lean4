import Mathlib
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Order

/-!
# Lean mirror of `DASHI/Statistics/Vec15Descriptive.agda` (genuine, fully proved)

The core descriptive surface for the 15-prime carrier: total mass (`sum15`),
pointwise extrema (`max15`, `min15`), spread (`range15`), and the non-zero count
(`countNonZero15`).  This is the foundation the whole "support / rarity" chain
rests on, so we additionally prove genuine monotonicity / bound theorems for the
non-zero count.
-/

namespace AgdaMirror.Vec15Descriptive

open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Order

/-- Total mass of the carrier. -/
def sum15 (v : PrimeCarrier15) : Nat := AgdaMirror.GodelLattice.sum v

/-- Pointwise maximum over the 15 lanes. -/
def max15 (v : PrimeCarrier15) : Nat :=
  max v.e2 (max v.e3 (max v.e5 (max v.e7 (max v.e11 (max v.e13 (max v.e17
    (max v.e19 (max v.e23 (max v.e29 (max v.e31 (max v.e41 (max v.e47
      (max v.e59 v.e71)))))))))))))

/-- Pointwise minimum over the 15 lanes. -/
def min15 (v : PrimeCarrier15) : Nat :=
  min v.e2 (min v.e3 (min v.e5 (min v.e7 (min v.e11 (min v.e13 (min v.e17
    (min v.e19 (min v.e23 (min v.e29 (min v.e31 (min v.e41 (min v.e47
      (min v.e59 v.e71)))))))))))))

/-- Spread = max − min. -/
def range15 (v : PrimeCarrier15) : Nat := max15 v - min15 v

/-- `0` for `0`, `1` for any successor. -/
def countNonZeroNat : Nat → Nat
  | 0 => 0
  | _+1 => 1

/-- Number of non-zero lanes. -/
def countNonZero15 (v : PrimeCarrier15) : Nat :=
  countNonZeroNat v.e2 + countNonZeroNat v.e3 + countNonZeroNat v.e5 + countNonZeroNat v.e7 +
  countNonZeroNat v.e11 + countNonZeroNat v.e13 + countNonZeroNat v.e17 + countNonZeroNat v.e19 +
  countNonZeroNat v.e23 + countNonZeroNat v.e29 + countNonZeroNat v.e31 + countNonZeroNat v.e41 +
  countNonZeroNat v.e47 + countNonZeroNat v.e59 + countNonZeroNat v.e71

/-! ### Genuine bound / monotonicity lemmas -/

/-- The per-lane non-zero indicator is at most `1`. -/
theorem countNonZeroNat_le_one (n : Nat) : countNonZeroNat n ≤ 1 := by
  cases n <;> simp [countNonZeroNat]

/-- The per-lane non-zero indicator is at most the lane value. -/
theorem countNonZeroNat_le_self (n : Nat) : countNonZeroNat n ≤ n := by
  cases n <;> simp [countNonZeroNat]

/-- `countNonZeroNat` is monotone. -/
theorem countNonZeroNat_mono {m n : Nat} (h : m ≤ n) :
    countNonZeroNat m ≤ countNonZeroNat n := by
  cases m with
  | zero => simp [countNonZeroNat]
  | succ k =>
    cases n with
    | zero => omega
    | succ j => simp [countNonZeroNat]

/-- The non-zero count never exceeds 15 (the number of lanes). -/
theorem countNonZero15_le_15 (v : PrimeCarrier15) : countNonZero15 v ≤ 15 := by
  unfold countNonZero15
  have h := fun n => countNonZeroNat_le_one n
  have := h v.e2; have := h v.e3; have := h v.e5; have := h v.e7; have := h v.e11
  have := h v.e13; have := h v.e17; have := h v.e19; have := h v.e23; have := h v.e29
  have := h v.e31; have := h v.e41; have := h v.e47; have := h v.e59; have := h v.e71
  omega

/-- The non-zero count is bounded by the total mass. -/
theorem countNonZero15_le_sum15 (v : PrimeCarrier15) : countNonZero15 v ≤ sum15 v := by
  unfold countNonZero15 sum15 AgdaMirror.GodelLattice.sum
  have h := fun n => countNonZeroNat_le_self n
  have := h v.e2; have := h v.e3; have := h v.e5; have := h v.e7; have := h v.e11
  have := h v.e13; have := h v.e17; have := h v.e19; have := h v.e23; have := h v.e29
  have := h v.e31; have := h v.e41; have := h v.e47; have := h v.e59; have := h v.e71
  omega

/-- The minimum is `≤` the maximum. -/
theorem min15_le_max15 (v : PrimeCarrier15) : min15 v ≤ max15 v := by
  unfold min15 max15
  cases v
  apply le_trans (min_le_left _ _)
  apply le_max_left

end AgdaMirror.Vec15Descriptive
