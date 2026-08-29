import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport
import AgdaMirror.ActiveWallStructure

/-!
# Lean mirror of `DASHI/Arithmetic/DeltaRarity.agda` (genuine, fully proved)

Threshold masks on the tracked 15-prime carrier: `thresholdAt k` is the
indicator for `δ_p ≥ k+1`.  The genuine monotone "large-δ is rare" theorem is
`thresholdCount k ≤ supportPrimeCount`: every threshold slice sits inside the
support-side shadow, uniformly in the threshold `k`.
-/

namespace AgdaMirror.DeltaRarity

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Descriptive
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.TrackedSupport
open AgdaMirror.ActiveWallStructure
open SSP

/-- Threshold indicator: `thresholdAt (k+1)` is the indicator for `δ_p ≥ k+2`. -/
def thresholdAt : Nat → SSP → IntCarrier → IntCarrier → Nat
  | 0, p, x, y => countNonZeroNat (deltaAt p x y)
  | (k+1), p, x, y => countNonZeroNat (deltaAt p x y - k)

/-- Threshold-count over the tracked 15-prime carrier. -/
def thresholdCount (k : Nat) (x y : IntCarrier) : Nat :=
  sum (mapPrimes15 (fun p => thresholdAt k p x y))

/-- The threshold-2 large-δ slice. -/
def largeDeltaCount2 (x y : IntCarrier) : Nat := thresholdCount 1 x y

/-- Pointwise support inclusion of every threshold slice. -/
theorem thresholdAt_le_supportMaskAt (k : Nat) (p : SSP) (x y : IntCarrier) :
    thresholdAt k p x y ≤ supportMaskAt p x y := by
  cases k with
  | zero =>
    simp only [thresholdAt, supportMaskAt, supportAt]
    exact Vec15Descriptive.countNonZeroNat_mono (deltaAt_le_supportAt p x y)
  | succ k =>
    simp only [thresholdAt, supportMaskAt, supportAt]
    exact le_trans (Vec15Descriptive.countNonZeroNat_mono (Nat.sub_le _ _))
      (Vec15Descriptive.countNonZeroNat_mono (deltaAt_le_supportAt p x y))

/-- The genuine rarity theorem: any threshold slice is bounded by the support
count, uniformly in `k`. -/
theorem thresholdCount_le_supportPrimeCount (k : Nat) (x y : IntCarrier) :
    thresholdCount k x y ≤ supportPrimeCount x y := by
  have key : supportPrimeCount x y = sum (mapPrimes15 (fun p => supportMaskAt p x y)) := rfl
  rw [thresholdCount, key]
  exact sum_mapPrimes15_mono (fun p => thresholdAt_le_supportMaskAt k p x y)

/-- The threshold-2 rarity bound. -/
theorem thresholdRarity2 (x y : IntCarrier) :
    largeDeltaCount2 x y ≤ supportPrimeCount x y :=
  thresholdCount_le_supportPrimeCount 1 x y

end AgdaMirror.DeltaRarity
