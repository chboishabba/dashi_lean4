import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport

/-!
# Lean mirror of `DASHI/Arithmetic/ActiveWallStructure.agda` (genuine, fully proved)

The active wall: tracked primes whose local cancellation lift is genuinely
non-zero.  We prove the local monotonicity of the non-zero indicator
(`countNonZeroNat_mono`) and the global subset bound
`activeWallCount ≤ supportPrimeCount`.
-/

namespace AgdaMirror.ActiveWallStructure

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Descriptive
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.TrackedSupport
open SSP

/-- Raw active-wall bit: `true` iff the local delta is non-zero. -/
def activeWallAt (p : SSP) (x y : IntCarrier) : Bool :=
  match deltaAt p x y with
  | 0 => false
  | _ + 1 => true

/-- Active-wall non-zero indicator. -/
def activeWallMaskAt (p : SSP) (x y : IntCarrier) : Nat := countNonZeroNat (deltaAt p x y)

/-- Support-side non-zero indicator. -/
def supportMaskAt (p : SSP) (x y : IntCarrier) : Nat := countNonZeroNat (supportAt p x y)

/-- Active-wall prime count over the tracked carrier. -/
def activeWallCount (x y : IntCarrier) : Nat := countNonZero15 (delta15 x y)

/-- Support prime count over the tracked carrier. -/
def supportPrimeCount (x y : IntCarrier) : Nat := countNonZero15 (gamma15 x y)

/-- Local monotonicity of the non-zero indicator (Agda `countNonZeroNat-mono`). -/
theorem countNonZeroNat_mono {a b : Nat} (h : a ≤ b) :
    countNonZeroNat a ≤ countNonZeroNat b :=
  AgdaMirror.Vec15Descriptive.countNonZeroNat_mono h

/-- Local active-wall ⊆ support. -/
theorem activeWallMaskAt_le_supportMaskAt (p : SSP) (x y : IntCarrier) :
    activeWallMaskAt p x y ≤ supportMaskAt p x y := by
  unfold activeWallMaskAt supportMaskAt
  exact countNonZeroNat_mono (deltaAt_le_supportAt p x y)

/-- Active-wall primes are a support-side subset over the tracked carrier. -/
theorem activeWallCount_le_supportPrimeCount (x y : IntCarrier) :
    activeWallCount x y ≤ supportPrimeCount x y := by
  unfold activeWallCount supportPrimeCount countNonZero15 delta15 gamma15 mapPrimes15
  simp only
  have h := fun p => activeWallMaskAt_le_supportMaskAt p x y
  simp only [activeWallMaskAt, supportMaskAt, supportAt] at h
  have := h p2; have := h p3; have := h p5; have := h p7; have := h p11
  have := h p13; have := h p17; have := h p19; have := h p23; have := h p29
  have := h p31; have := h p41; have := h p47; have := h p59; have := h p71
  omega

end AgdaMirror.ActiveWallStructure
