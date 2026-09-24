import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.VpAddUnequal
import AgdaMirror.DASHIValuation

/-!
# Lean mirror of `DASHI/Arithmetic/GlobalPressure.agda` (genuine, fully proved)

The wall-filtered global pressure over the tracked 15-prime carrier.  The wall
bit `wallBitBridge p x y = natEq (α_p, β_p)` is the *genuine* (non-postulated)
projection from the prime-profile bridge, and off the wall the local lift
collapses (`offWallZero`).  Hence the wall-filtered delta agrees with the tracked
delta lane-by-lane (`wallDeltaAt_eq_deltaAt`), and the headline structural
theorem holds: total tracked pressure lives entirely on the wall primes
(`totalPressure_eq_wallPressure`).

(Following the honesty discipline, only the genuine wall-bit / collapse content
is mirrored here.  The prime-profile-stats `postulate`s of
`ArithmeticPrimeProfileBridge` are *not* transcribed as axioms.)
-/

namespace AgdaMirror.GlobalPressure

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.DASHIValuation (natEq)
open SSP

/-- The genuine wall bit: `α_p = β_p` (Boolean), from the prime-profile bridge. -/
def wallBitBridge (p : SSP) (x y : IntCarrier) : Bool :=
  natEq (alphaAt p x y) (betaAt p x y)

/-- Off the wall, the local lift collapses to zero. -/
theorem offWallZero (p : SSP) (x y : IntCarrier) (h : wallBitBridge p x y = false) :
    deltaAt p x y = 0 := by
  unfold deltaAt
  rw [AgdaMirror.VpAddUnequal.vp_add_min_unequal p x y h, Nat.sub_self]

/-- The wall-filtered local pressure. -/
def wallDeltaAt (p : SSP) (x y : IntCarrier) : Nat :=
  if wallBitBridge p x y then deltaAt p x y else 0

/-- Local wall-filtering preserves the tracked delta exactly. -/
theorem wallDeltaAt_eq_deltaAt (p : SSP) (x y : IntCarrier) :
    wallDeltaAt p x y = deltaAt p x y := by
  unfold wallDeltaAt
  by_cases h : wallBitBridge p x y = true
  · rw [if_pos h]
  · have hf : wallBitBridge p x y = false := by
      cases hb : wallBitBridge p x y with
      | true => exact absurd hb h
      | false => rfl
    rw [if_neg (by simp [hf]), offWallZero p x y hf]

/-- Total tracked pressure. -/
def totalPressure (x y : IntCarrier) : Nat := sum (delta15 x y)

/-- The wall-filtered delta vector. -/
def wallDelta15 (x y : IntCarrier) : Vec15 Nat :=
  mapPrimes15 (fun p => wallDeltaAt p x y)

/-- The wall-filtered global pressure. -/
def wallPressure (x y : IntCarrier) : Nat := sum (wallDelta15 x y)

/-- The wall-filtered delta vector equals the tracked delta vector. -/
theorem wallDelta15_eq_delta15 (x y : IntCarrier) : wallDelta15 x y = delta15 x y := by
  unfold wallDelta15 delta15
  congr 1
  funext p
  exact wallDeltaAt_eq_deltaAt p x y

/-- Headline structural theorem: total tracked pressure lives entirely on the
wall primes. -/
theorem totalPressure_eq_wallPressure (x y : IntCarrier) :
    totalPressure x y = wallPressure x y := by
  unfold totalPressure wallPressure
  rw [wallDelta15_eq_delta15]

/-- The packaged global-pressure structure. -/
structure GlobalPressureStructure where
  total : IntCarrier → IntCarrier → Nat
  wall : IntCarrier → IntCarrier → Nat
  total_eq_wall : ∀ x y, total x y = wall x y

/-- The canonical witness. -/
def globalPressureStructure : GlobalPressureStructure where
  total := totalPressure
  wall := wallPressure
  total_eq_wall := totalPressure_eq_wallPressure

end AgdaMirror.GlobalPressure
