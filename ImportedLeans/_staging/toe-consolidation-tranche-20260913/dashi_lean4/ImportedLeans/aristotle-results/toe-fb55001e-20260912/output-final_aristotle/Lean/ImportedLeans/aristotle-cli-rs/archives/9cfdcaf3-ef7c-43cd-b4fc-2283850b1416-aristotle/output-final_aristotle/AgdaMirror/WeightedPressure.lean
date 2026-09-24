import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport

/-!
# Lean mirror of `DASHI/Arithmetic/WeightedPressure.agda` (genuine, fully proved)

Weighted quantities over the tracked 15-prime carrier, the weight being the
prime size `toNat`.  The local weighted bound uses multiplication monotonicity,
and the global inequality `weightedPressure ≤ weightedSupport` lifts it across
the 15 lanes.
-/

namespace AgdaMirror.WeightedPressure

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.TrackedSupport
open SSP

/-- Weight = prime size. -/
def weight (p : SSP) : Nat := toNat p

/-- Weighted local delta. -/
def weightedDeltaAt (p : SSP) (x y : IntCarrier) : Nat := weight p * deltaAt p x y

/-- Weighted local support. -/
def weightedSupportAt (p : SSP) (x y : IntCarrier) : Nat := weight p * supportAt p x y

/-- 15-lane weighted delta vector. -/
def weightedDelta15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => weightedDeltaAt p x y)

/-- 15-lane weighted support vector. -/
def weightedSupport15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => weightedSupportAt p x y)

/-- Global weighted pressure. -/
def weightedPressure (x y : IntCarrier) : Nat := sum (weightedDelta15 x y)

/-- Global weighted support. -/
def weightedSupport (x y : IntCarrier) : Nat := sum (weightedSupport15 x y)

/-- Local weighted bound (the only place needing multiplication monotonicity). -/
theorem weightedLocalBound (p : SSP) (x y : IntCarrier) :
    weightedDeltaAt p x y ≤ weightedSupportAt p x y := by
  unfold weightedDeltaAt weightedSupportAt
  exact Nat.mul_le_mul_left _ (deltaAt_le_supportAt p x y)

/-- Global weighted inequality. -/
theorem weightedPressure_le_weightedSupport (x y : IntCarrier) :
    weightedPressure x y ≤ weightedSupport x y := by
  unfold weightedPressure weightedSupport weightedDelta15 weightedSupport15 mapPrimes15 sum
  simp only
  have h := fun p => weightedLocalBound p x y
  have := h p2; have := h p3; have := h p5; have := h p7; have := h p11
  have := h p13; have := h p17; have := h p19; have := h p23; have := h p29
  have := h p31; have := h p41; have := h p47; have := h p59; have := h p71
  omega

end AgdaMirror.WeightedPressure
