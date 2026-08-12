import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.ActiveWallStructure
import AgdaMirror.ArithmeticDeltaGrowth
import AgdaMirror.DeltaInteraction
import AgdaMirror.DeltaRarity

/-!
# Lean mirror of `DASHI/Arithmetic/KPrimeInteraction.agda` (genuine, fully proved)

The minimal `k`-prime interaction surface.  The list side is the new honest
step: a finite inductive carrier of the tracked primes with a recursive
threshold/support count theorem (`familyThresholdSupportSubset`).  The pairwise
interaction side is reused from `DeltaInteraction`, and the single-lane budget
from `ArithmeticDeltaGrowth`.  The hard family-product theorem is intentionally
out of scope.
-/

namespace AgdaMirror.KPrimeInteraction

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.ActiveWallStructure
open AgdaMirror.ArithmeticDeltaGrowth
open AgdaMirror.DeltaInteraction
open AgdaMirror.DeltaRarity
open SSP

/-- The tracked prime list, in prime order. -/
def trackedPrimeList : List SSP :=
  [p2, p3, p5, p7, p11, p13, p17, p19, p23, p29, p31, p41, p47, p59, p71]

/-- Threshold mask over the 15-lane carrier. -/
def thresholdMask15 (k : Nat) (x y : IntCarrier) : Vec15 Nat :=
  mapPrimes15 (fun p => thresholdAt k p x y)

/-- Recursive threshold count over a list of tracked primes. -/
def familyThresholdCount (k : Nat) (ps : List SSP) (x y : IntCarrier) : Nat :=
  match ps with
  | [] => 0
  | p :: ps => thresholdAt k p x y + familyThresholdCount k ps x y

/-- Recursive support count over a list of tracked primes. -/
def familySupportCount (ps : List SSP) (x y : IntCarrier) : Nat :=
  match ps with
  | [] => 0
  | p :: ps => supportMaskAt p x y + familySupportCount ps x y

/-- Every threshold slice sits inside the support shadow, over any prime list. -/
theorem familyThresholdSupportSubset (k : Nat) (ps : List SSP) (x y : IntCarrier) :
    familyThresholdCount k ps x y ≤ familySupportCount ps x y := by
  induction ps with
  | nil => simp [familyThresholdCount, familySupportCount]
  | cons p ps ih =>
    simp only [familyThresholdCount, familySupportCount]
    exact Nat.add_le_add (thresholdAt_le_supportMaskAt k p x y) ih

/-- Pairwise distinct-lane product divisibility (reused). -/
theorem pairPowerDivides (p q : SSP) (x y : IntCarrier) (hpq : p ≠ q) :
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y) :=
  distinctPrimePowerProductDividesSum p q x y hpq

/-- Pairwise distinct-lane size budget (reused). -/
theorem pairPowerBound (p q : SSP) (x y : IntCarrier) (h : 0 < x + y) (hpq : p ≠ q) :
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y) :=
  twoPrimeInteractionBudget p q x y h hpq

/-- Tracked-family threshold count. -/
def trackedFamilyThresholdCount (k : Nat) (x y : IntCarrier) : Nat :=
  familyThresholdCount k trackedPrimeList x y

/-- Tracked-family support count. -/
def trackedFamilySupportCount (x y : IntCarrier) : Nat :=
  familySupportCount trackedPrimeList x y

theorem trackedFamilyThresholdSupportSubset (k : Nat) (x y : IntCarrier) :
    trackedFamilyThresholdCount k x y ≤ trackedFamilySupportCount x y :=
  familyThresholdSupportSubset k trackedPrimeList x y

/-- Vector-compatible threshold count. -/
def kThresholdCount (k : Nat) (x y : IntCarrier) : Nat := thresholdCount k x y

theorem kThresholdSupportSubset (k : Nat) (x y : IntCarrier) :
    kThresholdCount k x y ≤ supportPrimeCount x y :=
  thresholdCount_le_supportPrimeCount k x y

/-- Single-lane divisibility (reused). -/
theorem singleLanePowerDivides (p : SSP) (x y : IntCarrier) :
    pow (toNat p) (deltaAt p x y) ∣ (x + y) :=
  deltaPowerDividesSum p x y

/-- Single-lane size bound (reused). -/
theorem singleLanePowerBound (p : SSP) (x y : IntCarrier) (h : 0 < x + y) :
    pow (toNat p) (deltaAt p x y) ≤ x + y :=
  deltaPower_le_sum p x y h

end AgdaMirror.KPrimeInteraction
