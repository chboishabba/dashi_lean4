import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.ArithmeticDeltaGrowth
import AgdaMirror.ArithmeticCoprimeLayer

/-!
# Lean mirror of `DASHI/Arithmetic/DeltaInteraction.agda` (genuine, fully proved)

Two-prime interaction over the tracked carrier:

* single-lane divisibility / size bounds (from `ArithmeticDeltaGrowth`);
* the distinct-lane product divisibility helper
  (`distinctPrimePowerProductDividesSum`), via the coprime layer; and
* the corresponding shared-size budget corollary
  (`twoPrimeInteractionBudget`).
-/

namespace AgdaMirror.DeltaInteraction

open AgdaMirror.MonsterOntos
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.ArithmeticDeltaGrowth
open AgdaMirror.ArithmeticCoprimeLayer
open SSP

/-- One-lane divisibility (reused from `ArithmeticDeltaGrowth`). -/
theorem singlePrimePowerDividesSum (p : SSP) (x y : IntCarrier) :
    pow (toNat p) (deltaAt p x y) ∣ (x + y) :=
  deltaPowerDividesSum p x y

/-- One-lane size bound. -/
theorem singlePrimePowerBound (p : SSP) (x y : IntCarrier) (h : 0 < x + y) :
    pow (toNat p) (deltaAt p x y) ≤ x + y :=
  deltaPower_le_sum p x y h

/-- The product of two distinct-lane delta powers divides the sum. -/
theorem distinctPrimePowerProductDividesSum (p q : SSP) (x y : IntCarrier) (hpq : p ≠ q) :
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y) := by
  have hc : Nat.Coprime (pow (toNat p) (deltaAt p x y)) (pow (toNat q) (deltaAt q x y)) :=
    distinctTrackedPrimePowersCoprime p q (deltaAt p x y) (deltaAt q x y) hpq
  exact coprimeProductDivides hc (deltaPowerDividesSum p x y) (deltaPowerDividesSum q x y)

/-- The shared-size budget for two distinct lanes. -/
theorem twoPrimeInteractionBudget (p q : SSP) (x y : IntCarrier) (h : 0 < x + y) (hpq : p ≠ q) :
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y) :=
  Nat.le_of_dvd h (distinctPrimePowerProductDividesSum p q x y hpq)

/-- The packaged two-prime interaction surface. -/
structure DeltaInteractionSurface where
  oneLaneDivides : ∀ (p : SSP) (x y : IntCarrier),
    pow (toNat p) (deltaAt p x y) ∣ (x + y)
  oneLaneBound : ∀ (p : SSP) (x y : IntCarrier), 0 < x + y →
    pow (toNat p) (deltaAt p x y) ≤ x + y
  twoLaneDivides : ∀ (p q : SSP) (x y : IntCarrier), p ≠ q →
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y)
  twoLaneBound : ∀ (p q : SSP) (x y : IntCarrier), 0 < x + y → p ≠ q →
    (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y)

/-- The canonical surface witness. -/
def deltaInteractionSurface : DeltaInteractionSurface where
  oneLaneDivides := singlePrimePowerDividesSum
  oneLaneBound := singlePrimePowerBound
  twoLaneDivides := distinctPrimePowerProductDividesSum
  twoLaneBound := twoPrimeInteractionBudget

end AgdaMirror.DeltaInteraction
