import Mathlib
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport
import AgdaMirror.WeightedPressure

/-!
# Lean mirror of `DASHI/Arithmetic/MaxPressure.agda` (genuine, fully proved)

Pressure maxima for the arithmetic carriers.  The core carrier fact is that the
tracked 15-lane maximum is bounded by the 15-lane sum (`max15 ≤ sum15`), from
which `maxPressure ≤ totalPressure ≤ trackedSupport` and the weighted analogues
follow.
-/

namespace AgdaMirror.MaxPressure

open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Descriptive
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.TrackedSupport
open AgdaMirror.WeightedPressure

/-- The tracked 15-lane maximum is bounded by the 15-lane sum. -/
theorem max15_le_sum15 (v : Vec15 Nat) : max15 v ≤ sum v := by
  cases v
  simp only [max15, sum]
  omega

/-- Every lane is bounded by the 15-lane maximum. -/
theorem le_max15_all (v : Vec15 Nat) :
    v.e2 ≤ max15 v ∧ v.e3 ≤ max15 v ∧ v.e5 ≤ max15 v ∧ v.e7 ≤ max15 v ∧
    v.e11 ≤ max15 v ∧ v.e13 ≤ max15 v ∧ v.e17 ≤ max15 v ∧ v.e19 ≤ max15 v ∧
    v.e23 ≤ max15 v ∧ v.e29 ≤ max15 v ∧ v.e31 ≤ max15 v ∧ v.e41 ≤ max15 v ∧
    v.e47 ≤ max15 v ∧ v.e59 ≤ max15 v ∧ v.e71 ≤ max15 v := by
  cases v
  simp only [max15]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat' (first
      | exact le_max_left _ _
      | exact le_max_right _ _
      | refine le_trans ?_ (le_max_right _ _))

/-- Pressure maximum. -/
def maxPressure (x y : IntCarrier) : Nat := max15 (delta15 x y)

/-- Weighted pressure maximum. -/
def weightedMaxPressure (x y : IntCarrier) : Nat := max15 (weightedDelta15 x y)

/-- The pressure maximum is bounded by total pressure. -/
theorem maxPressure_le_totalPressure (x y : IntCarrier) :
    maxPressure x y ≤ totalPressure x y :=
  max15_le_sum15 (delta15 x y)

/-- The weighted pressure maximum is bounded by weighted pressure. -/
theorem weightedMaxPressure_le_weightedPressure (x y : IntCarrier) :
    weightedMaxPressure x y ≤ weightedPressure x y :=
  max15_le_sum15 (weightedDelta15 x y)

/-- The weighted pressure maximum is bounded by weighted support. -/
theorem weightedMaxPressure_le_weightedSupport (x y : IntCarrier) :
    weightedMaxPressure x y ≤ weightedSupport x y :=
  le_trans (weightedMaxPressure_le_weightedPressure x y)
    (weightedPressure_le_weightedSupport x y)

/-- The pressure maximum is bounded by tracked support. -/
theorem maxPressure_le_trackedSupport (x y : IntCarrier) :
    maxPressure x y ≤ trackedSupport x y :=
  le_trans (maxPressure_le_totalPressure x y) (totalPressure_le_trackedSupport x y)

end AgdaMirror.MaxPressure
