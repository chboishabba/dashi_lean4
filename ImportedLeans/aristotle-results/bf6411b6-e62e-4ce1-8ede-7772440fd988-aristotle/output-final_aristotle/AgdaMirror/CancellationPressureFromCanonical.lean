import Mathlib
import AgdaMirror.NormalizeAdd
import AgdaMirror.CancellationPressure

/-!
# Lean mirror of `DASHI/Arithmetic/CancellationPressureFromCanonical.agda`
(genuine, fully proved)

The cheapest honest state-side semantics supported by the carry-resolution
model: cancellation pressure is the carry-budget proxy, and support pressure is
the `p`-adic depth budget available to absorb it.  The canonical ⇒ bounded chain
(`canonical_boundedPressure`) and the one-step support bound
(`normalizeAddOneStepSupportBound`) are genuine consequences of the canonical
form's zero carry budget.
-/

namespace AgdaMirror.CancellationPressureFromCanonical

open AgdaMirror.NormalizeAdd
open AgdaMirror.CancellationPressure

/-- Cancellation pressure = the carry-budget proxy. -/
def StateCancellationPressure (s : NormalizeAddState) : Nat := s.carryBudget

/-- Support pressure = the `p`-adic depth budget. -/
def StateSupportPressure (s : NormalizeAddState) : Nat := s.padicDepth

theorem canonicalCancellationPressure_le_bound (s : NormalizeAddState) :
    StateCancellationPressure s ≤ StateCancellationPressure s := le_refl _

theorem canonicalCancellationPressure_step (s : NormalizeAddState) :
    StateCancellationPressure (normalizeAdd s) ≤ StateCancellationPressure s := by
  simp [StateCancellationPressure, normalizeAdd]

/-- The canonical ⇒ bounded chain: a canonical state's carry budget (zero) sits
under the support pressure. -/
theorem canonical_boundedPressure (s : NormalizeAddState) (canon : normalizeAddCanonical s) :
    StateCancellationPressure s ≤ StateSupportPressure s := by
  have hb : s.carryBudget = 0 := canonicalResidueBudget_fromCanonical s canon
  simp [StateCancellationPressure, StateSupportPressure, hb]

/-- After one step the state is canonical. -/
theorem normalizeAddOneStepCanonical (s : NormalizeAddState) :
    normalizeAddCanonical (normalizeAdd s) := normalizeAdd_canonical s

/-- The one-step support bound. -/
theorem normalizeAddOneStepSupportBound (s : NormalizeAddState) :
    StateCancellationPressure (normalizeAdd s) ≤ StateSupportPressure (normalizeAdd s) :=
  canonical_boundedPressure (normalizeAdd s) (normalizeAdd_canonical s)

/-- The canonical cancellation-pressure core (predecessor-free witness over the
state model). -/
def canonicalCancellationPressureCore : CancellationPressureCore where
  Carrier := NormalizeAddState
  step := normalizeAdd
  cancellationPressure := StateCancellationPressure
  pressure_step := canonicalCancellationPressure_step

end AgdaMirror.CancellationPressureFromCanonical
