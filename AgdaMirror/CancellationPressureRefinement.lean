import Mathlib
import AgdaMirror.NormalizeAdd
import AgdaMirror.CancellationPressureFromCanonical

/-!
# Lean mirror of `DASHI/Arithmetic/CancellationPressureRefinement.agda`
(genuine, fully proved)

The refined cancellation pressure `residueDepth + carryBudget`, and the genuine
canonical ⇒ bounded chain: at a canonical state the residue depth equals the
`p`-adic depth and the carry budget vanishes, so the refined pressure sits under
the support pressure (`canonical_refinedBounded`), in particular after one
`normalizeAdd` step (`normalizeAdd_refinedBounded`).
-/

namespace AgdaMirror.CancellationPressureRefinement

open AgdaMirror.NormalizeAdd
open AgdaMirror.CancellationPressureFromCanonical

/-- Refined cancellation pressure. -/
def RefinedCancellationPressure (s : NormalizeAddState) : Nat :=
  s.residueDepth + s.carryBudget

/-- At a canonical state, residue depth equals `p`-adic depth. -/
theorem canonicalResidueDepth_fromCanonical (s : NormalizeAddState)
    (canon : normalizeAddCanonical s) : s.residueDepth = s.padicDepth := canon.1

/-- Canonical ⇒ refined pressure bounded by support pressure. -/
theorem canonical_refinedBounded (s : NormalizeAddState) (canon : normalizeAddCanonical s) :
    RefinedCancellationPressure s ≤ StateSupportPressure s := by
  have hb : s.carryBudget = 0 := canonicalResidueBudget_fromCanonical s canon
  have hr : s.residueDepth = s.padicDepth := canonicalResidueDepth_fromCanonical s canon
  simp [RefinedCancellationPressure, StateSupportPressure, hb, hr]

/-- One-step refined bound. -/
theorem normalizeAdd_refinedBounded (s : NormalizeAddState) :
    RefinedCancellationPressure (normalizeAdd s) ≤ StateSupportPressure (normalizeAdd s) :=
  canonical_refinedBounded (normalizeAdd s) (normalizeAdd_canonical s)

/-- The packaged refinement surface. -/
structure RefinementSurface where
  refined : NormalizeAddState → Nat
  canonicalBound : ∀ s, normalizeAddCanonical s → refined s ≤ StateSupportPressure s
  normalizeAddOneStepBound : ∀ s, refined (normalizeAdd s) ≤ StateSupportPressure (normalizeAdd s)

/-- The canonical witness. -/
def cancellationPressureRefinement : RefinementSurface where
  refined := RefinedCancellationPressure
  canonicalBound := canonical_refinedBounded
  normalizeAddOneStepBound := normalizeAdd_refinedBounded

end AgdaMirror.CancellationPressureRefinement
