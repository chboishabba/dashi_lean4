import RequestProject.QuantumMereologySchwingerObjective
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite nonempty Schwinger-search minimizer

Carroll--Singh supply the external scientific objective.  The generic DASHI
selection layer deliberately does not infer that a physical minimizer exists.
This module isolates a purely finite-order theorem:

if the declared candidate carrier is finite and at least one candidate is
admissible, the real-valued Schwinger score has an admissible minimizer.

Thus the finite combinatorial existence step is theorem-derived.  What remains
scientific/application-specific is whether a proposed search domain is a
source-faithful finite candidate family, whether it is nonempty after the actual
physical admissibility constraints, and whether any minimizer is unique or
physically preferred beyond that declared domain.
-/

namespace QuantumMereology
namespace FiniteSchwingerSelection

open SchwingerObjective

variable
  {W : BareQuantumWorld}
  {PointerInit : Type*}
  [Fintype PointerInit] [Nonempty PointerInit]

/-- A finite nonempty admissible Schwinger search has a score-minimizing
selection receipt. -/
noncomputable def selectionReceipt
    (D : SearchData W PointerInit)
    [Finite D.Candidate]
    (hasAdmissible : ∃ c : D.Candidate, D.Admissible c) :
    PreferredTPSSelectionReceipt D.selectionProblem := by
  classical
  let s : Set D.Candidate := {c | D.Admissible c}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := by
    rcases hasAdmissible with ⟨c, hc⟩
    exact ⟨c, hc⟩
  obtain ⟨selected, hSelected, hMinimal⟩ :=
    s.exists_min_image D.score hsFinite hsNonempty
  refine
    { selected := selected
      selectedOptimal := ?_ }
  refine ⟨hSelected, ?_⟩
  intro other hOther
  exact hMinimal other hOther

/-- The receipt produced above minimizes the literal source-shaped Schwinger
score on every admissible candidate in the declared finite search domain. -/
theorem selectionReceipt_minimizes_score
    (D : SearchData W PointerInit)
    [Finite D.Candidate]
    (hasAdmissible : ∃ c : D.Candidate, D.Admissible c)
    (other : D.Candidate)
    (hOther : D.Admissible other) :
    D.score (selectionReceipt D hasAdmissible).selected ≤ D.score other :=
  D.selected_minimizes_schwinger_score
    (selectionReceipt D hasAdmissible) other hOther

structure Boundary where
  finiteNonemptyAdmissibleSearchHasMinimizer : Bool := true
  finiteMinimizerCreatesUniqueness : Bool := false
  sourceSearchIsAutomaticallyFinite : Bool := false
  sourceSearchIsAutomaticallyAdmissiblyNonempty : Bool := false
  finiteSearchMinimizerIsAutomaticallyPhysicalGlobalOptimum : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem finite_nonempty_admissible_search_has_minimizer :
    canonicalBoundary.finiteNonemptyAdmissibleSearchHasMinimizer = true := rfl

theorem finite_minimizer_does_not_create_uniqueness :
    canonicalBoundary.finiteMinimizerCreatesUniqueness = false := rfl

theorem source_search_not_automatically_finite :
    canonicalBoundary.sourceSearchIsAutomaticallyFinite = false := rfl

/-- Imported theorem-source attribution for the finite-order existence step. -/
def mathlibFiniteMinimumSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Set.Finite.exists_min_image"
  claim := "Supplies existence of a minimum of a real-valued function on a nonempty finite set."

/-- DASHI theorem receipt.  Carroll--Singh are not attributed this local finite
existence proof. -/
def dashiFiniteSchwingerSelectionReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Compiles any finite candidate carrier with a nonempty admissible subset into a PreferredTPSSelectionReceipt minimizing the already reconstructed Schwinger score. Finiteness, admissible nonemptiness, uniqueness and physical global preference remain separate obligations."

end FiniteSchwingerSelection
end QuantumMereology
