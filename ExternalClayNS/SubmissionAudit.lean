import ClauseAudit
import Gap
import NavierStokes.PeriodicPaperTheorem
import NavierStokes.PeriodicPaperComparator
import NavierStokes.R3.Theorem
import NavierStokes.R3.ComparatorBridge

/-!
# Submission-facing direct C/D source audit

Goal 1 is mathematical sufficiency for the official Clay alternatives, not
reconstruction of every standard analytic lemma in DASHI.

This file deliberately bypasses the high-level `ComparatorSolution` aliases.
It rebuilds the C/D endpoints directly from the pinned source theorem spines:

* C: `NavierStokesR3.theorem_1_1`
     → `NavierStokesR3.comparator_of_breakdown`
     → the independently proved semantic bridge in `Gap.lean`.
* D: `PeriodicPaper.periodic_corollary`
     → `ComparatorBridge.option_D_of_paper_candidate`
     → the independently proved semantic bridge in `Gap.lean`.

Thus the build-time axiom report below is attached to the actual paper-level
source theorems rather than only to wrapper names.
-/

noncomputable section

namespace DASHILiteralClayNS.SubmissionAudit

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Direct source spine for alternative C, bypassing ComparatorSolution. -/
theorem directComparatorC : SemanticGap.ComparatorOptionC := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact NavierStokesR3.comparator_of_breakdown hc hglobal

/-- Direct source spine for alternative D, bypassing ComparatorSolution. -/
theorem directComparatorD : SemanticGap.ComparatorOptionD := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hglobal⟩ := PeriodicPaper.periodic_corollary ν hν
  exact NavierStokes.ComparatorBridge.option_D_of_paper_candidate hc hglobal

/-- Direct source-to-independent-Clay endpoint for C. -/
theorem directClayC : ClaySpec.ClayOptionC :=
  SemanticGap.ComparatorOptionC_to_ClayOptionC directComparatorC

/-- Direct source-to-independent-Clay endpoint for D. -/
theorem directClayD : ClaySpec.ClayOptionD :=
  SemanticGap.ComparatorOptionD_to_ClayOptionD directComparatorD

/-- Every fixed positive viscosity exposes the official C clauses directly. -/
theorem directClauseAuditC (ν : ℝ) (hν : 0 < ν) :
    DASHILiteralClayNS.ClauseAuditC ν hν :=
  DASHILiteralClayNS.clauseAuditC_of_ClayOptionC directClayC ν hν

/-- Every fixed positive viscosity exposes the official D clauses directly. -/
theorem directClauseAuditD (ν : ℝ) (hν : 0 < ν) :
    DASHILiteralClayNS.ClauseAuditD ν hν :=
  DASHILiteralClayNS.clauseAuditD_of_ClayOptionD directClayD ν hν

/-- Clause unpacking/repacking loses no content on the direct C spine. -/
theorem directClayC_roundTrip : ClaySpec.ClayOptionC :=
  DASHILiteralClayNS.ClayOptionC_of_clauseAudits directClauseAuditC

/-- Clause unpacking/repacking loses no content on the direct D spine. -/
theorem directClayD_roundTrip : ClaySpec.ClayOptionD :=
  DASHILiteralClayNS.ClayOptionD_of_clauseAudits directClauseAuditD

/-- The direct and wrapper routes end at definitionally the same proposition.
This theorem records both inhabitants without asserting proof-term equality. -/
structure DualRouteReceipt : Prop where
  directC : ClaySpec.ClayOptionC
  wrapperC : ClaySpec.ClayOptionC
  directD : ClaySpec.ClayOptionD
  wrapperD : ClaySpec.ClayOptionD

theorem dualRouteReceipt : DualRouteReceipt :=
  ⟨directClayC_roundTrip,
   DASHILiteralClayNS.literalClayC_roundTrip,
   directClayD_roundTrip,
   DASHILiteralClayNS.literalClayD_roundTrip⟩

#print axioms NavierStokesR3.theorem_1_1
#print axioms NavierStokesR3.comparator_of_breakdown
#print axioms directComparatorC
#print axioms directClayC
#print axioms directClayC_roundTrip

#print axioms PeriodicPaper.periodic_corollary
#print axioms NavierStokes.ComparatorBridge.option_D_of_paper_candidate
#print axioms directComparatorD
#print axioms directClayD
#print axioms directClayD_roundTrip

#print axioms dualRouteReceipt

end DASHILiteralClayNS.SubmissionAudit
