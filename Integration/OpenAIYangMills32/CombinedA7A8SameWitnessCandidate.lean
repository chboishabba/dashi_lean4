import CombinedAcceptance
import OPECheck

/-!
# October OpenAI YM A7 + A8, same selected hierarchy (PROOF CANDIDATE)

Upstream mathematical source and all theorem credit: OpenAI, 28 October 2026.
Review interface and review credit: YM review group (Douglas, Gross, Jaffe,
Klebanov, Nekrasov), 10 November 2026. This adapter only composes their
existing source and review theorems. It is not a new physics theorem.

Compile in the *external review release*, Lean 4.32.0, after placing this
file next to CombinedAcceptance.lean and OPECheck.lean. It is intentionally
not imported into native DASHI Lean 4.28.0. No kernel receipt has been
obtained for this new adapter.

The combined witness chooses C,S,F. Its Accepted.source contains a
same-hierarchy OPE property, and OPE.from_source converts this to the
independently reviewed CommonOPE structure with no new existential choices.
-/ 

set_option autoImplicit false
noncomputable section
namespace YMReview.Acceptance
open YM YM.Table
variable {g : YangMills.GaugeGroup} {C : Family g.core}
variable {o : Extraction.Order} {S : Table C.book}

/-- A8 CommonOPE for the hierarchy of the very same A7 Accepted F. -/
theorem accepted_same_hierarchy_commonOPE (hg : g.IsSimple)
    (F : Spec.Final C o S) (h : Accepted hg F) :
    ∃ (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
      YMReview.OPE.CommonOPE (YangMills.hierarchy F Q) := by
  obtain ⟨L, Q, M, X, hpublic, hcontacts, hcore, hrest⟩ := h.source
  exact ⟨Q, YMReview.OPE.from_source hpublic.ope⟩

/-- Candidate joint endpoint with the original A7 family/order scope.
All assertions refer to the identical selected F, without choosing a
second hierarchy. This does not assert mass gap or unique limits. -/
theorem combined_acceptance_with_same_hierarchy_commonOPE
    (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : Family g.core, C.path.levels.clock.kernel.penalty = b ∧
      ∀ p : Extraction.Order,
        ∃ (q : Extraction.Order) (S : Table C.book)
          (F : Spec.Final C (p.refine q) S),
          Accepted hg F ∧
          ∃ (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
            YMReview.OPE.CommonOPE (YangMills.hierarchy F Q) := by
  obtain ⟨C, hpenalty, horders⟩ := combined_acceptance g hg b hb
  refine ⟨C, hpenalty, ?_⟩
  intro p
  obtain ⟨q, S, F, hAccepted⟩ := horders p
  exact ⟨q, S, F, hAccepted, accepted_same_hierarchy_commonOPE hg F hAccepted⟩

#print axioms YMReview.Acceptance.accepted_same_hierarchy_commonOPE
#print axioms YMReview.Acceptance.combined_acceptance_with_same_hierarchy_commonOPE

end YMReview.Acceptance
