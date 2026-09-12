import RequestProject.Wikidata.Examples
import RequestProject.Wikidata.Lens

/-!
# Worked example: pooled conflict, and layer transport

Two regressions over the artist / painter / sculptor fragment of
`Wikidata.Examples`, one for each of the two structures added in the latest
pass.

* **Pooling before collapsing.**  The claim `painter ⊑ artist` is decided
  positively by the checker on `artistKB` and negatively on `partialKB`.  Both
  are certified verdicts — the checkers are exact — but they are certified about
  *different knowledge bases*, so at world level the two sources are in conflict.
  Pooled on support squares, that conflict is visible
  (`pooled_verdicts_conflict`); collapsed to a single evidence state first, it is
  indistinguishable from never having heard anything at all
  (`conflict_indistinguishable_from_silence`).  This is why the merge happens on
  squares.

* **Layer transport.**  Class facts survive the move between the full and truthy
  layers unchanged (`artistKB_class_view_layer_invariant`), while two ranked
  variants of a single statement show the direct RDF layer collapsing a
  distinction that the reified layer keeps (`ranked_variants_agree_directly`),
  which is the concrete witness behind `no_transition_direct_reified`.
-/

namespace Wikidata

namespace Example

open Epistemic

/-! ## Two knowledge bases, two certified verdicts, one conflict -/

/-- The verdict a source reports about `painter ⊑ artist` after running the
exact checker on a given knowledge base. -/
def painterArtistVerdict (kb : KB) : ObjectVerdict :=
  if isSubclassOf kb painter artist then ObjectVerdict.certifiedHolds
  else ObjectVerdict.certifiedRefuted

theorem verdict_artistKB : painterArtistVerdict artistKB = ObjectVerdict.certifiedHolds := by
  decide

theorem verdict_partialKB : painterArtistVerdict partialKB = ObjectVerdict.certifiedRefuted := by
  decide

/-- The support square of a source that ran the checker on `kb`. -/
def painterArtistSquare (kb : KB) : SupportSquare :=
  importSquare true true (painterArtistVerdict kb)

/-- Each single source lands on a resolved corner: no source contradicts itself. -/
theorem single_source_resolved (kb : KB) :
    (classify (painterArtistSquare kb)).Resolved := by
  unfold painterArtistSquare painterArtistVerdict
  split <;> decide

/-- The two sources pooled. -/
def pooledSquare : SupportSquare :=
  SupportSquare.merge (painterArtistSquare artistKB) (painterArtistSquare partialKB)

/-- **The pooled evidence is a genuine conflict**, and the square records it. -/
theorem pooled_verdicts_conflict : classify pooledSquare = Corner.bothSupported := by decide

/-- **Collapsing first destroys exactly that information**: the conflict reads as
`unresolved`, the same state as two sources that observed nothing. -/
theorem conflict_indistinguishable_from_silence :
    collapse (classify pooledSquare) = Trit.unresolved ∧
      collapse (classify (SupportSquare.merge SupportSquare.empty SupportSquare.empty))
        = Trit.unresolved ∧
      classify pooledSquare
        ≠ classify (SupportSquare.merge SupportSquare.empty SupportSquare.empty) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The trit-level comparison of the same two verdicts agrees: `conflicting` is
exactly the top corner. -/
theorem pooled_conflict_matches_comparison :
    compareStates (verdictState true true (painterArtistVerdict artistKB))
        (verdictState true true (painterArtistVerdict partialKB))
      = Disposition.conflicting := by
  decide

/-- Neither verdict may be exported as a world-level refutation, which is what
`absence_is_not_world_refutation` says about this very pair: `partialKB` simply
lacks the edge. -/
theorem partialKB_negative_is_kb_relative :
    ¬ SubclassOf partialKB painter artist ∧ SubclassOf artistKB painter artist := by
  refine ⟨?_, painter_subclass_artist⟩
  intro h
  have := (isSubclassOf_iff partialKB painter artist).2 h
  exact absurd this (by decide)

/-! ## Layer transport on the worked fragment -/

/-- Class facts are the same at the full and the truthy layer. -/
theorem artistKB_class_view_layer_invariant :
    classView.project StatementLayer.full artistKB
      = classView.project StatementLayer.truthy artistKB :=
  classView_project_eq _ _ artistKB

/-- Transporting the class view between those layers is the identity. -/
theorem artistKB_class_transport_id :
    classTransition_full_truthy.forward (classView.project StatementLayer.full artistKB)
      = classView.project StatementLayer.truthy artistKB :=
  classTransition_full_truthy.forwardProjects artistKB

/-- The same `painter ⊑ artist` statement, at normal and at preferred rank. -/
def normalRankKB : KB where
  entities := [painter, artist]
  statements := [⟨painter, P279, artist, Rank.normal⟩]

/-- The preferred-rank variant. -/
def preferredRankKB : KB where
  entities := [painter, artist]
  statements := [⟨painter, P279, artist, Rank.preferred⟩]

/-- The direct RDF layer cannot tell the two apart ... -/
theorem ranked_variants_agree_directly :
    rdfView.project RdfLayer.direct normalRankKB
      = rdfView.project RdfLayer.direct preferredRankKB := by decide

/-- ... while the reified layer keeps the distinction. -/
theorem ranked_variants_differ_reified :
    rdfView.project RdfLayer.reified normalRankKB
      ≠ rdfView.project RdfLayer.reified preferredRankKB := by decide

/-- So no transport can undo the move to the direct layer. -/
theorem no_transport_back_from_direct :
    IsEmpty (ViewFamily.Transition rdfView RdfLayer.direct RdfLayer.reified) :=
  no_transition_direct_reified

end Example

end Wikidata
