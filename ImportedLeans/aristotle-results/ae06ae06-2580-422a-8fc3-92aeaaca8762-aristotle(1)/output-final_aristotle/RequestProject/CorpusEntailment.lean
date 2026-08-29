import RequestProject.Generated.Core
import RequestProject.Generated.DouglasAdams
import RequestProject.Generated.UpperOntology
import RequestProject.Generated.Geography
import RequestProject.Generated.CreativeWorks
import RequestProject.Generated.Science
import RequestProject.Generated.Technology
import RequestProject.Generated.Mathematics
import RequestProject.Generated.LifeSciences
import RequestProject.Generated.Society
import RequestProject.Generated.Chemistry
import RequestProject.Generated.Events

/-!
# The merged corpus keeps everything the individual downloads knew

`data/core.wdkb` is built by merging the eleven downloaded fragments and then
*deduplicating* them: repeated items and repeated statements — of which
overlapping downloads produce many — are dropped.  Deduplication is proved not
to change any answer in `RequestProject/Normalize.lean`, but that theorem is
about `KB.normalize` in the abstract.  Here the claim is checked for the actual
compiled data: **the corpus entails every one of the eleven fragments**, so
nothing any single download stated was lost on the way in.

* `Corpus.fragments` — the eleven compiled fragments.
* `Corpus.core_entails_fragments` — `Core.kb.Entails` holds for each of them.
* `Corpus.core_derives_fragment_sub`, `Corpus.core_derives_fragment_inst` — the
  consequence, spelled out on the abstract relations: every `subclass of` and
  every `instance of` statement of every fragment is derivable in the corpus.
-/

namespace Wikidata
namespace Corpus

open Wikidata.Generated

/-- The eleven downloaded fragments that `data/core.wdkb` is merged from. -/
def fragments : List KB :=
  [DouglasAdams.kb, UpperOntology.kb, Geography.kb, CreativeWorks.kb, Science.kb,
    Technology.kb, Mathematics.kb, LifeSciences.kb, Society.kb, Chemistry.kb, Events.kb]

/-- **The merged corpus entails every fragment it was built from.**  Checked in
one pass over a single closure table of the corpus. -/
theorem core_entails_fragments : ∀ kb' ∈ fragments, Core.kb.Entails kb' = true := by
  have h : Core.kb.EntailsAllT fragments = true := by native_decide
  rw [KB.EntailsAllT_eq, List.all_eq_true] at h
  exact fun kb' hkb => h kb' (by simpa using hkb)

/-- Every `subclass of` statement of every downloaded fragment is derivable in
the merged corpus. -/
theorem core_derives_fragment_sub :
    ∀ kb' ∈ fragments, ∀ p ∈ kb'.sub, Relation.ReflTransGen Core.kb.Sub p.1 p.2 := by
  intro kb' hkb p hp
  exact (KB.isSubclassOf_iff Core.kb_wellFormed _ _).1
    (KB.entails_sub (core_entails_fragments kb' hkb) (show kb'.Sub p.1 p.2 from hp))

/-- Every `instance of` statement of every downloaded fragment is derivable in
the merged corpus. -/
theorem core_derives_fragment_inst :
    ∀ kb' ∈ fragments, ∀ p ∈ kb'.inst,
      ∃ d, Core.kb.Inst p.1 d ∧ Relation.ReflTransGen Core.kb.Sub d p.2 := by
  intro kb' hkb p hp
  exact (KB.isInstanceOf_iff Core.kb_wellFormed _ _).1
    (KB.entails_inst (core_entails_fragments kb' hkb) (show kb'.Inst p.1 p.2 from hp))

end Corpus
end Wikidata
