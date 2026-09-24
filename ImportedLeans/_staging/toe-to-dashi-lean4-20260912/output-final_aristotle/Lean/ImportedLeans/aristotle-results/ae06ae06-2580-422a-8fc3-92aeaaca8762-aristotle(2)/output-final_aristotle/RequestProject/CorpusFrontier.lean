import RequestProject.Generated.Core
import RequestProject.Generated.Frontier
import RequestProject.Generated.Frontier2
import RequestProject.Normalize
import RequestProject.Merge

/-!
# What the corpus was missing: the frontier of the crawl

The eleven downloads that make up `data/core.wdkb` were obtained by following
`instance of` (P31) and `subclass of` (P279) links **two steps** from each seed.
A crawl of bounded depth always stops somewhere: the items reached on the last
step were recorded, but their own P31/P279 statements were never asked for.
Those items are the *frontier* of the crawl — items the corpus mentions and
about which it says nothing.

`data/frontier.wdkb` is the download that closes that gap: every item of the
corpus without an outgoing statement was queried again, one step further, and
the answer compiled to `RequestProject.Generated.Frontier` (477 items, 853
statements).  This file measures what was missing.

* `KB.rootlessL` — the items of a base with no outgoing P279 and no outgoing P31
  statement, with `KB.mem_rootlessL_iff` fixing its meaning;
* `Corpus.core_rootless_card` — the corpus had **144** such items;
* `Corpus.frontier_leaves_one_root` — after the new download exactly **one** of
  them is still without a statement, namely `Q16003513`;
* `KB.gainedL` — the items that reach a given class in the larger base but not in
  the smaller one, with `KB.mem_gainedL` fixing its meaning on the abstract
  relations;
* `Corpus.frontier_gained_entity_card` — **131** of the 144 frontier items become
  subclasses of `entity` (Q35120), the top of the Wikidata ontology, only once the
  missing layer is downloaded; `Corpus.coreExtended_q111513007_sub_entity` and
  `Corpus.core_not_q111513007_sub_entity` spell one of them out;
* `Corpus.coreExtended_entails_core`, `Corpus.coreExtended_entails_frontier` — the
  extended corpus loses nothing: it still derives every statement of the old
  corpus and every statement of the new download;
* and the same question asked again of the extended corpus: it has **70** items it
  says nothing about, `data/frontier2.wdkb` asks Wikidata about those, and after
  that round **42** are left (`Corpus.coreExtended_rootless_card`,
  `Corpus.coreExtended2_rootless_card`) — of the 70, again all but `Q16003513`
  turned out to have statements the corpus was missing
  (`Corpus.round_two_leaves_one_root`).
-/

namespace Wikidata
namespace KB

/-! ### Items a base says nothing about -/

/-- The items of a base with neither a `subclass of` nor an `instance of`
statement of their own: the frontier at which a crawl of bounded depth stopped,
together with the genuine roots of the hierarchy. -/
def rootlessL (kb : KB) : List Qid :=
  kb.items.filter (fun q => kb.supersL q == [] && kb.directClassesL q == [])

theorem supersL_eq_nil_iff {kb : KB} {q : Qid} :
    kb.supersL q = [] ↔ ∀ b, ¬ kb.Sub q b := by
  constructor
  · intro h b hb
    have hmem : b ∈ kb.supersL q := by
      simp only [supersL, List.mem_map, List.mem_filter]
      exact ⟨(q, b), ⟨hb, by simp⟩, rfl⟩
    simp [h] at hmem
  · intro h
    simp only [supersL, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hq
    have hp1 : p.1 = q := by simpa using hq
    refine h p.2 ?_
    show (q, p.2) ∈ kb.sub
    rw [← hp1]
    simpa using hp

theorem directClassesL_eq_nil_iff {kb : KB} {q : Qid} :
    kb.directClassesL q = [] ↔ ∀ c, ¬ kb.Inst q c := by
  constructor
  · intro h c hc
    have hmem : c ∈ kb.directClassesL q := by
      simp only [directClassesL, List.mem_map, List.mem_filter]
      exact ⟨(q, c), ⟨hc, by simp⟩, rfl⟩
    simp [h] at hmem
  · intro h
    simp only [directClassesL, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hq
    have hp1 : p.1 = q := by simpa using hq
    refine h p.2 ?_
    show (q, p.2) ∈ kb.inst
    rw [← hp1]
    simpa using hp

/-- An item is rootless exactly when the base declares it and states nothing
about what it is a subclass or an instance of. -/
theorem mem_rootlessL_iff {kb : KB} {q : Qid} :
    q ∈ kb.rootlessL ↔ q ∈ kb.items ∧ (∀ b, ¬ kb.Sub q b) ∧ (∀ c, ¬ kb.Inst q c) := by
  simp [rootlessL, List.mem_filter, ← supersL_eq_nil_iff, ← directClassesL_eq_nil_iff]

/-! ### What a further download adds -/

/-- Those items of `qs` that reach `root` through `subclass of` in `kb₁` but not
already in `kb₀`. -/
def gainedL (kb₀ kb₁ : KB) (qs : List Qid) (root : Qid) : List Qid :=
  qs.filter fun q => kb₁.isSubclassOf q root && !kb₀.isSubclassOf q root

/-- The meaning of `gainedL`, on the abstract relations: a listed item is a
derived subclass of `root` in the larger base and not in the smaller one. -/
theorem mem_gainedL {kb₀ kb₁ : KB} (h₀ : kb₀.wellFormed = true) (h₁ : kb₁.wellFormed = true)
    {qs : List Qid} {root q : Qid} (hq : q ∈ gainedL kb₀ kb₁ qs root) :
    Relation.ReflTransGen kb₁.Sub q root ∧ ¬ Relation.ReflTransGen kb₀.Sub q root := by
  simp only [gainedL, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hq
  obtain ⟨-, h₁', h₀'⟩ := hq
  refine ⟨(isSubclassOf_iff h₁ _ _).1 h₁', fun h => ?_⟩
  have hcontra := (isSubclassOf_iff h₀ _ _).2 h
  rw [hcontra] at h₀'
  exact Bool.noConfusion h₀'

end KB

namespace Corpus

open Wikidata.Generated

/-! ### The frontier of the eleven downloads -/

/-- **The corpus mentioned 144 items it said nothing about.** -/
theorem core_rootless_card : Core.kb.rootlessL.length = 144 := by native_decide

/-- The corpus, extended by the download that asks the frontier items what they
are subclasses and instances of, and deduplicated. -/
def coreExtended : KB := (Core.kb.merge Frontier.kb).normalize

/-- The extended corpus is well formed, so all the certified queries apply to
it. -/
theorem coreExtended_wellFormed : coreExtended.wellFormed = true :=
  KB.normalize_wellFormed (KB.wellFormed_merge Core.kb_wellFormed Frontier.kb_wellFormed)

/-- How large the extended corpus is: 749 items, against the 588 of the corpus. -/
theorem coreExtended_card : coreExtended.items.length = 749 := by native_decide

/-- **Exactly one of the 144 frontier items is a genuine root**: after the new
download every one of them except `Q16003513` (*Wikimedia entity*) has a
`subclass of` or an `instance of` statement of its own. -/
theorem frontier_leaves_one_root :
    (let R := coreExtended.rootlessL; Core.kb.rootlessL.filter (fun q => q ∈ R)) =
      [Qid.wd "Q16003513"] := by
  native_decide

/-- Spelled out on the abstract relations: `Q16003513` is declared by the extended
corpus, and the extended corpus states nothing about what it is a subclass or an
instance of. -/
theorem q16003513_rootless :
    Qid.wd "Q16003513" ∈ coreExtended.items ∧
      (∀ b, ¬ coreExtended.Sub (Qid.wd "Q16003513") b) ∧
      (∀ c, ¬ coreExtended.Inst (Qid.wd "Q16003513") c) :=
  KB.mem_rootlessL_iff.1 (by native_decide)

/-! ### What the missing layer adds -/

/-- **131 of the 144 frontier items become subclasses of `entity` (Q35120) — the
top of the Wikidata class hierarchy — only after the missing layer is
downloaded.** -/
theorem frontier_gained_entity_card :
    (KB.gainedL Core.kb coreExtended Core.kb.rootlessL (Qid.wd "Q35120")).length = 131 := by
  native_decide

/-- Every item counted by `frontier_gained_entity_card` really is a derived
subclass of `entity` in the extended corpus and really is not one in the corpus
as it stood. -/
theorem frontier_gained_entity_meaning :
    ∀ q ∈ KB.gainedL Core.kb coreExtended Core.kb.rootlessL (Qid.wd "Q35120"),
      Relation.ReflTransGen coreExtended.Sub q (Qid.wd "Q35120") ∧
        ¬ Relation.ReflTransGen Core.kb.Sub q (Qid.wd "Q35120") :=
  fun _ hq => KB.mem_gainedL Core.kb_wellFormed coreExtended_wellFormed hq

/-- One of them by name: `Q111513007` is a subclass of `entity` in the extended
corpus … -/
theorem coreExtended_q111513007_sub_entity :
    Relation.ReflTransGen coreExtended.Sub (Qid.wd "Q111513007") (Qid.wd "Q35120") :=
  (KB.isSubclassOf_iff coreExtended_wellFormed _ _).1 (by native_decide)

/-- … and is not one in the corpus as it stood before the missing layer was
downloaded. -/
theorem core_not_q111513007_sub_entity :
    ¬ Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q111513007") (Qid.wd "Q35120") := by
  intro h
  have hsub : Core.kb.isSubclassOf (Qid.wd "Q111513007") (Qid.wd "Q35120") = true :=
    (KB.isSubclassOf_iff Core.kb_wellFormed _ _).2 h
  revert hsub
  native_decide

/-! ### And nothing is lost -/

/-- The extended corpus entails the old corpus: every statement that was there
before is still derivable.  No evaluation is needed — this follows from the
general theorems about merging and deduplication. -/
theorem coreExtended_entails_core : coreExtended.Entails Core.kb = true :=
  KB.entails_trans coreExtended_wellFormed
    (KB.wellFormed_merge Core.kb_wellFormed Frontier.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge Core.kb_wellFormed Frontier.kb_wellFormed))
    (KB.merge_entails_left Core.kb_wellFormed Frontier.kb_wellFormed)

/-- The extended corpus entails the new download as well. -/
theorem coreExtended_entails_frontier : coreExtended.Entails Frontier.kb = true :=
  KB.entails_trans coreExtended_wellFormed
    (KB.wellFormed_merge Core.kb_wellFormed Frontier.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge Core.kb_wellFormed Frontier.kb_wellFormed))
    (KB.merge_entails_right Core.kb_wellFormed Frontier.kb_wellFormed)

/-- Consequently every `subclass of` statement of the corpus and of the new
download is derivable in the extended corpus. -/
theorem coreExtended_derives_sub :
    ∀ p ∈ Core.kb.sub ++ Frontier.kb.sub,
      Relation.ReflTransGen coreExtended.Sub p.1 p.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact (KB.isSubclassOf_iff coreExtended_wellFormed _ _).1
      (KB.entails_sub coreExtended_entails_core (show Core.kb.Sub p.1 p.2 from hp))
  · exact (KB.isSubclassOf_iff coreExtended_wellFormed _ _).1
      (KB.entails_sub coreExtended_entails_frontier (show Frontier.kb.Sub p.1 p.2 from hp))

/-! ### Asking the same question again

Every round of downloading declares items of its own, so the frontier moves
rather than disappears; but it shrinks, and the items that stay rootless are the
genuine roots. -/

/-- The extended corpus mentions 70 items it says nothing about — the frontier of
the frontier download. -/
theorem coreExtended_rootless_card : coreExtended.rootlessL.length = 70 := by native_decide

/-- The corpus after a second round of downloading. -/
def coreExtended2 : KB := (coreExtended.merge Frontier2.kb).normalize

/-- It is well formed too. -/
theorem coreExtended2_wellFormed : coreExtended2.wellFormed = true :=
  KB.normalize_wellFormed (KB.wellFormed_merge coreExtended_wellFormed Frontier2.kb_wellFormed)

/-- 847 items after the second round. -/
theorem coreExtended2_card : coreExtended2.items.length = 847 := by native_decide

/-- **The frontier shrinks**: 144 items with nothing said about them, then 70,
then 42. -/
theorem coreExtended2_rootless_card : coreExtended2.rootlessL.length = 42 := by native_decide

/-- And again exactly one of the items asked about in the second round is a
genuine root: `Q16003513`. -/
theorem round_two_leaves_one_root :
    (let R := coreExtended2.rootlessL; coreExtended.rootlessL.filter (fun q => q ∈ R)) =
      [Qid.wd "Q16003513"] := by
  native_decide

/-- The corpus of the second round still derives everything the first round
derived. -/
theorem coreExtended2_entails_coreExtended : coreExtended2.Entails coreExtended = true :=
  KB.entails_trans coreExtended2_wellFormed
    (KB.wellFormed_merge coreExtended_wellFormed Frontier2.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended_wellFormed Frontier2.kb_wellFormed))
    (KB.merge_entails_left coreExtended_wellFormed Frontier2.kb_wellFormed)

/-- … and everything the second download stated. -/
theorem coreExtended2_entails_frontier2 : coreExtended2.Entails Frontier2.kb = true :=
  KB.entails_trans coreExtended2_wellFormed
    (KB.wellFormed_merge coreExtended_wellFormed Frontier2.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended_wellFormed Frontier2.kb_wellFormed))
    (KB.merge_entails_right coreExtended_wellFormed Frontier2.kb_wellFormed)

end Corpus
end Wikidata
