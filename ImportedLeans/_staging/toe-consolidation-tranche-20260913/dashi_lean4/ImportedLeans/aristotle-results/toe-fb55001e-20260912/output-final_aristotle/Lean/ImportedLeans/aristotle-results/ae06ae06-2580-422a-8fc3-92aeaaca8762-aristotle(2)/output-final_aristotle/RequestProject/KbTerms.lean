import RequestProject.Terms
import RequestProject.Generated.KbTerms
import RequestProject.DefectReport

/-!
# The terms of the corpus

`RequestProject.Terms` formalises Wikidata's *term* layer — the labels,
descriptions and aliases of an entity — and its two constraints.  This module
fills that layer with the real thing: `scripts/fetch_kb_terms.py` downloads the
English terms of **every** entity of the downloaded corpus (the 1578 items of
`DefectReport.corpus`, plus the two properties `P31` and `P279` that carry its
statements) and compiles them into `Wikidata.Generated.kbTerms`; everything
below is then decided by computation on that table.

* `kbTerms_size`, `kbTerms_aliases_count` — 1580 entities, 3515 aliases;
* `kbTerms_covers_corpus` and `corpus_item_has_label` — **every item of the
  corpus carries an English label**, so every identifier the knowledge base
  talks about has a name;
* `kbTerms_uniqueOk_en` — the table satisfies Wikidata's label/description
  uniqueness constraint, hence a label-plus-description search returns at most
  one item (`byLabelDesc_subsingleton_kbTerms`).  The check is decided through
  `TermStore.uniqueOk_of_nodup_pairsOf`, proved here: it is enough that the
  (label, description) pairs are pairwise distinct, which is a single pass
  instead of a comparison of every pair of items;
* `kbTerms_aliasOk` — no alias repeats the label of its own item;
* `element_byLabel`, `element_byTerm` — labels do *not* identify items: two
  items of the corpus are both labelled *element*, and a search for the alias
  *element of a set* matches two items again.  These are exactly the items that
  `RequestProject.PeriodicityReport` finds on a `subclass of` cycle, which is
  what a duplicated notion looks like from the term side.
-/

namespace Wikidata
namespace KbTerms

open Wikidata.Generated

/-! ### A one-pass form of the uniqueness constraint -/

namespace TermStoreAux

/-- The (label, description) pairs of the items that carry both, in the order of
the table. -/
def pairsOf (st : TermStore) (l : Lang) : List (String × String) :=
  st.items.filterMap fun q =>
    match st.labelOf q l, st.descOf q l with
    | some s, some d => some (s, d)
    | _, _ => none

/-- **Distinct pairs suffice**: if no two entries of the table produce the same
(label, description) pair, the uniqueness constraint holds.  This replaces the
quadratic check `TermStore.uniqueOk` by one pass and a duplicate test. -/
theorem uniqueOk_of_nodup_pairsOf {st : TermStore} {l : Lang}
    (h : (pairsOf st l).Nodup) : st.uniqueOk l = true := by
  refine (st.uniqueOk_iff l).2 ?_
  intro a ha b hb s d hla hda hlb hdb
  by_contra hne
  have hpair : List.Pairwise
      (fun q q' => ∀ p, (match st.labelOf q l, st.descOf q l with
          | some s, some d => some (s, d)
          | _, _ => none) = some p →
        ∀ p', (match st.labelOf q' l, st.descOf q' l with
          | some s, some d => some (s, d)
          | _, _ => none) = some p' → p ≠ p') st.items := by
    have := h
    rw [pairsOf, List.nodup_iff_pairwise_ne] at this
    exact List.pairwise_filterMap.1 this
  have hsymm : Symmetric
      (fun q q' : Qid => ∀ p, (match st.labelOf q l, st.descOf q l with
          | some s, some d => some (s, d)
          | _, _ => none) = some p →
        ∀ p', (match st.labelOf q' l, st.descOf q' l with
          | some s, some d => some (s, d)
          | _, _ => none) = some p' → p ≠ p') := by
    intro x y hxy p hp p' hp' hpp
    exact hxy p' hp' p hp hpp.symm
  have := hpair.forall hsymm ha hb hne
  exact this (s, d) (by rw [hla, hda]) (s, d) (by rw [hlb, hdb]) rfl

end TermStoreAux

open TermStoreAux

/-! ### The table -/

/-- The term table covers 1580 entities. -/
theorem kbTerms_size : kbTerms.items.length = 1580 := by native_decide

/-- Every entity of the table carries an English label. -/
theorem kbTerms_all_labelled :
    kbTerms.items.all (fun q => (kbTerms.labelOf q "en").isSome) = true := by native_decide

/-- 1519 of them also carry an English description. -/
theorem kbTerms_desc_count :
    (kbTerms.items.filter (fun q => (kbTerms.descOf q "en").isSome)).length = 1519 := by
  native_decide

/-- The table records 3515 aliases. -/
theorem kbTerms_aliases_count :
    (kbTerms.entries.map (fun e => e.2.aliases.length)).sum = 3515 := by native_decide

/-! ### Coverage of the corpus -/

/-- **Every item of the downloaded corpus carries an English label.** -/
theorem kbTerms_covers_corpus : kbTerms.labelledOk DefectReport.corpus "en" = true := by
  native_decide

/-- Read off: each of the 1578 items of the corpus has a name in the term
table. -/
theorem corpus_item_has_label {q : Qid} (hq : q ∈ DefectReport.corpus.items) :
    ∃ s, kbTerms.labelOf q "en" = some s :=
  kbTerms.exists_label_of_labelledOk kbTerms_covers_corpus hq

/-! ### The two term constraints -/

/-- No two entities of the corpus share both their label and their description. -/
theorem kbTerms_pairs_nodup : (pairsOf kbTerms "en").Nodup := by native_decide

/-- **Wikidata's uniqueness constraint holds on the whole corpus.** -/
theorem kbTerms_uniqueOk_en : kbTerms.uniqueOk "en" = true :=
  uniqueOk_of_nodup_pairsOf kbTerms_pairs_nodup

/-- Hence a search by label *and* description picks out at most one item. -/
theorem byLabelDesc_subsingleton_kbTerms {s d : String} {a b : Qid}
    (ha : a ∈ kbTerms.byLabelDesc "en" s d) (hb : b ∈ kbTerms.byLabelDesc "en" s d) : a = b :=
  kbTerms.byLabelDesc_subsingleton kbTerms_uniqueOk_en ha hb

/-- **No alias repeats the label of its own item.** -/
theorem kbTerms_aliasOk : kbTerms.aliasOk = true := by native_decide

/-- Read off: the label of an item of the corpus is never one of its own
aliases. -/
theorem label_notMem_aliases_kbTerms {q : Qid} (hq : q ∈ kbTerms.items) {s : String}
    (hl : kbTerms.labelOf q "en" = some s) : s ∉ kbTerms.aliasesOf q "en" :=
  kbTerms.label_notMem_aliases kbTerms_aliasOk hq hl

/-! ### Labels do not identify items

The two items labelled *element* — *element* (Q379825), "any one of the distinct
objects that make up a set", and *element* (Q5358816), the category-theoretic
notion — are two of the three items that the periodicity search finds on a
`subclass of` cycle in `RequestProject.PeriodicityReport`.  The third,
*element of set* (Q36808958), carries the same alias as the first. -/

/-- Two items of the corpus are labelled *element*. -/
theorem element_byLabel :
    kbTerms.byLabel "en" "element" = [Qid.wd "Q379825", Qid.wd "Q5358816"] := by native_decide

/-- A search that also looks at aliases matches *element* (Q379825) and *element
of set* (Q36808958) for the same string. -/
theorem element_byTerm :
    kbTerms.byTerm "en" "element of a set" = [Qid.wd "Q379825", Qid.wd "Q36808958"] := by
  native_decide

/-- Their descriptions do tell them apart, as the uniqueness constraint
guarantees. -/
theorem element_byLabelDesc :
    kbTerms.byLabelDesc "en" "element" "concept in category theory" =
      [Qid.wd "Q5358816"] := by native_decide

/-- The property `P31` is in the table too, with the aliases a search box would
use for it. -/
theorem p31_byTerm : Qid.wd "P31" ∈ kbTerms.byTerm "en" "is a" := by native_decide

end KbTerms
end Wikidata
