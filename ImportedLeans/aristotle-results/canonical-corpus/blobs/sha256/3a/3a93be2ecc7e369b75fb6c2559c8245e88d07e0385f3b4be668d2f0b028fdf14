import RequestProject.Engine

/-!
# Labels, descriptions and aliases: the term layer

Besides its statements, every Wikidata item carries *terms*: a **label** and a
**description** in each language, and any number of **aliases**.  Terms are not
statements — they carry no ontological content — but they are governed by their
own constraints, the most important being:

* the pair (label, description) must be **unique** among items in each language,
  and
* an **alias must differ from the label** of its own item in that language.

This file formalises the term layer:

* `Wikidata.Terms` and `Wikidata.TermStore` — the terms of an item and the term
  table of a knowledge base, with the lookups `labelOf`, `descOf`, `aliasesOf`.
* `Wikidata.TermStore.uniqueOk` — the executable label/description uniqueness
  check, proved to be **exactly** the injectivity of `item ↦ (label, description)`
  on the items that carry both (`uniqueOk_iff`), so the checker neither over- nor
  under-approximates the constraint.
* `Wikidata.TermStore.aliasOk` — the executable alias check with its soundness
  theorem.
* Search: `byLabel`, `byTerm` and `byLabelDesc`, characterised by their defining
  property, with the theorem that under the uniqueness constraint a
  label-plus-description search returns **at most one** item — labels alone,
  however, do not identify an item, which is demonstrated by a fragment where
  three different items are all labelled *Mercury*.
-/

namespace Wikidata

/-- A language code, e.g. `"en"`. -/
abbrev Lang := String

/-- The terms of one item: labels and descriptions, one per language, and any
number of aliases. -/
structure Terms where
  /-- The label in each language. -/
  labels : List (Lang × String) := []
  /-- The description in each language. -/
  descriptions : List (Lang × String) := []
  /-- The aliases, as (language, string) pairs. -/
  aliases : List (Lang × String) := []
deriving DecidableEq, Repr, Inhabited

/-- The term table of a knowledge base. -/
structure TermStore where
  /-- The terms of each item. -/
  entries : List (Qid × Terms) := []
deriving DecidableEq, Repr, Inhabited

namespace TermStore

variable (st : TermStore)

/-- The items the term table knows about. -/
def items : List Qid := st.entries.map Prod.fst

/-- The terms of an item (empty if it has none). -/
def termsOf (q : Qid) : Terms := (st.entries.lookup q).getD {}

/-- The label of an item in a language, if any. -/
def labelOf (q : Qid) (l : Lang) : Option String := (st.termsOf q).labels.lookup l

/-- The description of an item in a language, if any. -/
def descOf (q : Qid) (l : Lang) : Option String := (st.termsOf q).descriptions.lookup l

/-- The aliases of an item in a language. -/
def aliasesOf (q : Qid) (l : Lang) : List String :=
  ((st.termsOf q).aliases.filter (fun p => p.1 == l)).map Prod.snd

theorem mem_aliasesOf {q : Qid} {l : Lang} {s : String} :
    s ∈ st.aliasesOf q l ↔ (l, s) ∈ (st.termsOf q).aliases := by
  simp only [aliasesOf, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hmem, rfl⟩, rfl⟩; exact hmem
  · intro hmem; exact ⟨(l, s), ⟨hmem, rfl⟩, rfl⟩

/-! ### The label/description uniqueness constraint -/

/-- The executable uniqueness check: in the language `l`, no two items share both
their label and their description. -/
def uniqueOk (l : Lang) : Bool :=
  st.items.all fun a => st.items.all fun b =>
    !((st.labelOf a l).isSome && (st.descOf a l).isSome &&
        (st.labelOf a l == st.labelOf b l) && (st.descOf a l == st.descOf b l)) || (a == b)

/-- **The checker is exactly the constraint**: `uniqueOk` holds precisely when the
assignment of a (label, description) pair to an item is injective, among the items
carrying both in that language. -/
theorem uniqueOk_iff (l : Lang) :
    st.uniqueOk l = true ↔
      ∀ a ∈ st.items, ∀ b ∈ st.items, ∀ s d : String,
        st.labelOf a l = some s → st.descOf a l = some d →
        st.labelOf b l = some s → st.descOf b l = some d → a = b := by
  simp only [uniqueOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
  constructor
  · intro h a ha b hb s d hla hda hlb hdb
    rcases h a ha b hb with (((h₁ | h₁) | h₁) | h₁) | h₁
    · rw [hla] at h₁; exact absurd h₁ (by simp)
    · rw [hda] at h₁; exact absurd h₁ (by simp)
    · rw [hla, hlb] at h₁; simp at h₁
    · rw [hda, hdb] at h₁; simp at h₁
    · exact h₁
  · intro h a ha b hb
    by_cases hab : a = b
    · exact Or.inr hab
    refine Or.inl ?_
    by_cases hla : st.labelOf a l = none
    · exact Or.inl (Or.inl (Or.inl hla))
    by_cases hda : st.descOf a l = none
    · exact Or.inl (Or.inl (Or.inr hda))
    obtain ⟨s, hs⟩ : ∃ s, st.labelOf a l = some s := Option.ne_none_iff_exists'.1 hla
    obtain ⟨d, hd⟩ : ∃ d, st.descOf a l = some d := Option.ne_none_iff_exists'.1 hda
    by_cases hlb : st.labelOf b l = some s
    · refine Or.inr ?_
      rw [beq_eq_false_iff_ne, ne_eq, hd]
      intro hdb
      exact hab (h a ha b hb s d hs hd hlb hdb.symm)
    · refine Or.inl (Or.inr ?_)
      rw [beq_eq_false_iff_ne, ne_eq, hs]
      intro hcon
      exact hlb hcon.symm

/-- Soundness of the uniqueness check, in the form it is used: two items of the
term table with the same label *and* the same description in some language are
the same item. -/
theorem eq_of_uniqueOk {l : Lang} (h : st.uniqueOk l = true) {a b : Qid}
    (ha : a ∈ st.items) (hb : b ∈ st.items) {s d : String}
    (hla : st.labelOf a l = some s) (hda : st.descOf a l = some d)
    (hlb : st.labelOf b l = some s) (hdb : st.descOf b l = some d) : a = b :=
  (st.uniqueOk_iff l).1 h a ha b hb s d hla hda hlb hdb

/-! ### The alias constraint -/

/-- The executable alias check: no alias repeats the label of its own item. -/
def aliasOk : Bool :=
  st.items.all fun a => (st.termsOf a).aliases.all fun p => !(st.labelOf a p.1 == some p.2)

/-- Soundness of the alias check: the label of an item is never among its aliases. -/
theorem label_notMem_aliases (h : st.aliasOk = true) {a : Qid} (ha : a ∈ st.items) {l : Lang}
    {s : String} (hl : st.labelOf a l = some s) : s ∉ st.aliasesOf a l := by
  intro hmem
  have hp : (l, s) ∈ (st.termsOf a).aliases := (st.mem_aliasesOf).1 hmem
  simp only [aliasOk, List.all_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact h a ha (l, s) hp hl

/-! ### Search -/

/-- The items whose label in a language is a given string. -/
def byLabel (l : Lang) (s : String) : List Qid :=
  st.items.filter (fun q => st.labelOf q l == some s)

/-- The items whose label *or* one of whose aliases in a language is a given
string — what a search box matches. -/
def byTerm (l : Lang) (s : String) : List Qid :=
  st.items.filter (fun q => (st.labelOf q l == some s) || s ∈ st.aliasesOf q l)

/-- The items with a given label *and* a given description in a language. -/
def byLabelDesc (l : Lang) (s d : String) : List Qid :=
  st.items.filter (fun q => (st.labelOf q l == some s) && (st.descOf q l == some d))

@[simp] theorem mem_byLabel {l : Lang} {s : String} {q : Qid} :
    q ∈ st.byLabel l s ↔ q ∈ st.items ∧ st.labelOf q l = some s := by
  simp [byLabel]

@[simp] theorem mem_byTerm {l : Lang} {s : String} {q : Qid} :
    q ∈ st.byTerm l s ↔ q ∈ st.items ∧ (st.labelOf q l = some s ∨ s ∈ st.aliasesOf q l) := by
  simp [byTerm]

@[simp] theorem mem_byLabelDesc {l : Lang} {s d : String} {q : Qid} :
    q ∈ st.byLabelDesc l s d ↔
      q ∈ st.items ∧ st.labelOf q l = some s ∧ st.descOf q l = some d := by
  simp [byLabelDesc]

/-- Searching by label is a weakening of searching by label and description. -/
theorem byLabelDesc_subset_byLabel {l : Lang} {s d : String} {q : Qid}
    (h : q ∈ st.byLabelDesc l s d) : q ∈ st.byLabel l s := by
  rw [mem_byLabelDesc] at h
  exact st.mem_byLabel.2 ⟨h.1, h.2.1⟩

/-- Every match of a label search is a match of a term search. -/
theorem byLabel_subset_byTerm {l : Lang} {s : String} {q : Qid} (h : q ∈ st.byLabel l s) :
    q ∈ st.byTerm l s := by
  rw [mem_byLabel] at h
  exact st.mem_byTerm.2 ⟨h.1, Or.inl h.2⟩

/-- **Under the uniqueness constraint a label-plus-description search identifies
at most one item.** -/
theorem byLabelDesc_subsingleton {l : Lang} (h : st.uniqueOk l = true) {s d : String}
    {a b : Qid} (ha : a ∈ st.byLabelDesc l s d) (hb : b ∈ st.byLabelDesc l s d) : a = b := by
  rw [mem_byLabelDesc] at ha hb
  exact st.eq_of_uniqueOk h ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2

/-! ### Terms and the knowledge base -/

/-- Every item of the knowledge base carries a label in the given language. -/
def labelledOk (kb : KB) (l : Lang) : Bool :=
  kb.items.all fun q => (st.labelOf q l).isSome

/-- Soundness of the coverage check. -/
theorem exists_label_of_labelledOk {kb : KB} {l : Lang} (h : st.labelledOk kb l = true) {q : Qid}
    (hq : q ∈ kb.items) : ∃ s, st.labelOf q l = some s := by
  simp only [labelledOk, List.all_eq_true, Option.isSome_iff_exists] at h
  exact h q hq

end TermStore

/-! ### A worked fragment: three items labelled *Mercury*

*Mercury* is the name of a planet (Q308), of a chemical element (Q925) and of a
Roman god (Q1084) — labels do not identify items, descriptions are what
disambiguate them. -/

namespace TermExample

open Wikidata

/-- The planet Mercury. -/
def planet : Qid := .wd "Q308"
/-- The chemical element mercury. -/
def element : Qid := .wd "Q925"
/-- The Roman god Mercury. -/
def god : Qid := .wd "Q1084"

/-- A small term table. -/
def mercury : TermStore where
  entries :=
    [(planet,
        { labels := [("en", "Mercury"), ("de", "Merkur")],
          descriptions := [("en", "planet closest to the Sun")],
          aliases := [("en", "Mercury (planet)")] }),
     (element,
        { labels := [("en", "mercury"), ("de", "Quecksilber")],
          descriptions := [("en", "chemical element with symbol Hg")],
          aliases := [("en", "quicksilver"), ("en", "hydrargyrum")] }),
     (god,
        { labels := [("en", "Mercury"), ("de", "Merkur")],
          descriptions := [("en", "Roman god of commerce")],
          aliases := [] })]

/-- The table satisfies the label/description uniqueness constraint in English … -/
theorem mercury_uniqueOk_en : mercury.uniqueOk "en" = true := by decide

/-- … and in German, where the planet and the god share the label *Merkur*: neither
carries a German description, so the constraint — which only bites when both a
label and a description are present — is satisfied. -/
theorem mercury_uniqueOk_de : mercury.uniqueOk "de" = true := by decide

/-- No alias repeats its own item's label. -/
theorem mercury_aliasOk : mercury.aliasOk = true := by decide

/-- A label search for *Mercury* returns two different items: labels are not
identifiers. -/
theorem mercury_byLabel : mercury.byLabel "en" "Mercury" = [planet, god] := by decide

/-- Adding the description picks out exactly one of them. -/
theorem mercury_byLabelDesc :
    mercury.byLabelDesc "en" "Mercury" "Roman god of commerce" = [god] := by decide

/-- A term search also finds the item through an alias. -/
theorem mercury_byTerm_alias : mercury.byTerm "en" "quicksilver" = [element] := by decide

/-- The same knowledge base with a duplicated label *and* description is rejected
by the uniqueness check. -/
def mercuryBad : TermStore where
  entries :=
    [(planet,
        { labels := [("en", "Mercury")],
          descriptions := [("en", "Roman god of commerce")] }),
     (god,
        { labels := [("en", "Mercury")],
          descriptions := [("en", "Roman god of commerce")] })]

theorem mercuryBad_not_uniqueOk : mercuryBad.uniqueOk "en" = false := by decide

/-- An alias equal to the item's own label is rejected. -/
def mercuryBadAlias : TermStore where
  entries := [(planet, { labels := [("en", "Mercury")], aliases := [("en", "Mercury")] })]

theorem mercuryBadAlias_not_aliasOk : mercuryBadAlias.aliasOk = false := by decide

end TermExample

end Wikidata
