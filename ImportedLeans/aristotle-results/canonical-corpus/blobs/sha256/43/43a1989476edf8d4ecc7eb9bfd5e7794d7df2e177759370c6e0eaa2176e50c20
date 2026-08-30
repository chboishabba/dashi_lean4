import RequestProject.Engine

/-!
# Grounding the vocabulary in Wikidata

Every identifier this development talks about — `P279`, `Q5`, `Q18647515`, … — is
supposed to be the identifier of a real Wikidata entity, and every notion the
formalisation names is supposed to be the notion Wikidata attaches to that
entity.  This file provides the machinery that makes "supposed to be" checkable:

* `Wikidata.Gloss` is one grounded term: an entity identifier together with the
  English label, the English description and the English Wikipedia article
  Wikidata records for it, plus the two derived links `Gloss.conceptUrl` (the
  Wikidata page) and `Gloss.articleUrl` (the Wikipedia article);
* `Wikidata.Glossary` is a table of those, with `Glossary.lookup`,
  `Glossary.grounds` (is this identifier grounded?) and `Glossary.groundsKB`
  (is every Wikidata item of a knowledge base grounded?);
* `Glossary.wellFormed` is the executable health check on a table — well-shaped
  identifiers, non-empty labels, no identifier listed twice — and
  `Glossary.wellFormed_iff` says exactly what it means.

The theorems here are about *any* table; the table of this development is
`Wikidata.Generated.glossary`, downloaded from Wikidata by
`scripts/fetch_glossary.py`, and the statements that it covers the whole system
are in `RequestProject.Grounded`.
-/

namespace Wikidata

/-- One grounded term: what Wikidata says about one entity.

`article` is the title of the English Wikipedia article about the entity, and is
empty when the entity has none (most properties, and many items, have none). -/
structure Gloss where
  /-- The Wikidata entity identifier, e.g. `"Q5"` or `"P279"`. -/
  id : String
  /-- The label Wikidata gives the entity, e.g. `"human"`: its English label, or
  its language-independent (`mul`) label when it has no English one. -/
  label : String
  /-- The English description Wikidata gives the entity. -/
  description : String
  /-- The title of the English Wikipedia article, or `""` if there is none. -/
  article : String := ""
  /-- The identifier Wikidata answers with, which differs from `id` exactly when
  `id` is a redirect. -/
  canonical : String := ""
deriving DecidableEq, Repr, Inhabited

namespace Gloss

variable (g : Gloss)

/-- A property glossed, i.e. an entity of the `P…` namespace. -/
def isProperty : Bool := g.id.startsWith "P"

/-- An item glossed, i.e. an entity of the `Q…` namespace. -/
def isItem : Bool := g.id.startsWith "Q"

/-- The identifier is well shaped: a `Q` or a `P` followed by a positive number
written without a leading zero. -/
def idOk : Bool :=
  (g.isItem || g.isProperty) && g.id.length ≥ 2 &&
    (g.id.drop 1).all Char.isDigit && !(g.id.drop 1).startsWith "0"

/-- The address of the Wikidata page of the entity. -/
def conceptUrl : String :=
  if g.isProperty then "https://www.wikidata.org/wiki/Property:" ++ g.id
  else "https://www.wikidata.org/wiki/" ++ g.id

/-- Does the entity have an English Wikipedia article? -/
def hasArticle : Bool := g.article ≠ ""

/-- Is the identifier a redirect to another entity? -/
def isRedirect : Bool := g.canonical ≠ g.id

/-- The address of the English Wikipedia article about the entity, if it has one. -/
def articleUrl : Option String :=
  if g.hasArticle then some ("https://en.wikipedia.org/wiki/" ++ g.article.replace " " "_")
  else none

/-- The item identifier of the entity, as used by the knowledge bases of
`RequestProject.Engine`. -/
def qid : Qid := Qid.wd g.id

/-- A one-line rendering, `Q5 — human: … <url>`. -/
def render : String :=
  g.id ++ " — " ++ g.label ++ (if g.description = "" then "" else ": " ++ g.description) ++
    " <" ++ g.conceptUrl ++ ">"

@[simp] theorem qid_id : g.qid = Qid.wd g.id := rfl

theorem conceptUrl_eq_of_isItem (h : g.isProperty = false) :
    g.conceptUrl = "https://www.wikidata.org/wiki/" ++ g.id := by
  simp [conceptUrl, h]

theorem conceptUrl_eq_of_isProperty (h : g.isProperty = true) :
    g.conceptUrl = "https://www.wikidata.org/wiki/Property:" ++ g.id := by
  simp [conceptUrl, h]

theorem articleUrl_isSome_iff : g.articleUrl.isSome ↔ g.article ≠ "" := by
  by_cases h : g.article = "" <;> simp [articleUrl, hasArticle, h]

/-- In a list of glosses whose identifiers are distinct, looking an identifier up
finds the entry that carries it. -/
theorem find?_eq_some_of_mem :
    ∀ (l : List Gloss), (l.map Gloss.id).Nodup → ∀ {e : Gloss}, e ∈ l →
      l.find? (fun f => f.id == e.id) = some e
  | [], _, _, he => absurd he (by simp)
  | f :: fs, hnd, e, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists] at hnd
    rcases List.mem_cons.1 he with rfl | he'
    · simp
    · have hne : ¬ (f.id = e.id) := fun h => hnd.1 e ⟨he', h.symm⟩
      have hfe : (f.id == e.id) = false := by simpa using hne
      simp only [List.find?_cons, hfe]
      exact find?_eq_some_of_mem fs (by simpa using hnd.2) he'

end Gloss

/-- A glossary: the Wikidata entry of every entity a development refers to. -/
structure Glossary where
  /-- The grounded terms. -/
  entries : List Gloss
deriving DecidableEq, Repr, Inhabited

namespace Glossary

variable (G : Glossary)

/-- The identifiers the glossary grounds. -/
def ids : List String := G.entries.map Gloss.id

/-- The entry for an identifier, if the glossary has one. -/
def lookup (s : String) : Option Gloss := G.entries.find? (fun e => e.id == s)

/-- Is this identifier grounded? -/
def grounds (s : String) : Bool := (G.lookup s).isSome

/-- The label of an identifier, or the identifier itself when it is not grounded. -/
def labelOf (s : String) : String := ((G.lookup s).map Gloss.label).getD s

/-- Are all of these identifiers grounded? -/
def groundsAll (l : List String) : Bool := l.all G.grounds

/-- The Wikidata entities named by a list of item identifiers of a knowledge
base; the identifiers that are internal to the formalisation (`Qid.ont`,
`Qid.about`, `Qid.lvl`) name no Wikidata entity and are dropped. -/
def wdIds (l : List Qid) : List String :=
  l.filterMap fun q => match q with | .wd s => some s | _ => none

/-- Is every Wikidata item of this knowledge base grounded? -/
def groundsKB (kb : KB) : Bool := G.groundsAll (wdIds kb.items)

/-- The glossary is in good shape: well-shaped identifiers, no empty label, and
no identifier listed twice. -/
def wellFormed : Bool :=
  G.entries.all (fun e => e.idOk && e.label ≠ "") && G.ids.dedup.length == G.ids.length

/-- How many of the grounded entities have an English Wikipedia article. -/
def articleCount : ℕ := (G.entries.filter Gloss.hasArticle).length

/-- How many of the identifiers are redirects to another entity. -/
def redirectCount : ℕ := (G.entries.filter Gloss.isRedirect).length

/-! ### What the lookup means -/

theorem lookup_id {s : String} {e : Gloss} (h : G.lookup s = some e) : e.id = s := by
  have := List.find?_some h
  simpa using this

theorem mem_of_lookup {s : String} {e : Gloss} (h : G.lookup s = some e) : e ∈ G.entries :=
  List.mem_of_find?_eq_some h

theorem grounds_iff (s : String) : G.grounds s = true ↔ ∃ e ∈ G.entries, e.id = s := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ⟨e, mem_of_lookup G he, lookup_id G he⟩
  · rintro ⟨e, he, rfl⟩
    have : (G.entries.find? (fun f => f.id == e.id)).isSome := by
      rw [List.find?_isSome]
      exact ⟨e, he, by simp⟩
    simpa [grounds, lookup] using this

theorem mem_ids_iff (s : String) : s ∈ G.ids ↔ G.grounds s = true := by
  rw [grounds_iff]
  simp only [ids, List.mem_map]

theorem groundsAll_iff (l : List String) :
    G.groundsAll l = true ↔ ∀ s ∈ l, G.grounds s = true := by
  simp [groundsAll]

theorem groundsKB_iff (kb : KB) :
    G.groundsKB kb = true ↔ ∀ s : String, Qid.wd s ∈ kb.items → G.grounds s = true := by
  rw [groundsKB, groundsAll_iff]
  constructor
  · intro h s hs
    refine h s ?_
    simp only [wdIds, List.mem_filterMap]
    exact ⟨Qid.wd s, hs, rfl⟩
  · intro h s hs
    simp only [wdIds, List.mem_filterMap] at hs
    obtain ⟨q, hq, hqs⟩ := hs
    cases q with
    | wd u =>
      have hus : u = s := by simpa using hqs
      subst hus
      exact h u hq
    | ont _ => simp at hqs
    | about _ => simp at hqs
    | lvl _ => simp at hqs

theorem nodup_ids_of_wellFormed (hw : G.wellFormed = true) : G.ids.Nodup := by
  have h2 : G.ids.dedup.length = G.ids.length := by
    simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at hw
    exact hw.2
  have := List.Sublist.eq_of_length (List.dedup_sublist G.ids) h2
  rw [← this]
  exact G.ids.nodup_dedup

/-- The grounding is unambiguous: in a well-formed glossary, the entry found for
an identifier is *the* entry carrying it. -/
theorem lookup_eq_some_of_mem (hw : G.wellFormed = true) {e : Gloss} (he : e ∈ G.entries) :
    G.lookup e.id = some e := by
  exact Gloss.find?_eq_some_of_mem G.entries (nodup_ids_of_wellFormed G hw) he

theorem wellFormed_iff :
    G.wellFormed = true ↔
      ((∀ e ∈ G.entries, e.idOk = true ∧ e.label ≠ "") ∧ G.ids.Nodup) := by
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · intro e he
      have h1 : ∀ e ∈ G.entries, (e.idOk && (e.label ≠ "")) = true := by
        simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hw
        intro e he
        have := hw.1 e (by simpa using he)
        simpa using this
      have := h1 e he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · exact nodup_ids_of_wellFormed G hw
  · rintro ⟨h1, h2⟩
    have hlen : G.ids.dedup = G.ids := List.dedup_eq_self.2 h2
    simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨?_, by rw [hlen]⟩
    intro e he
    obtain ⟨ha, hb⟩ := h1 e (by simpa using he)
    simp [ha, hb]

/-! ### Rendering a glossary -/

/-- The glossary as text, one line per grounded term. -/
def render : String := String.intercalate "\n" (G.entries.map Gloss.render)

end Glossary

/-! ### Grounding the vocabulary of the development itself

The glossary grounds the *identifiers* the development mentions.  The notions the
development **defines** are grounded by a second table: a `GroundedTerm` pairs a
Lean declaration of this library with the Wikidata entity that is the notion it
formalises, and with the label Wikidata gives that entity.  Because `decl` is a
name literal, Lean refuses to elaborate an entry naming a declaration that does
not exist; because the label is recorded, the glossary can be used to check that
the entity really is the one we mean. -/

open Lean in
/-- One notion of the formalisation, grounded in Wikidata. -/
structure GroundedTerm where
  /-- The Lean declaration that formalises the notion. -/
  decl : Name
  /-- The Wikidata entity the notion is grounded in. -/
  entity : String
  /-- The English label Wikidata gives that entity. -/
  label : String
deriving DecidableEq, Repr, Inhabited

namespace Glossary

variable (G : Glossary)

/-- Is this notion grounded in an entity the glossary knows, under the label the
entry claims? -/
def checksTerm (t : GroundedTerm) : Bool :=
  ((G.lookup t.entity).map Gloss.label) == some t.label

/-- Are all these notions grounded, with the labels they claim? -/
def checksAll (ts : List GroundedTerm) : Bool := ts.all G.checksTerm

theorem checksTerm_iff (t : GroundedTerm) :
    G.checksTerm t = true ↔ ∃ e, G.lookup t.entity = some e ∧ e.label = t.label := by
  simp only [checksTerm, beq_iff_eq]
  cases h : G.lookup t.entity with
  | none => simp
  | some e => simp

theorem checksTerm_grounds {t : GroundedTerm} (h : G.checksTerm t = true) :
    G.grounds t.entity = true := by
  obtain ⟨e, he, _⟩ := (G.checksTerm_iff t).1 h
  simp [grounds, he]

theorem checksAll_iff (ts : List GroundedTerm) :
    G.checksAll ts = true ↔ ∀ t ∈ ts, G.checksTerm t = true := by
  simp [checksAll]

end Glossary

end Wikidata
