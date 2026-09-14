import RequestProject.Engine
import RequestProject.Matching

/-!
# Sitelinks

Besides statements, terms and references, a Wikidata item carries **sitelinks**:
the pages of the Wikimedia projects that the item is *about*.  The data model
imposes two conditions, and they are the whole content of the sitelink layer:

* an item has **at most one page per site**, and
* a page of a site is linked from **at most one item**.

Together they make the sitelink table a *partial bijection*, per site, between
items and pages.  That is the main theorem of this file
(`Wikidata.SiteKB.pageOf_eq_some_iff_itemOf_eq_some`): the two lookups
`pageOf` (item ↦ page) and `itemOf` (page ↦ item) are mutually inverse.

The two conditions are given both as executable checks and as abstract
properties, and the checks are proved to decide exactly those properties.  We
then look at what merging two items does to the sitelinks: a merge is legitimate
exactly when the two items' sitelinks do not clash on a common site, which is
the reason Wikidata refuses to merge two items linked to different pages of the
same wiki.
-/

namespace Wikidata

/-- A link from an item to a page of a Wikimedia site. -/
structure Sitelink where
  /-- The site, e.g. `"enwiki"`. -/
  site : String
  /-- The page title on that site. -/
  page : String
deriving DecidableEq, Repr, Inhabited

/-- A knowledge base of sitelinks: items together with their links. -/
structure SiteKB where
  /-- The items. -/
  items : List Qid
  /-- The sitelinks, as pairs of an item and a link. -/
  links : List (Qid × Sitelink) := []
deriving DecidableEq, Repr, Inhabited

namespace SiteKB

variable (S : SiteKB)

/-- The sitelinks read as a table of triples ⟨item, site, page⟩, so that the
general partial-bijection theory of `RequestProject.Matching` applies. -/
def table : KeyTable Qid String String := ⟨S.links.map (fun l => (l.1, l.2.site, l.2.page))⟩

/-- The page of `site` that the item `q` is linked to, if any. -/
def pageOf (q : Qid) (site : String) : Option String := S.table.value? q site

/-- The item linked to the page `page` of `site`, if any. -/
def itemOf (site page : String) : Option Qid := S.table.subject? site page

/-- Every item has at most one page per site. -/
def Functional : Prop :=
  ∀ q site p p', (q, ⟨site, p⟩) ∈ S.links → (q, ⟨site, p'⟩) ∈ S.links → p = p'

/-- Every page is linked from at most one item. -/
def PageInjective : Prop :=
  ∀ site page q q', (q, ⟨site, page⟩) ∈ S.links → (q', ⟨site, page⟩) ∈ S.links → q = q'

/-- The executable check for `Functional`. -/
def functionalB : Bool := S.table.functionalB

/-- The executable check for `PageInjective`. -/
def pageInjectiveB : Bool := S.table.injectiveB

/-- All linked items are declared items. -/
def wellFormedB : Bool := S.links.all (fun l => l.1 ∈ S.items)

variable {S}

@[simp] theorem mem_table_rows {q : Qid} {site p : String} :
    (q, site, p) ∈ S.table.rows ↔ (q, (⟨site, p⟩ : Sitelink)) ∈ S.links := by
  simp only [table, List.mem_map, Prod.ext_iff]
  constructor
  · rintro ⟨l, hl, h1, h2, h3⟩
    obtain ⟨a, b⟩ := l
    obtain ⟨s, pg⟩ := b
    simp_all
  · intro h
    exact ⟨(q, ⟨site, p⟩), h, rfl, rfl, rfl⟩

theorem functional_iff_table : S.Functional ↔ S.table.Functional := by
  constructor
  · intro h q site p p' h1 h2
    exact h q site p p' (mem_table_rows.1 h1) (mem_table_rows.1 h2)
  · intro h q site p p' h1 h2
    exact h q site p p' (mem_table_rows.2 h1) (mem_table_rows.2 h2)

theorem pageInjective_iff_table : S.PageInjective ↔ S.table.Injective := by
  constructor
  · intro h site page q q' h1 h2
    exact h site page q q' (mem_table_rows.1 h1) (mem_table_rows.1 h2)
  · intro h site page q q' h1 h2
    exact h site page q q' (mem_table_rows.2 h1) (mem_table_rows.2 h2)

theorem functionalB_iff : S.functionalB = true ↔ S.Functional := by
  rw [functionalB, KeyTable.functionalB_iff, functional_iff_table]

theorem pageInjectiveB_iff : S.pageInjectiveB = true ↔ S.PageInjective := by
  rw [pageInjectiveB, KeyTable.injectiveB_iff, pageInjective_iff_table]

/-! ### The lookups -/

theorem pageOf_eq_some_iff (hf : S.Functional) {q : Qid} {site p : String} :
    S.pageOf q site = some p ↔ (q, ⟨site, p⟩) ∈ S.links := by
  rw [pageOf, KeyTable.value?_eq_some_iff (functional_iff_table.1 hf), mem_table_rows]

theorem itemOf_eq_some_iff (hi : S.PageInjective) {q : Qid} {site p : String} :
    S.itemOf site p = some q ↔ (q, ⟨site, p⟩) ∈ S.links := by
  rw [itemOf, KeyTable.subject?_eq_some_iff (pageInjective_iff_table.1 hi), mem_table_rows]

/-- **The sitelink table is a partial bijection**: when every item has at most one
page per site and every page is linked from at most one item, the lookup from
items to pages and the lookup from pages to items are mutually inverse. -/
theorem pageOf_eq_some_iff_itemOf_eq_some (hf : S.Functional) (hi : S.PageInjective)
    {q : Qid} {site p : String} : S.pageOf q site = some p ↔ S.itemOf site p = some q := by
  rw [pageOf_eq_some_iff hf, itemOf_eq_some_iff hi]

/-- Round trip, item ↦ page ↦ item. -/
theorem itemOf_pageOf (hf : S.Functional) (hi : S.PageInjective) {q : Qid} {site p : String}
    (h : S.pageOf q site = some p) : S.itemOf site p = some q :=
  (pageOf_eq_some_iff_itemOf_eq_some hf hi).1 h

/-- Round trip, page ↦ item ↦ page. -/
theorem pageOf_itemOf (hf : S.Functional) (hi : S.PageInjective) {q : Qid} {site p : String}
    (h : S.itemOf site p = some q) : S.pageOf q site = some p :=
  (pageOf_eq_some_iff_itemOf_eq_some hf hi).2 h

/-- Two items linked to the same page of a site are the same item — the sitelink
of a site identifies the item. -/
theorem eq_of_pageOf_eq (hf : S.Functional) (hi : S.PageInjective) {q q' : Qid}
    {site p : String} (h : S.pageOf q site = some p) (h' : S.pageOf q' site = some p) :
    q = q' := by
  rw [pageOf_eq_some_iff hf] at h h'
  exact hi _ _ _ _ h h'

/-! ### Merging items -/

/-- Renaming the items of a sitelink table along `f`; merging two items is the
special case where `f` identifies them. -/
def rename (f : Qid → Qid) : SiteKB where
  items := S.items.map f
  links := S.links.map (fun l => (f l.1, l.2))

variable (S)

theorem mem_rename_links {f : Qid → Qid} {q : Qid} {sl : Sitelink} :
    (q, sl) ∈ (S.rename f).links ↔ ∃ x, (x, sl) ∈ S.links ∧ f x = q := by
  simp only [rename, List.mem_map, Prod.ext_iff]
  constructor
  · rintro ⟨l, hl, h1, h2⟩
    exact ⟨l.1, by cases l; simp_all, h1⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x, sl), hx, rfl, rfl⟩

variable {S}

/-- **When a merge is legitimate**: renaming items preserves the "one page per
site" condition exactly when items that get identified do not link to different
pages of the same site. -/
theorem functional_rename {f : Qid → Qid}
    (h : ∀ x y site p p', f x = f y → (x, ⟨site, p⟩) ∈ S.links → (y, ⟨site, p'⟩) ∈ S.links →
      p = p') : (S.rename f).Functional := by
  intro q site p p' hp hp'
  obtain ⟨x, hx, hfx⟩ := (mem_rename_links S).1 hp
  obtain ⟨y, hy, hfy⟩ := (mem_rename_links S).1 hp'
  exact h x y site p p' (hfx.trans hfy.symm) hx hy

/-- Conversely, a merge that clashes on a site is rejected: if two items linked to
different pages of the same site are identified, the result is no longer
functional. -/
theorem not_functional_rename_of_clash {f : Qid → Qid} {x y : Qid} {site p p' : String}
    (hxy : f x = f y) (hp : (x, ⟨site, p⟩) ∈ S.links) (hp' : (y, ⟨site, p'⟩) ∈ S.links)
    (hne : p ≠ p') : ¬ (S.rename f).Functional := by
  intro hF
  exact hne (hF (f x) site p p' ((mem_rename_links S).2 ⟨x, hp, rfl⟩)
    ((mem_rename_links S).2 ⟨y, hp', hxy.symm⟩))

/-- Renaming preserves injectivity of pages only if the renaming is injective on
the items owning them; here is the useful direction. -/
theorem pageInjective_rename {f : Qid → Qid} (hi : S.PageInjective) :
    (S.rename f).PageInjective := by
  intro site page q q' hq hq'
  obtain ⟨x, hx, rfl⟩ := (mem_rename_links S).1 hq
  obtain ⟨y, hy, rfl⟩ := (mem_rename_links S).1 hq'
  rw [hi _ _ _ _ hx hy]

end SiteKB

/-! ## A worked fragment -/

namespace SitelinkExample

open Wikidata

/-- Douglas Adams (Q42). -/
def adams : Qid := .wd "Q42"
/-- *The Hitchhiker's Guide to the Galaxy* (Q25169). -/
def hitchhiker : Qid := .wd "Q25169"
/-- A duplicate item for Douglas Adams, to be merged away. -/
def adamsDup : Qid := .wd "Q999999"

/-- A small sitelink table. -/
def frag : SiteKB where
  items := [adams, hitchhiker, adamsDup]
  links :=
    [(adams, ⟨"enwiki", "Douglas Adams"⟩),
     (adams, ⟨"dewiki", "Douglas Adams"⟩),
     (hitchhiker, ⟨"enwiki", "The Hitchhiker's Guide to the Galaxy"⟩),
     (adamsDup, ⟨"frwiki", "Douglas Adams"⟩)]

theorem frag_wellFormed : frag.wellFormedB = true := by decide

theorem frag_functional : frag.Functional := SiteKB.functionalB_iff.1 (by decide)

theorem frag_pageInjective : frag.PageInjective := SiteKB.pageInjectiveB_iff.1 (by decide)

/-- The same page title on two different sites belongs to two different items —
titles are only unique per site. -/
theorem frag_lookup_dewiki : frag.itemOf "dewiki" "Douglas Adams" = some adams := by decide

theorem frag_lookup_frwiki : frag.itemOf "frwiki" "Douglas Adams" = some adamsDup := by decide

theorem frag_page_adams : frag.pageOf adams "enwiki" = some "Douglas Adams" := by decide

/-- The round trip through the two lookups. -/
theorem frag_round_trip : frag.itemOf "enwiki" "Douglas Adams" = some adams :=
  SiteKB.itemOf_pageOf frag_functional frag_pageInjective frag_page_adams

/-- Merging the duplicate into Douglas Adams: the two items link to pages of
different sites, so the merge is legitimate. -/
def mergeDup : Qid → Qid := fun q => if q = adamsDup then adams else q

theorem merge_ok : (frag.rename mergeDup).Functional := by
  refine SiteKB.functional_rename ?_
  intro x y site p p' hf hx hy
  simp only [frag, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;>
    simp_all [mergeDup, adams, adamsDup, hitchhiker]

/-- Merging Douglas Adams with the *Hitchhiker's Guide*, by contrast, is rejected:
both are linked to a page of the English Wikipedia, and to different pages. -/
def mergeBad : Qid → Qid := fun q => if q = hitchhiker then adams else q

theorem merge_bad : ¬ (frag.rename mergeBad).Functional :=
  SiteKB.not_functional_rename_of_clash (x := adams) (y := hitchhiker)
    (site := "enwiki") (p := "Douglas Adams")
    (p' := "The Hitchhiker's Guide to the Galaxy")
    (by decide) (by decide) (by decide) (by decide)

/-- A table linking two items to the same page fails the check. -/
def fragBad : SiteKB where
  items := [adams, adamsDup]
  links := [(adams, ⟨"enwiki", "Douglas Adams"⟩), (adamsDup, ⟨"enwiki", "Douglas Adams"⟩)]

theorem fragBad_not_pageInjective : ¬ fragBad.PageInjective := by
  intro h
  have : adams = adamsDup := h "enwiki" "Douglas Adams" adams adamsDup (by decide) (by decide)
  exact absurd this (by decide)

/-- A table linking one item to two pages of the same site fails the other
check. -/
def fragBad2 : SiteKB where
  items := [adams]
  links := [(adams, ⟨"enwiki", "Douglas Adams"⟩), (adams, ⟨"enwiki", "Douglas Noel Adams"⟩)]

theorem fragBad2_not_functional : ¬ fragBad2.Functional := by
  intro h
  have : "Douglas Adams" = "Douglas Noel Adams" :=
    h adams "enwiki" _ _ (by decide) (by decide)
  exact absurd this (by decide)

end SitelinkExample

end Wikidata
