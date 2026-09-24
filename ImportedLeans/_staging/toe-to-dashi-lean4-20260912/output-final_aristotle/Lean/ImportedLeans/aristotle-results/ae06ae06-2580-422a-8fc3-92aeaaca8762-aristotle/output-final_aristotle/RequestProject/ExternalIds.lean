import RequestProject.Matching
import RequestProject.Engine

/-!
# External identifiers and authority control

A large part of Wikidata consists of **external identifiers**: properties of
datatype *external-id* such as `VIAF ID` (P214) or `GND ID` (P227), each linking
an item to its record in some outside database, and each carrying a
`formatter URL` (P1630) that turns the identifier into a web address.

Two constraints govern them, and they are the same two conditions that govern
sitelinks: single-value (Q19474404) — an item has at most one identifier per
property — and distinct-values (Q21502410) — an identifier belongs to at most one
item.  So the general theory of `RequestProject.Matching` applies, and gives:

* an identifier property satisfying both constraints is a **partial bijection**
  between items and identifier strings, so the identifier *identifies* the item;
* two items carrying the same identifier are therefore duplicates — the
  computation `Wikidata.IdKB.duplicatesOn` lists them, and finding one is exactly
  a failure of the distinct-values constraint, i.e. a merge waiting to happen;
* the `formatter URL` resolves an identifier to an address, and does so
  injectively, so the resolved URL identifies the item just as the identifier
  does;
* **authority control**: two databases sharing an identifier property are matched
  through it, and the matching is a partial bijection — symmetric, injective and
  transitive along a third database.  This is how an item of Wikidata is linked
  to the corresponding record elsewhere without either side knowing the other's
  identifiers.
-/

namespace Wikidata

/-- A knowledge base of external identifiers: a set of items, a table of
⟨item, identifier property, identifier⟩ triples, and the `formatter URL` (P1630)
of each identifier property, given as a prefix and a suffix. -/
structure IdKB where
  /-- A human readable name. -/
  name : String := "authority file"
  /-- The items. -/
  items : List Qid := []
  /-- The identifier statements. -/
  ids : KeyTable Qid Qid String := {}
  /-- The formatter URLs, as ⟨property, prefix, suffix⟩. -/
  formatters : List (Qid × String × String) := []
deriving DecidableEq, Repr, Inhabited

namespace IdKB

variable (T : IdKB)

/-- The identifier of an item for a property, if any. -/
def idOf (q p : Qid) : Option String := T.ids.value? q p

/-- The item carrying an identifier for a property, if any. -/
def itemById (p : Qid) (v : String) : Option Qid := T.ids.subject? p v

/-- The single-value constraint (Q19474404): an item has at most one identifier
per property. -/
def SingleValue : Prop := T.ids.Functional

/-- The distinct-values constraint (Q21502410): an identifier belongs to at most
one item. -/
def DistinctValues : Prop := T.ids.Injective

/-- The executable single-value check. -/
def singleValueB : Bool := T.ids.functionalB

/-- The executable distinct-values check. -/
def distinctValuesB : Bool := T.ids.injectiveB

theorem singleValueB_iff : T.singleValueB = true ↔ T.SingleValue := KeyTable.functionalB_iff

theorem distinctValuesB_iff : T.distinctValuesB = true ↔ T.DistinctValues :=
  KeyTable.injectiveB_iff

variable {T}

theorem idOf_eq_some_iff (hs : T.SingleValue) {q p : Qid} {v : String} :
    T.idOf q p = some v ↔ (q, p, v) ∈ T.ids.rows := KeyTable.value?_eq_some_iff hs

theorem itemById_eq_some_iff (hd : T.DistinctValues) {q p : Qid} {v : String} :
    T.itemById p v = some q ↔ (q, p, v) ∈ T.ids.rows := KeyTable.subject?_eq_some_iff hd

/-- **An external identifier property is a partial bijection** between items and
identifiers: looking up the identifier of an item and looking up the item of an
identifier are mutually inverse. -/
theorem idOf_eq_some_iff_itemById_eq_some (hs : T.SingleValue) (hd : T.DistinctValues)
    {q p : Qid} {v : String} : T.idOf q p = some v ↔ T.itemById p v = some q :=
  KeyTable.value?_eq_some_iff_subject?_eq_some hs hd

/-- **The identifier identifies the item.** -/
theorem eq_of_idOf_eq (hs : T.SingleValue) (hd : T.DistinctValues) {q q' p : Qid} {v : String}
    (h : T.idOf q p = some v) (h' : T.idOf q' p = some v) : q = q' :=
  KeyTable.eq_of_value?_eq hs hd h h'

/-- An item has at most one identifier per property. -/
theorem idOf_unique (hs : T.SingleValue) {q p : Qid} {v v' : String}
    (h : T.idOf q p = some v) (h' : T.idOf q p = some v') : v = v' := by
  rw [idOf_eq_some_iff hs] at h h'
  exact hs _ _ _ _ h h'

/-! ### Formatter URLs -/

variable (T)

/-- The `formatter URL` (P1630) of an identifier property applied to an
identifier. -/
def formatUrl (p : Qid) (v : String) : Option String :=
  (T.formatters.find? (fun f => f.1 == p)).map (fun f => f.2.1 ++ v ++ f.2.2)

/-- The web address of an item's identifier. -/
def resolve (q p : Qid) : Option String := (T.idOf q p).bind (T.formatUrl p)

variable {T}

/-- **Resolving is injective**: two identifiers of the same property with the same
URL are the same identifier. -/
theorem formatUrl_inj {p : Qid} {v v' u : String} (h : T.formatUrl p v = some u)
    (h' : T.formatUrl p v' = some u) : v = v' := by
  simp only [formatUrl, Option.map_eq_some_iff] at h h'
  obtain ⟨f, hf, hu⟩ := h
  obtain ⟨f', hf', hu'⟩ := h'
  rw [hf] at hf'
  cases hf'
  have hstr : f.2.1 ++ v ++ f.2.2 = f.2.1 ++ v' ++ f.2.2 := by rw [hu, hu']
  have h1 := congrArg String.toList hstr
  rw [String.toList_append, String.toList_append, String.toList_append,
    String.toList_append] at h1
  exact String.ext (List.append_cancel_left (List.append_cancel_right h1))

/-- Hence the resolved URL identifies the item just as the identifier does. -/
theorem eq_of_resolve_eq (hs : T.SingleValue) (hd : T.DistinctValues) {q q' p : Qid}
    {u : String} (h : T.resolve q p = some u) (h' : T.resolve q' p = some u) : q = q' := by
  simp only [resolve, Option.bind_eq_some_iff] at h h'
  obtain ⟨v, hv, hu⟩ := h
  obtain ⟨v', hv', hu'⟩ := h'
  have : v = v' := formatUrl_inj hu hu'
  subst this
  exact eq_of_idOf_eq hs hd hv hv'

/-! ### Duplicate detection -/

variable (T)

/-- The pairs of *distinct* items carrying the same identifier for a property:
each such pair is a violation of the distinct-values constraint, and a candidate
for a merge. -/
def duplicatesOn (p : Qid) : List (Qid × Qid) :=
  T.ids.rows.flatMap (fun r =>
    T.ids.rows.filterMap (fun r' =>
      if r.2.1 = p ∧ r'.2.1 = p ∧ r.2.2 = r'.2.2 ∧ r.1 ≠ r'.1 then some (r.1, r'.1) else none))

variable {T}

theorem mem_duplicatesOn {p a b : Qid} (h : (a, b) ∈ T.duplicatesOn p) :
    a ≠ b ∧ ∃ v, (a, p, v) ∈ T.ids.rows ∧ (b, p, v) ∈ T.ids.rows := by
  simp only [duplicatesOn, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨r, hr, r', hr', hcond⟩ := h
  by_cases hc : r.2.1 = p ∧ r'.2.1 = p ∧ r.2.2 = r'.2.2 ∧ r.1 ≠ r'.1
  · rw [if_pos hc] at hcond
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases hcond
    refine ⟨h4, r.2.2, ?_, ?_⟩
    · obtain ⟨x, y, z⟩ := r; simp_all
    · obtain ⟨x, y, z⟩ := r'; simp_all
  · rw [if_neg hc] at hcond
    exact absurd hcond (by simp)

/-- **A duplicate is a constraint violation**: if two distinct items share an
identifier, the distinct-values constraint fails — the two items are the same
thing recorded twice, and should be merged. -/
theorem not_distinctValues_of_duplicate {p a b : Qid} (h : (a, b) ∈ T.duplicatesOn p) :
    ¬ T.DistinctValues := by
  obtain ⟨hne, v, ha, hb⟩ := mem_duplicatesOn h
  exact fun hd => hne (hd _ _ _ _ ha hb)

/-! ### Authority control: matching two databases -/

variable (A B : IdKB)

/-- The item of `B` that carries the same identifier as the given item of `A`. -/
def matchOn (p : Qid) (q : Qid) : Option Qid := A.ids.matchWith B.ids p q

variable {A B}

theorem matchOn_eq_some_iff (hs : A.SingleValue) (hd : B.DistinctValues) {p q b : Qid} :
    A.matchOn B p q = some b ↔
      ∃ v, (q, p, v) ∈ A.ids.rows ∧ (b, p, v) ∈ B.ids.rows :=
  KeyTable.matchWith_eq_some_iff hs hd

/-- **The match is symmetric**: the two databases agree on which records
correspond. -/
theorem matchOn_symm (hsA : A.SingleValue) (hdA : A.DistinctValues) (hsB : B.SingleValue)
    (hdB : B.DistinctValues) {p q b : Qid} (h : A.matchOn B p q = some b) :
    B.matchOn A p b = some q :=
  KeyTable.matchWith_symm hsA hdA hsB hdB h

/-- **The match is injective**: two items matched to the same record are the same
item. -/
theorem matchOn_inj (hsA : A.SingleValue) (hdA : A.DistinctValues) (hsB : B.SingleValue)
    (hdB : B.DistinctValues) {p q q' b : Qid} (h : A.matchOn B p q = some b)
    (h' : A.matchOn B p q' = some b) : q = q' :=
  KeyTable.matchWith_inj hsA hdA hsB hdB h h'

/-- **The match is transitive**: chains of authority-control links compose. -/
theorem matchOn_trans {C : IdKB} (hsA : A.SingleValue) (hsB : B.SingleValue)
    (hdB : B.DistinctValues) (hdC : C.DistinctValues) {p q b c : Qid}
    (h : A.matchOn B p q = some b) (h' : B.matchOn C p b = some c) :
    A.matchOn C p q = some c :=
  KeyTable.matchWith_trans hsA hsB hdB hdC h h'

end IdKB

/-! ## A worked fragment -/

namespace ExternalIdExample

open Wikidata

/-- Douglas Adams (Q42). -/
def adams : Qid := .wd "Q42"
/-- *The Hitchhiker's Guide to the Galaxy* (Q25169). -/
def hitchhiker : Qid := .wd "Q25169"
/-- A duplicate item for Douglas Adams. -/
def adamsDup : Qid := .wd "Q999999"
/-- `VIAF ID` (P214). -/
def viaf : Qid := .wd "P214"
/-- `GND ID` (P227). -/
def gnd : Qid := .wd "P227"

/-- A fragment of Wikidata with two external identifiers per item. -/
def wd : IdKB where
  name := "wikidata fragment"
  items := [adams, hitchhiker]
  ids := ⟨[(adams, viaf, "113230702"), (adams, gnd, "119033364"),
    (hitchhiker, viaf, "180945770")]⟩
  formatters := [(viaf, "https://viaf.org/viaf/", ""), (gnd, "https://d-nb.info/gnd/", "")]

/-- The German national library's catalogue, with its own item identifiers and
the same `GND ID` values. -/
def dnb : IdKB where
  name := "dnb catalogue"
  items := [.wd "DNB-1", .wd "DNB-2"]
  ids := ⟨[(.wd "DNB-1", gnd, "119033364"), (.wd "DNB-2", gnd, "118500775")]⟩
  formatters := [(gnd, "https://d-nb.info/gnd/", "")]

theorem wd_singleValue : wd.SingleValue := (IdKB.singleValueB_iff wd).1 (by decide)

theorem wd_distinctValues : wd.DistinctValues := (IdKB.distinctValuesB_iff wd).1 (by decide)

theorem dnb_singleValue : dnb.SingleValue := (IdKB.singleValueB_iff dnb).1 (by decide)

theorem dnb_distinctValues : dnb.DistinctValues := (IdKB.distinctValuesB_iff dnb).1 (by decide)

theorem adams_viaf : wd.idOf adams viaf = some "113230702" := by decide

/-- The identifier identifies the item. -/
theorem viaf_lookup : wd.itemById viaf "113230702" = some adams := by decide

theorem adams_url : wd.resolve adams gnd = some "https://d-nb.info/gnd/119033364" := by decide

/-- **Authority control**: the Wikidata item is matched to the catalogue record
carrying the same `GND ID`, ... -/
theorem adams_match : wd.matchOn dnb gnd adams = some (.wd "DNB-1") := by decide

/-- ... and the catalogue matches it back. -/
theorem adams_match_back : dnb.matchOn wd gnd (.wd "DNB-1") = some adams :=
  IdKB.matchOn_symm wd_singleValue wd_distinctValues dnb_singleValue dnb_distinctValues
    adams_match

/-- An item with no identifier of the property is matched to nothing. -/
theorem hitchhiker_no_match : wd.matchOn dnb gnd hitchhiker = none := by decide

/-- A base in which a duplicate item carries the same `VIAF ID`. -/
def wdDup : IdKB where
  name := "wikidata fragment with a duplicate"
  items := [adams, adamsDup]
  ids := ⟨[(adams, viaf, "113230702"), (adamsDup, viaf, "113230702")]⟩

/-- The duplicate is found, ... -/
theorem wdDup_duplicate : (adams, adamsDup) ∈ wdDup.duplicatesOn viaf := by decide

/-- ... and it is exactly a failure of the distinct-values constraint. -/
theorem wdDup_not_distinctValues : ¬ wdDup.DistinctValues :=
  IdKB.not_distinctValues_of_duplicate wdDup_duplicate

/-- The good fragment has no duplicates. -/
theorem wd_no_duplicates : wd.duplicatesOn viaf = [] := by decide

end ExternalIdExample

end Wikidata
