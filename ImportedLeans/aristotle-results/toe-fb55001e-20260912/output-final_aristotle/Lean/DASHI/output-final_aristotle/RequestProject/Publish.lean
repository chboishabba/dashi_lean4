import RequestProject.Cli.Format

/-!
# Publishing a knowledge base: JSON Lines, content addresses

This file is the *publication layer*: what the project puts on a web site, in a
dataset repository, on a peer-to-peer network or in a long term archive.

Two things are needed for that, and both are proved here.

* **A public interchange format.** `Publish.jsonlOfKB` writes a knowledge base as
  [JSON Lines](https://jsonlines.org) — one JSON array of strings per record, the
  same records the `.wdkb` format uses (`Wikidata.Cli.kbRecs`). This is what a
  Hugging Face dataset, a static site or an `archive.org` item can carry.
  `Publish.parseJsonl?` reads it back, and `Publish.parseJsonl?_jsonlOfKB` says a
  round trip through the published file returns *exactly* the knowledge base that
  was published: nothing is invented, nothing is dropped.

* **A content address.** `Publish.cid` is a deterministic identifier computed from
  the canonical text of a base (a 64-bit FNV-1a digest of `Cli.renderKB`). Peers
  and mirrors quote it to say *which* ontology they have.
  `Publish.eq_of_renderKB_eq` says the canonical text identifies the base:
  two clean knowledge bases with the same canonical text are equal. So agreeing on
  the bytes is agreeing on the ontology.

The row count is pinned down too (`Publish.length_kbRecs`): the published file has
exactly one header row plus one row per item, level, `subclass of`, `instance of`
and disjointness statement.
-/

namespace Wikidata
namespace Publish

open Wikidata.Cli

/-! ### JSON-safe fields -/

/-- The separator between the entries of a JSON array. -/
def comma : Char := ','

/-- The quotation mark delimiting a JSON string. -/
def quoteCh : Char := '"'

/-- The JSON escape character. -/
def backslash : Char := '\\'

/-- A field is *JSON safe* when it needs no escaping and no un-escaping: it
contains no tab, newline, quotation mark, backslash or comma.  Wikidata
identifiers, metaclass levels and the record tags are all of this shape. -/
def jsonSafeB (x : String) : Bool :=
  cleanFieldB x && !x.toList.contains quoteCh && !x.toList.contains backslash &&
    !x.toList.contains comma

theorem cleanFieldB_of_jsonSafeB {x : String} (h : jsonSafeB x = true) :
    cleanFieldB x = true := by
  simp only [jsonSafeB, Bool.and_eq_true] at h
  exact h.1.1.1

theorem quote_notMem_of_jsonSafeB {x : String} (h : jsonSafeB x = true) :
    quoteCh ∉ x.toList := by
  simp only [jsonSafeB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.eq_false_iff, ne_eq] at h
  simpa using h.1.1.2

theorem comma_notMem_of_jsonSafeB {x : String} (h : jsonSafeB x = true) :
    comma ∉ x.toList := by
  simp only [jsonSafeB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.eq_false_iff, ne_eq] at h
  simpa using h.2

/-! ### JSON strings -/

/-- A field as a JSON string. -/
def quote (x : String) : String := String.ofList (quoteCh :: (x.toList ++ [quoteCh]))

/-- Reads a JSON string. -/
def unquote? (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
      if c = quoteCh then
        match rest.reverse with
        | d :: mid => if d = quoteCh then some (String.ofList mid.reverse) else none
        | [] => none
      else none
  | [] => none

/-- **JSON strings round-trip.** -/
theorem unquote?_quote (x : String) : unquote? (quote x) = some x := by
  have hx : (quote x).toList = quoteCh :: (x.toList ++ [quoteCh]) := by
    simp [quote]
  simp [unquote?, hx]

theorem quote_toList (x : String) : (quote x).toList = quoteCh :: (x.toList ++ [quoteCh]) := by
  simp [quote]

theorem notMem_quote {c : Char} {x : String} (hq : c ≠ quoteCh) (hx : c ∉ x.toList) :
    c ∉ (quote x).toList := by
  simp [quote_toList, hq, hx]

/-! ### JSON arrays of strings -/

/-- A record as a JSON array of strings. -/
def jsonArray (fs : List String) : String :=
  String.ofList ('[' :: ((joinChar comma (fs.map quote)).toList ++ [']']))

/-- Reads a JSON array of strings. -/
def parseJsonArray? (s : String) : Option (List String) :=
  match s.toList with
  | c :: rest =>
      if c = '[' then
        match rest.reverse with
        | d :: mid =>
            if d = ']' then (splitChar comma (String.ofList mid.reverse)).mapM unquote?
            else none
        | [] => none
      else none
  | [] => none

theorem mapM_unquote?_map_quote (fs : List String) :
    (fs.map quote).mapM unquote? = some fs := by
  induction fs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, unquote?_quote, ih]

theorem mapM_unquote?_comp (fs : List String) : fs.mapM (unquote? ∘ quote) = some fs := by
  induction fs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, Function.comp_apply, unquote?_quote, ih]

/-- **JSON arrays round-trip** for JSON-safe fields. -/
theorem parseJsonArray?_jsonArray (fs : List String) (hne : fs ≠ [])
    (h : ∀ x ∈ fs, jsonSafeB x = true) : parseJsonArray? (jsonArray fs) = some fs := by
  have hcomma : ∀ y ∈ fs.map quote, comma ∉ y.toList := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact notMem_quote (by decide) (comma_notMem_of_jsonSafeB (h x hx))
  have hsplit : splitChar comma (joinChar comma (fs.map quote)) = fs.map quote :=
    splitChar_joinChar comma _ hcomma (by simpa using hne)
  have harr : (jsonArray fs).toList =
      '[' :: ((joinChar comma (fs.map quote)).toList ++ [']']) := by
    simp [jsonArray]
  simp [parseJsonArray?, harr, hsplit, mapM_unquote?_comp]

/-! ### A knowledge base as JSON Lines -/

/-- One published row: the fields of a record, as a JSON array. -/
def jsonRow (r : Rec) : String := jsonArray (renderRec r)

/-- A knowledge base as JSON Lines. -/
def jsonlOfKB (kb : KB) : String := joinChar nl ((kbRecs kb).map jsonRow)

/-- Reads a knowledge base from JSON Lines. -/
def parseJsonl? (s : String) : Option KB :=
  ((splitChar nl s).mapM (fun l => (parseJsonArray? l).bind parseRec?)).map kbOfRecs

/-- Every field of every published row is JSON safe.  The tool checks this before
publishing. -/
def jsonSafeKB (kb : KB) : Bool := (kbRecs kb).all (fun r => (renderRec r).all jsonSafeB)

theorem jsonSafe_fields {kb : KB} (h : jsonSafeKB kb = true) :
    ∀ r ∈ kbRecs kb, ∀ x ∈ renderRec r, jsonSafeB x = true := by
  simp only [jsonSafeKB, List.all_eq_true] at h
  intro r hr x hx
  exact h r hr x hx

theorem nl_notMem_jsonRow {r : Rec} (h : ∀ x ∈ renderRec r, jsonSafeB x = true) :
    nl ∉ (jsonRow r).toList := by
  have hj : nl ∉ (joinChar comma ((renderRec r).map quote)).toList := by
    simp only [joinChar, String.toList_ofList]
    refine mem_intercalate_singleton (by decide) ?_
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hl
    exact notMem_quote (by decide) (notMem_of_cleanFieldB (cleanFieldB_of_jsonSafeB (h x hx))).2
  have harr : (jsonRow r).toList =
      '[' :: ((joinChar comma ((renderRec r).map quote)).toList ++ [']']) := by
    simp [jsonRow, jsonArray]
  simp only [harr, List.mem_cons, List.mem_append, not_or]
  exact ⟨by decide, hj, by decide⟩

theorem mapM_rows : ∀ (rs : List Rec),
    (∀ r ∈ rs, (parseJsonArray? (jsonRow r)).bind parseRec? = some r) →
      (rs.map jsonRow).mapM (fun l => (parseJsonArray? l).bind parseRec?) = some rs
  | [], _ => rfl
  | r :: rs, h => by
      have h1 := h r List.mem_cons_self
      have h2 := mapM_rows rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      simp [List.mapM_cons, h1, h2]

/-- **The published file is lossless**: reading back the JSON Lines the project
publishes returns exactly the knowledge base that was published. -/
theorem parseJsonl?_jsonlOfKB (kb : KB) (h : jsonSafeKB kb = true) :
    parseJsonl? (jsonlOfKB kb) = some kb := by
  have hne : (kbRecs kb).map jsonRow ≠ [] := by simp [kbRecs]
  have hlines : splitChar nl (joinChar nl ((kbRecs kb).map jsonRow)) = (kbRecs kb).map jsonRow := by
    refine splitChar_joinChar nl _ ?_ hne
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact nl_notMem_jsonRow (jsonSafe_fields h r hr)
  have hrow : ∀ r ∈ kbRecs kb, (parseJsonArray? (jsonRow r)).bind parseRec? = some r := by
    intro r hr
    rw [jsonRow, parseJsonArray?_jsonArray _ (renderRec_ne_nil r) (jsonSafe_fields h r hr)]
    simpa using parseRec?_renderRec r
  simp [parseJsonl?, jsonlOfKB, hlines, mapM_rows _ hrow, kbOfRecs_kbRecs]

/-- **The published file carries every row and no others**: one header row, then
one row per item, per declared level and per statement. -/
theorem length_kbRecs (kb : KB) :
    (kbRecs kb).length =
      1 + kb.items.length + kb.levels.length + kb.sub.length + kb.inst.length +
        kb.disj.length := by
  simp [kbRecs]
  omega

theorem length_jsonRows (kb : KB) :
    ((kbRecs kb).map jsonRow).length =
      1 + kb.items.length + kb.levels.length + kb.sub.length + kb.inst.length +
        kb.disj.length := by
  rw [List.length_map, length_kbRecs]

/-! ### Content addresses -/

/-- The FNV-1a offset basis. -/
def fnvOffset : UInt64 := 14695981039346656037

/-- The FNV-1a prime. -/
def fnvPrime : UInt64 := 1099511628211

/-- A 64-bit FNV-1a digest of a string, over its code points. -/
def fnv1a (s : String) : UInt64 :=
  s.toList.foldl (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnvPrime) fnvOffset

/-- A lowercase hexadecimal digit. -/
def hexDigit (n : ℕ) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A 64-bit number in 16 hexadecimal digits. -/
def hex16 (x : UInt64) : String :=
  String.ofList ((List.range 16).map fun i => hexDigit ((x.toNat >>> (4 * (15 - i))) % 16))

/-- The **content address** of a knowledge base: a deterministic identifier
computed from its canonical text.  Peers, mirrors and archives quote it to say
which ontology they are talking about. -/
def cid (kb : KB) : String := "wdkb1-" ++ hex16 (fnv1a (renderKB kb))

/-- The canonical text of a knowledge base determines it: two clean bases written
the same way *are* the same base.  This is what makes `cid` a meaningful name for
a peer to quote. -/
theorem eq_of_renderKB_eq {kb kb' : KB} (h : KB.cleanB kb = true) (h' : KB.cleanB kb' = true)
    (hr : renderKB kb = renderKB kb') : kb = kb' := by
  have h1 := parseKB?_renderKB kb h
  have h2 := parseKB?_renderKB kb' h'
  rw [hr, h2] at h1
  exact (Option.some.inj h1).symm

/-- Equal bases have equal content addresses. -/
theorem cid_congr {kb kb' : KB} (h : kb = kb') : cid kb = cid kb' := by rw [h]

theorem cid_eq_of_renderKB_eq {kb kb' : KB} (hr : renderKB kb = renderKB kb') :
    cid kb = cid kb' := by rw [cid, cid, hr]

/-- Two clean bases whose canonical texts agree are equal, hence so is everything
computed from them; in particular a mirror that reproduces the canonical text
reproduces the ontology. -/
theorem eq_of_cid_and_render {kb kb' : KB} (h : KB.cleanB kb = true) (h' : KB.cleanB kb' = true)
    (hr : renderKB kb = renderKB kb') : cid kb = cid kb' ∧ kb = kb' :=
  ⟨cid_eq_of_renderKB_eq hr, eq_of_renderKB_eq h h' hr⟩

end Publish
end Wikidata
