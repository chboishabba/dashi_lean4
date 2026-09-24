import RequestProject.Cli.Format
import RequestProject.TaxaLineage

/-!
# A verified on-disk format for taxon layers

`RequestProject.Cli.Format` stores a knowledge base as tab-separated records.  This file
extends the format with the three record kinds of the taxon layer, so that a whole `TKB`
can be written to a file and read back:

```
name    life
item    wd      Q171283
inst    wd      Q171283 wd      Q16521
parent  wd      Q171283 wd      Q7380
rank    genus   wd      Q171283
tname   Homo    wd      Q171283
```

The base records are exactly the ones of the knowledge base format, and the three new
keywords are `parent` (P171), `rank` (P105) and `tname` (P225).  The point of the file is
`Wikidata.Cli.parseTKB?_renderTKB`: **reading back a taxon layer that was written returns
exactly the layer that was written**, provided its identifiers, names and scientific names
carry no tab or newline (`TKB.cleanB`).
-/

namespace Wikidata
namespace Cli

/-! ### Ranks as tokens -/

/-- Writes a `taxon rank` value. -/
def renderRank (r : TaxonRank) : String := r.label

/-- Reads a `taxon rank` value. -/
def parseRank? (s : String) : Option TaxonRank :=
  if s = "species" then some .species
  else if s = "genus" then some .genus
  else if s = "family" then some .family
  else if s = "order" then some .order
  else if s = "class" then some .class_
  else if s = "phylum" then some .phylum
  else if s = "kingdom" then some .kingdom
  else if s = "domain" then some .domain
  else none

theorem parseRank?_renderRank (r : TaxonRank) : parseRank? (renderRank r) = some r := by
  cases r <;> rfl

theorem cleanFieldB_renderRank (r : TaxonRank) : cleanFieldB (renderRank r) = true := by
  cases r <;> rfl

/-! ### Records -/

/-- A record of a taxon-layer file: a knowledge base record, or one of the three taxon
statements. -/
inductive TRec where
  /-- A record of the underlying knowledge base. -/
  | base (r : Rec)
  /-- A `parent taxon` (P171) statement. -/
  | parent (a b : Qid)
  /-- A `taxon rank` (P105) value. -/
  | rank (a : Qid) (r : TaxonRank)
  /-- A `taxon name` (P225) value. -/
  | tname (a : Qid) (n : String)
deriving Repr, DecidableEq, Inhabited

/-- Renders one taxon-layer record. -/
def renderTRec : TRec → Record
  | .base r => renderRec r
  | .parent a b => "parent" :: (qidTokens a ++ qidTokens b)
  | .rank a r => "rank" :: renderRank r :: qidTokens a
  | .tname a n => "tname" :: n :: qidTokens a

/-- Reads one taxon-layer record; anything that is not one of the three taxon keywords is
handed to the knowledge base reader. -/
def parseTRec? (r : Record) : Option TRec :=
  match r with
  | "parent" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (b, []) => some (.parent a b)
          | _ => none
      | _ => none
  | "rank" :: d :: ts =>
      match parseRank? d, parseQid? ts with
      | some rk, some (a, []) => some (.rank a rk)
      | _, _ => none
  | "tname" :: n :: ts =>
      match parseQid? ts with
      | some (a, []) => some (.tname a n)
      | _ => none
  | _ => (parseRec? r).map TRec.base

/-- The head keyword of a knowledge base record is never one of the taxon keywords, so base
records are read by the knowledge base reader. -/
theorem parseTRec?_renderRec (r : Rec) : parseTRec? (renderRec r) = some (.base r) := by
  cases r with
  | name s =>
      have h : parseRec? ["name", s] = some (Rec.name s) := parseRec?_renderRec (Rec.name s)
      show parseTRec? ["name", s] = _
      simp [parseTRec?, h]
  | item q =>
      have h : parseRec? ("item" :: qidTokens q) = some (Rec.item q) :=
        parseRec?_renderRec (Rec.item q)
      show parseTRec? ("item" :: qidTokens q) = _
      simp [parseTRec?, h]
  | level q n =>
      have h : parseRec? ("level" :: renderNat n :: qidTokens q) = some (Rec.level q n) :=
        parseRec?_renderRec (Rec.level q n)
      show parseTRec? ("level" :: renderNat n :: qidTokens q) = _
      simp [parseTRec?, h]
  | sub a b =>
      have h : parseRec? ("sub" :: (qidTokens a ++ qidTokens b)) = some (Rec.sub a b) :=
        parseRec?_renderRec (Rec.sub a b)
      show parseTRec? ("sub" :: (qidTokens a ++ qidTokens b)) = _
      simp [parseTRec?, h]
  | inst a c =>
      have h : parseRec? ("inst" :: (qidTokens a ++ qidTokens c)) = some (Rec.inst a c) :=
        parseRec?_renderRec (Rec.inst a c)
      show parseTRec? ("inst" :: (qidTokens a ++ qidTokens c)) = _
      simp [parseTRec?, h]
  | disj a b =>
      have h : parseRec? ("disj" :: (qidTokens a ++ qidTokens b)) = some (Rec.disj a b) :=
        parseRec?_renderRec (Rec.disj a b)
      show parseTRec? ("disj" :: (qidTokens a ++ qidTokens b)) = _
      simp [parseTRec?, h]

/-- **Records round-trip.** -/
theorem parseTRec?_renderTRec (r : TRec) : parseTRec? (renderTRec r) = some r := by
  cases r with
  | base r => exact parseTRec?_renderRec r
  | parent a b =>
      show parseTRec? ("parent" :: (qidTokens a ++ qidTokens b)) = _
      rw [show qidTokens b = qidTokens b ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseTRec?, parseQid?_qidTokens]
  | rank a rk =>
      show parseTRec? ("rank" :: renderRank rk :: qidTokens a) = _
      rw [show qidTokens a = qidTokens a ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseTRec?, parseQid?_qidTokens, parseRank?_renderRank]
  | tname a n =>
      show parseTRec? ("tname" :: n :: qidTokens a) = _
      rw [show qidTokens a = qidTokens a ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseTRec?, parseQid?_qidTokens]

theorem renderTRec_ne_nil (r : TRec) : renderTRec r ≠ [] := by
  cases r with
  | base r => simpa [renderTRec] using renderRec_ne_nil r
  | _ => simp [renderTRec]

/-! ### Taxon layers as record lists -/

/-- The records of a taxon layer. -/
def tkbRecs (k : TKB) : List TRec :=
  (kbRecs k.base).map TRec.base ++
    k.parents.map (fun p => TRec.parent p.1 p.2) ++
    k.ranks.map (fun p => TRec.rank p.1 p.2) ++
    k.names.map (fun p => TRec.tname p.1 p.2)

/-- The base records of a record list. -/
def tBaseRecs (rs : List TRec) : List Rec :=
  rs.filterMap (fun r => match r with | .base b => some b | _ => none)

/-- The taxon layer assembled from a list of records. -/
def tkbOfRecs (rs : List TRec) : TKB where
  base := kbOfRecs (tBaseRecs rs)
  parents := rs.filterMap (fun r => match r with | .parent a b => some (a, b) | _ => none)
  ranks := rs.filterMap (fun r => match r with | .rank a rk => some (a, rk) | _ => none)
  names := rs.filterMap (fun r => match r with | .tname a n => some (a, n) | _ => none)

/-- **Taxon layers round-trip through their records.** -/
theorem tkbOfRecs_tkbRecs (k : TKB) : tkbOfRecs (tkbRecs k) = k := by
  obtain ⟨base, parents, ranks, names⟩ := k
  have hnone : ∀ {α β : Type} (l : List α), l.filterMap (fun _ => (none : Option β)) = [] :=
    fun l => List.filterMap_eq_nil_iff.2 fun _ _ => by simp
  simp [tkbOfRecs, tkbRecs, tBaseRecs, List.filterMap_append, List.filterMap_map,
    Function.comp_def, hnone, kbOfRecs_kbRecs]

/-! ### The complete codec -/

/-- Every string of a taxon layer is free of the separators. -/
def TKB.cleanB (k : TKB) : Bool :=
  KB.cleanB k.base &&
  k.parents.all (fun p => cleanQidB p.1 && cleanQidB p.2) &&
  k.ranks.all (fun p => cleanQidB p.1) &&
  k.names.all (fun p => cleanQidB p.1 && cleanFieldB p.2)

/-- Writes a taxon layer as text. -/
def renderTKB (k : TKB) : String := renderRecords ((tkbRecs k).map renderTRec)

/-- Reads a taxon layer from text. -/
def parseTKB? (str : String) : Option TKB :=
  ((parseRecords str).mapM parseTRec?).map tkbOfRecs

theorem clean_fields_of_tkbRecs {k : TKB} (h : TKB.cleanB k = true) :
    ∀ r ∈ (tkbRecs k).map renderTRec, r ≠ [] ∧ ∀ x ∈ r, cleanFieldB x = true := by
  simp only [TKB.cleanB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hbase, hparents⟩, hranks⟩, hnames⟩ := h
  have hqid : ∀ {q : Qid}, cleanQidB q = true → ∀ x ∈ qidTokens q, cleanFieldB x = true :=
    fun hq => cleanFieldB_of_mem_qidTokens hq
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨rec, hrec, rfl⟩ := hr
  refine ⟨renderTRec_ne_nil rec, ?_⟩
  simp only [tkbRecs, List.mem_append, List.mem_map] at hrec
  rcases hrec with ((hrec | hrec) | hrec) | hrec
  · obtain ⟨b, hb, rfl⟩ := hrec
    exact (clean_fields_of_kbRecs hbase (renderRec b) (List.mem_map_of_mem hb)).2
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by simpa using hparents p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_append.1 hx with hx | hx
    · exact hqid hp'.1 x hx
    · exact hqid hp'.2 x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_cons.1 hx with rfl | hx
    · exact cleanFieldB_renderRank _
    · exact hqid (hranks p hp) x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanFieldB p.2 = true := by simpa using hnames p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hp'.2
    · exact hqid hp'.1 x hx

/-- **The taxon file format is lossless**: reading back what was written returns exactly
the taxon layer that was written. -/
theorem parseTKB?_renderTKB (k : TKB) (h : TKB.cleanB k = true) :
    parseTKB? (renderTKB k) = some k := by
  have hne : (tkbRecs k).map renderTRec ≠ [] := by
    simp [tkbRecs, kbRecs]
  have hrecs := parseRecords_renderRecords _ hne (clean_fields_of_tkbRecs h)
  have hmap : List.mapM (parseTRec? ∘ renderTRec) (tkbRecs k) = some (tkbRecs k) := by
    induction tkbRecs k with
    | nil => rfl
    | cons r rs ih =>
        simp [List.mapM_cons, Function.comp_apply, parseTRec?_renderTRec, ih]
  simp [parseTKB?, renderTKB, hrecs, List.mapM_map, hmap, tkbOfRecs_tkbRecs]

end Cli
end Wikidata
