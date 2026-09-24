import RequestProject.Cli.Format
import RequestProject.SeriesChain

/-!
# A verified on-disk format for series layers

`RequestProject.Cli.Format` stores a knowledge base as tab-separated records.  This file
extends the format with the three record kinds of the series layer, so that a whole `SKB`
can be written to a file and read back:

```
name    trilogy
item    wd      v1
inst    wd      v1      wd      Q7725634
series  wd      v1      wd      t
follows wd      v2      wd      v1
ord     1       wd      v1
```

The base records are exactly the ones of the knowledge base format, and the three new
keywords are `series` (P179), `follows` (P155) and `ord` (P1545).  The point of the file is
`Wikidata.Cli.parseSKB?_renderSKB`: **reading back a series layer that was written returns
exactly the layer that was written**, provided its identifiers and name carry no tab or
newline (`SKB.cleanB`).
-/

namespace Wikidata
namespace Cli

/-- A record of a series-layer file: a knowledge base record, or one of the three series
statements. -/
inductive SRec where
  /-- A record of the underlying knowledge base. -/
  | base (r : Rec)
  /-- A `part of the series` (P179) statement. -/
  | series (a t : Qid)
  /-- A `follows` (P155) statement. -/
  | follows (a b : Qid)
  /-- A `series ordinal` (P1545) value. -/
  | ord (a : Qid) (n : ℕ)
deriving Repr, DecidableEq, Inhabited

/-- Renders one series-layer record. -/
def renderSRec : SRec → Record
  | .base r => renderRec r
  | .series a t => "series" :: (qidTokens a ++ qidTokens t)
  | .follows a b => "follows" :: (qidTokens a ++ qidTokens b)
  | .ord a n => "ord" :: renderNat n :: qidTokens a

/-- Reads one series-layer record; anything that is not one of the three series keywords is
handed to the knowledge base reader. -/
def parseSRec? (r : Record) : Option SRec :=
  match r with
  | "series" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (t, []) => some (.series a t)
          | _ => none
      | _ => none
  | "follows" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (b, []) => some (.follows a b)
          | _ => none
      | _ => none
  | "ord" :: d :: ts =>
      match parseNat? d, parseQid? ts with
      | some n, some (a, []) => some (.ord a n)
      | _, _ => none
  | _ => (parseRec? r).map SRec.base

/-- The head keyword of a knowledge base record is never one of the series keywords, so
base records are read by the knowledge base reader. -/
theorem parseSRec?_renderRec (r : Rec) : parseSRec? (renderRec r) = some (.base r) := by
  cases r with
  | name s =>
      have h : parseRec? ["name", s] = some (Rec.name s) := parseRec?_renderRec (Rec.name s)
      show parseSRec? ["name", s] = _
      simp [parseSRec?, h]
  | item q =>
      have h : parseRec? ("item" :: qidTokens q) = some (Rec.item q) :=
        parseRec?_renderRec (Rec.item q)
      show parseSRec? ("item" :: qidTokens q) = _
      simp [parseSRec?, h]
  | level q n =>
      have h : parseRec? ("level" :: renderNat n :: qidTokens q) = some (Rec.level q n) :=
        parseRec?_renderRec (Rec.level q n)
      show parseSRec? ("level" :: renderNat n :: qidTokens q) = _
      simp [parseSRec?, h]
  | sub a b =>
      have h : parseRec? ("sub" :: (qidTokens a ++ qidTokens b)) = some (Rec.sub a b) :=
        parseRec?_renderRec (Rec.sub a b)
      show parseSRec? ("sub" :: (qidTokens a ++ qidTokens b)) = _
      simp [parseSRec?, h]
  | inst a c =>
      have h : parseRec? ("inst" :: (qidTokens a ++ qidTokens c)) = some (Rec.inst a c) :=
        parseRec?_renderRec (Rec.inst a c)
      show parseSRec? ("inst" :: (qidTokens a ++ qidTokens c)) = _
      simp [parseSRec?, h]
  | disj a b =>
      have h : parseRec? ("disj" :: (qidTokens a ++ qidTokens b)) = some (Rec.disj a b) :=
        parseRec?_renderRec (Rec.disj a b)
      show parseSRec? ("disj" :: (qidTokens a ++ qidTokens b)) = _
      simp [parseSRec?, h]

/-- **Records round-trip.** -/
theorem parseSRec?_renderSRec (r : SRec) : parseSRec? (renderSRec r) = some r := by
  cases r with
  | base r => exact parseSRec?_renderRec r
  | series a t =>
      show parseSRec? ("series" :: (qidTokens a ++ qidTokens t)) = _
      rw [show qidTokens t = qidTokens t ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseSRec?, parseQid?_qidTokens]
  | follows a b =>
      show parseSRec? ("follows" :: (qidTokens a ++ qidTokens b)) = _
      rw [show qidTokens b = qidTokens b ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseSRec?, parseQid?_qidTokens]
  | ord a n =>
      show parseSRec? ("ord" :: renderNat n :: qidTokens a) = _
      rw [show qidTokens a = qidTokens a ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseSRec?, parseQid?_qidTokens, parseNat?_renderNat]

theorem renderSRec_ne_nil (r : SRec) : renderSRec r ≠ [] := by
  cases r with
  | base r => simpa [renderSRec] using renderRec_ne_nil r
  | _ => simp [renderSRec]

/-! ### Series layers as record lists -/

/-- The records of a series layer. -/
def skbRecs (s : SKB) : List SRec :=
  (kbRecs s.base).map SRec.base ++
    s.series.map (fun p => SRec.series p.1 p.2) ++
    s.follows.map (fun p => SRec.follows p.1 p.2) ++
    s.ordinals.map (fun p => SRec.ord p.1 p.2)

/-- The base records of a record list. -/
def baseRecs (rs : List SRec) : List Rec :=
  rs.filterMap (fun r => match r with | .base b => some b | _ => none)

/-- The series layer assembled from a list of records. -/
def skbOfRecs (rs : List SRec) : SKB where
  base := kbOfRecs (baseRecs rs)
  series := rs.filterMap (fun r => match r with | .series a t => some (a, t) | _ => none)
  follows := rs.filterMap (fun r => match r with | .follows a b => some (a, b) | _ => none)
  ordinals := rs.filterMap (fun r => match r with | .ord a n => some (a, n) | _ => none)

/-- **Series layers round-trip through their records.** -/
theorem skbOfRecs_skbRecs (s : SKB) : skbOfRecs (skbRecs s) = s := by
  obtain ⟨base, series, follows, ordinals⟩ := s
  have hnone : ∀ {α β : Type} (l : List α), l.filterMap (fun _ => (none : Option β)) = [] :=
    fun l => List.filterMap_eq_nil_iff.2 fun _ _ => by simp
  simp [skbOfRecs, skbRecs, baseRecs, List.filterMap_append, List.filterMap_map,
    Function.comp_def, hnone, kbOfRecs_kbRecs]

/-! ### The complete codec -/

/-- Every string of a series layer is free of the separators. -/
def SKB.cleanB (s : SKB) : Bool :=
  KB.cleanB s.base &&
  s.series.all (fun p => cleanQidB p.1 && cleanQidB p.2) &&
  s.follows.all (fun p => cleanQidB p.1 && cleanQidB p.2) &&
  s.ordinals.all (fun p => cleanQidB p.1)

/-- Writes a series layer as text. -/
def renderSKB (s : SKB) : String := renderRecords ((skbRecs s).map renderSRec)

/-- Reads a series layer from text. -/
def parseSKB? (str : String) : Option SKB :=
  ((parseRecords str).mapM parseSRec?).map skbOfRecs

theorem clean_fields_of_skbRecs {s : SKB} (h : SKB.cleanB s = true) :
    ∀ r ∈ (skbRecs s).map renderSRec, r ≠ [] ∧ ∀ x ∈ r, cleanFieldB x = true := by
  simp only [SKB.cleanB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hbase, hseries⟩, hfollows⟩, hord⟩ := h
  have hqid : ∀ {q : Qid}, cleanQidB q = true → ∀ x ∈ qidTokens q, cleanFieldB x = true :=
    fun hq => cleanFieldB_of_mem_qidTokens hq
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨rec, hrec, rfl⟩ := hr
  refine ⟨renderSRec_ne_nil rec, ?_⟩
  simp only [skbRecs, List.mem_append, List.mem_map] at hrec
  rcases hrec with ((hrec | hrec) | hrec) | hrec
  · obtain ⟨b, hb, rfl⟩ := hrec
    exact (clean_fields_of_kbRecs hbase (renderRec b) (List.mem_map_of_mem hb)).2
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by simpa using hseries p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_append.1 hx with hx | hx
    · exact hqid hp'.1 x hx
    · exact hqid hp'.2 x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by simpa using hfollows p hp
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
    · exact cleanFieldB_renderNat _
    · exact hqid (hord p hp) x hx

/-- **The series file format is lossless**: reading back what was written returns exactly
the series layer that was written. -/
theorem parseSKB?_renderSKB (s : SKB) (h : SKB.cleanB s = true) :
    parseSKB? (renderSKB s) = some s := by
  have hne : (skbRecs s).map renderSRec ≠ [] := by
    simp [skbRecs, kbRecs]
  have hrecs := parseRecords_renderRecords _ hne (clean_fields_of_skbRecs h)
  have hmap : List.mapM (parseSRec? ∘ renderSRec) (skbRecs s) = some (skbRecs s) := by
    induction skbRecs s with
    | nil => rfl
    | cons r rs ih =>
        simp [List.mapM_cons, Function.comp_apply, parseSRec?_renderSRec, ih]
  simp [parseSKB?, renderSKB, hrecs, List.mapM_map, hmap, skbOfRecs_skbRecs]

end Cli
end Wikidata
