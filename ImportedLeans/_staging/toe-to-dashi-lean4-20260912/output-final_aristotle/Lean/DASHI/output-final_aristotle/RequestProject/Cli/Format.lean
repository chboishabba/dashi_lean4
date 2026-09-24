import RequestProject.Engine

/-!
# A verified on-disk format for knowledge bases

The command line tool stores knowledge bases in a simple tab-separated, one
record per line text format (`.wdkb`):

```
name    my ontology
item    wd      Q5
level   1       wd      Q5
sub     wd      Q5      wd      Q215627
inst    wd      Q42     wd      Q5
disj    wd      Q5      wd      Q16521
```

The point of this file is `Wikidata.Cli.parseKB?_renderKB`: **reading back a
knowledge base that the tool has written returns exactly the knowledge base that
was written**, provided the identifiers and the name contain no tab or newline
(`KB.cleanB`, which the tool checks before writing).  Nothing is silently lost or
altered by a round trip through the disk.

The codec is built in layers, each with its own round-trip theorem:

* decimal numerals (`renderNat` / `parseNat?`, `parseNat?_renderNat`);
* fields and lines (`joinChar` / `splitChar`, `splitChar_joinChar`);
* item identifiers as token sequences (`qidTokens` / `parseQid?`,
  `parseQid?_qidTokens`);
* records (`renderRec` / `parseRec?`, `parseRec?_renderRec`);
* knowledge bases as record lists (`kbRecs` / `kbOfRecs`, `kbOfRecs_kbRecs`).
-/

namespace Wikidata
namespace Cli

/-! ### Decimal numerals -/

/-- Reads a decimal digit. -/
def charToDigit? (c : Char) : Option ℕ :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- The decimal digits of `n`, most significant first. -/
def natChars (n : ℕ) : List Char := (Nat.digits 10 n).reverse.map fun d => Char.ofNat (48 + d)

/-- `n` as a decimal numeral. -/
def renderNat (n : ℕ) : String := if n = 0 then "0" else String.ofList (natChars n)

/-- Reads a decimal numeral. -/
def parseNat? (s : String) : Option ℕ :=
  match s.toList.mapM charToDigit? with
  | some ds => if ds.isEmpty then none else some (Nat.ofDigits 10 ds.reverse)
  | none => none

theorem mapM_natChars (ds : List ℕ) (h : ∀ d ∈ ds, d < 10) :
    (ds.map fun d => Char.ofNat (48 + d)).mapM charToDigit? = some ds := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd : d < 10 := h d List.mem_cons_self
      have hchar : (Char.ofNat (48 + d)).toNat = 48 + d := by
        rw [Char.toNat_ofNat, if_pos (Or.inl (by omega))]
      simp only [List.map_cons, List.mapM_cons, charToDigit?, hchar,
        if_pos (⟨by omega, by omega⟩ : 48 ≤ 48 + d ∧ 48 + d ≤ 57),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      simp

/-- **Numerals round-trip.** -/
theorem parseNat?_renderNat (n : ℕ) : parseNat? (renderNat n) = some n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hpos : n ≠ 0 := by omega
    have hdig : ∀ d ∈ (Nat.digits 10 n).reverse, d < 10 := fun d hd =>
      Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hd)
    show parseNat? (if n = 0 then "0" else String.ofList (natChars n)) = some n
    rw [if_neg hpos]
    simp only [parseNat?, String.toList_ofList, natChars, mapM_natChars _ hdig]
    rw [if_neg (by simpa using Nat.digits_ne_nil_iff_ne_zero.2 hpos)]
    simp [Nat.ofDigits_digits]

/-! ### Fields and lines -/

/-- The field separator. -/
def tab : Char := '\t'

/-- The record separator. -/
def nl : Char := '\n'

/-- Splits a string at every occurrence of `c`. -/
def splitChar (c : Char) (s : String) : List String := (s.toList.splitOn c).map String.ofList

/-- Joins strings with `c` in between. -/
def joinChar (c : Char) (xs : List String) : String :=
  String.ofList ([c].intercalate (xs.map String.toList))

/-- **Splitting undoes joining** for separator-free pieces. -/
theorem splitChar_joinChar (c : Char) (xs : List String)
    (h : ∀ x ∈ xs, c ∉ x.toList) (hne : xs ≠ []) : splitChar c (joinChar c xs) = xs := by
  simp only [splitChar, joinChar, String.toList_ofList]
  rw [List.splitOn_intercalate c (ls := xs.map String.toList) ?_ ?_]
  · simp [Function.comp_def, String.ofList_toList]
  · intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    exact h x hx
  · simpa using hne

/-- A field is *clean* when it contains neither separator. -/
def cleanFieldB (x : String) : Bool := !x.toList.contains tab && !x.toList.contains nl

theorem notMem_of_cleanFieldB {x : String} (h : cleanFieldB x = true) :
    tab ∉ x.toList ∧ nl ∉ x.toList := by
  simp only [cleanFieldB, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1, by simpa using h.2⟩

/-- A record is a list of fields; it is rendered as one line. -/
abbrev Record := List String

/-- Renders a list of records as text. -/
def renderRecords (rs : List Record) : String := joinChar nl (rs.map (joinChar tab))

/-- Reads text back as a list of records. -/
def parseRecords (s : String) : List Record := (splitChar nl s).map (splitChar tab)

theorem mem_intercalate_singleton {α : Type*} {sep : α} {ls : List (List α)} {c : α}
    (hsep : c ≠ sep) (h : ∀ l ∈ ls, c ∉ l) : c ∉ [sep].intercalate ls := by
  induction ls with
  | nil => simp [List.intercalate]
  | cons l ls ih =>
      cases ls with
      | nil => simpa [List.intercalate] using h l List.mem_cons_self
      | cons l' ls' =>
          have hrec : [sep].intercalate (l :: l' :: ls') =
              l ++ sep :: ([sep].intercalate (l' :: ls')) := by simp [List.intercalate]
          rw [hrec]
          simp only [List.mem_append, List.mem_cons, not_or]
          exact ⟨h l List.mem_cons_self, hsep, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem nl_notMem_joinChar_tab {r : Record} (h : ∀ x ∈ r, cleanFieldB x = true) :
    nl ∉ (joinChar tab r).toList := by
  simp only [joinChar, String.toList_ofList]
  refine mem_intercalate_singleton (by decide) ?_
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact (notMem_of_cleanFieldB (h x hx)).2

/-- **Text round-trips**: a list of nonempty records with clean fields is recovered
exactly. -/
theorem parseRecords_renderRecords (rs : List Record) (hne : rs ≠ [])
    (hrec : ∀ r ∈ rs, r ≠ [] ∧ ∀ x ∈ r, cleanFieldB x = true) :
    parseRecords (renderRecords rs) = rs := by
  have hlines : splitChar nl (joinChar nl (rs.map (joinChar tab))) = rs.map (joinChar tab) := by
    refine splitChar_joinChar nl _ ?_ (by simpa using hne)
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact nl_notMem_joinChar_tab (hrec r hr).2
  simp only [parseRecords, renderRecords, hlines, List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id rs)
  intro r hr
  simp only [Function.comp_apply]
  exact splitChar_joinChar tab r
    (fun x hx => (notMem_of_cleanFieldB ((hrec r hr).2 x hx)).1) (hrec r hr).1

/-! ### Identifiers -/

/-- An item identifier as a sequence of fields. -/
def qidTokens : Qid → List String
  | .wd id => ["wd", id]
  | .ont n => ["ont", n]
  | .about q => "about" :: qidTokens q
  | .lvl n => ["lvl", renderNat n]

/-- Reads an item identifier from the front of a sequence of fields, returning the
unconsumed fields. -/
def parseQid? : List String → Option (Qid × List String)
  | "wd" :: id :: rest => some (.wd id, rest)
  | "ont" :: n :: rest => some (.ont n, rest)
  | "about" :: rest => (parseQid? rest).map fun r => (.about r.1, r.2)
  | "lvl" :: d :: rest => (parseNat? d).map fun n => (.lvl n, rest)
  | _ => none

/-- **Identifiers round-trip**, even in the middle of a record. -/
theorem parseQid?_qidTokens (q : Qid) (rest : List String) :
    parseQid? (qidTokens q ++ rest) = some (q, rest) := by
  induction q generalizing rest with
  | wd id => rfl
  | ont n => rfl
  | about q ih => simp [qidTokens, parseQid?, ih]
  | lvl n => simp [qidTokens, parseQid?, parseNat?_renderNat]

/-- Identifiers with clean strings. -/
def cleanQidB : Qid → Bool
  | .wd id => cleanFieldB id
  | .ont n => cleanFieldB n
  | .about q => cleanQidB q
  | .lvl _ => true

theorem cleanFieldB_renderNat (n : ℕ) : cleanFieldB (renderNat n) = true := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hpos : n ≠ 0 := by omega
    show cleanFieldB (if n = 0 then "0" else String.ofList (natChars n)) = true
    rw [if_neg hpos]
    have key : ∀ c ∈ natChars n, c ≠ tab ∧ c ≠ nl := by
      intro c hc
      simp only [natChars, List.mem_map, List.mem_reverse] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      have hd10 : d < 10 := Nat.digits_lt_base (by norm_num) hd
      have hnat : (Char.ofNat (48 + d)).toNat = 48 + d := by
        rw [Char.toNat_ofNat, if_pos (Or.inl (by omega))]
      constructor <;> intro hEq <;> rw [hEq] at hnat <;> simp [tab, nl, Char.toNat] at hnat <;>
        omega
    simp only [cleanFieldB, String.toList_ofList, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact ⟨fun hmem => (key _ hmem).1 rfl, fun hmem => (key _ hmem).2 rfl⟩

theorem cleanFieldB_of_mem_qidTokens {q : Qid} (h : cleanQidB q = true) :
    ∀ x ∈ qidTokens q, cleanFieldB x = true := by
  induction q with
  | wd id =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · simpa using (List.mem_singleton.1 hx) ▸ h
  | ont n =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · simpa using (List.mem_singleton.1 hx) ▸ h
  | about q ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · exact ih h x hx
  | lvl n =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · decide
      · rw [List.mem_singleton.1 hx]; exact cleanFieldB_renderNat n

/-! ### Records of a knowledge base -/

/-- One line of the file format. -/
inductive Rec where
  /-- The name of the knowledge base. -/
  | name (s : String)
  /-- An item. -/
  | item (q : Qid)
  /-- The metaclass level of an item. -/
  | level (q : Qid) (n : ℕ)
  /-- A `subclass of` (P279) statement. -/
  | sub (a b : Qid)
  /-- An `instance of` (P31) statement. -/
  | inst (a c : Qid)
  /-- A disjointness declaration. -/
  | disj (a b : Qid)
deriving Repr, DecidableEq, Inhabited

/-- Renders one record. -/
def renderRec : Rec → Record
  | .name s => ["name", s]
  | .item q => "item" :: qidTokens q
  | .level q n => "level" :: renderNat n :: qidTokens q
  | .sub a b => "sub" :: (qidTokens a ++ qidTokens b)
  | .inst a c => "inst" :: (qidTokens a ++ qidTokens c)
  | .disj a b => "disj" :: (qidTokens a ++ qidTokens b)

/-- Reads one record. -/
def parseRec? : Record → Option Rec
  | ["name", s] => some (.name s)
  | "item" :: ts =>
      match parseQid? ts with
      | some (q, []) => some (.item q)
      | _ => none
  | "level" :: d :: ts =>
      match parseNat? d, parseQid? ts with
      | some n, some (q, []) => some (.level q n)
      | _, _ => none
  | "sub" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (b, []) => some (.sub a b)
          | _ => none
      | _ => none
  | "inst" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (c, []) => some (.inst a c)
          | _ => none
      | _ => none
  | "disj" :: ts =>
      match parseQid? ts with
      | some (a, ts') =>
          match parseQid? ts' with
          | some (b, []) => some (.disj a b)
          | _ => none
      | _ => none
  | _ => none

/-- **Records round-trip.** -/
theorem parseRec?_renderRec (r : Rec) : parseRec? (renderRec r) = some r := by
  cases r with
  | name s => rfl
  | item q =>
      show parseRec? ("item" :: qidTokens q) = _
      rw [show qidTokens q = qidTokens q ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseRec?, parseQid?_qidTokens]
  | level q n =>
      show parseRec? ("level" :: renderNat n :: qidTokens q) = _
      rw [show qidTokens q = qidTokens q ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseRec?, parseQid?_qidTokens, parseNat?_renderNat]
  | sub a b =>
      show parseRec? ("sub" :: (qidTokens a ++ qidTokens b)) = _
      rw [show qidTokens b = qidTokens b ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseRec?, parseQid?_qidTokens]
  | inst a c =>
      show parseRec? ("inst" :: (qidTokens a ++ qidTokens c)) = _
      rw [show qidTokens c = qidTokens c ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseRec?, parseQid?_qidTokens]
  | disj a b =>
      show parseRec? ("disj" :: (qidTokens a ++ qidTokens b)) = _
      rw [show qidTokens b = qidTokens b ++ ([] : List String) from (List.append_nil _).symm]
      simp only [parseRec?, parseQid?_qidTokens]

theorem renderRec_ne_nil (r : Rec) : renderRec r ≠ [] := by
  cases r <;> simp [renderRec]

/-! ### Knowledge bases as record lists -/

/-- The records of a knowledge base. -/
def kbRecs (kb : KB) : List Rec :=
  Rec.name kb.name ::
    (kb.items.map Rec.item ++ kb.levels.map (fun p => Rec.level p.1 p.2) ++
      kb.sub.map (fun p => Rec.sub p.1 p.2) ++ kb.inst.map (fun p => Rec.inst p.1 p.2) ++
      kb.disj.map (fun p => Rec.disj p.1 p.2))

/-- The knowledge base assembled from a list of records. -/
def kbOfRecs : List Rec → KB
  | [] => { items := [] }
  | .name s :: rs => { kbOfRecs rs with name := s }
  | .item q :: rs => let kb := kbOfRecs rs; { kb with items := q :: kb.items }
  | .level q n :: rs => let kb := kbOfRecs rs; { kb with levels := (q, n) :: kb.levels }
  | .sub a b :: rs => let kb := kbOfRecs rs; { kb with sub := (a, b) :: kb.sub }
  | .inst a c :: rs => let kb := kbOfRecs rs; { kb with inst := (a, c) :: kb.inst }
  | .disj a b :: rs => let kb := kbOfRecs rs; { kb with disj := (a, b) :: kb.disj }

theorem kbOfRecs_items_append (qs : List Qid) (rs : List Rec) :
    kbOfRecs (qs.map Rec.item ++ rs) =
      { kbOfRecs rs with items := qs ++ (kbOfRecs rs).items } := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp [kbOfRecs, ih]

theorem kbOfRecs_levels_append (ls : List (Qid × ℕ)) (rs : List Rec) :
    kbOfRecs (ls.map (fun p => Rec.level p.1 p.2) ++ rs) =
      { kbOfRecs rs with levels := ls ++ (kbOfRecs rs).levels } := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp [kbOfRecs, ih]

theorem kbOfRecs_sub_append (ss : List (Qid × Qid)) (rs : List Rec) :
    kbOfRecs (ss.map (fun p => Rec.sub p.1 p.2) ++ rs) =
      { kbOfRecs rs with sub := ss ++ (kbOfRecs rs).sub } := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [kbOfRecs, ih]

theorem kbOfRecs_inst_append (is : List (Qid × Qid)) (rs : List Rec) :
    kbOfRecs (is.map (fun p => Rec.inst p.1 p.2) ++ rs) =
      { kbOfRecs rs with inst := is ++ (kbOfRecs rs).inst } := by
  induction is with
  | nil => simp
  | cons i is ih => simp [kbOfRecs, ih]

theorem kbOfRecs_disj_append (ds : List (Qid × Qid)) (rs : List Rec) :
    kbOfRecs (ds.map (fun p => Rec.disj p.1 p.2) ++ rs) =
      { kbOfRecs rs with disj := ds ++ (kbOfRecs rs).disj } := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [kbOfRecs, ih]

/-- **A knowledge base is recovered from its records.** -/
theorem kbOfRecs_kbRecs (kb : KB) : kbOfRecs (kbRecs kb) = kb := by
  obtain ⟨name, items, levels, sub, inst, disj⟩ := kb
  have hd : kbOfRecs (disj.map fun p => Rec.disj p.1 p.2) =
      { items := [], disj := disj } := by
    simpa [kbOfRecs] using kbOfRecs_disj_append disj []
  simp only [kbRecs, kbOfRecs, List.append_assoc, kbOfRecs_items_append,
    kbOfRecs_levels_append, kbOfRecs_sub_append, kbOfRecs_inst_append, hd]
  simp

/-! ### The complete codec -/

/-- Every string of a knowledge base is free of the separators. -/
def KB.cleanB (kb : KB) : Bool :=
  cleanFieldB kb.name &&
  kb.items.all cleanQidB &&
  kb.levels.all (fun p => cleanQidB p.1) &&
  kb.sub.all (fun p => cleanQidB p.1 && cleanQidB p.2) &&
  kb.inst.all (fun p => cleanQidB p.1 && cleanQidB p.2) &&
  kb.disj.all (fun p => cleanQidB p.1 && cleanQidB p.2)

/-- Writes a knowledge base as text. -/
def renderKB (kb : KB) : String := renderRecords ((kbRecs kb).map renderRec)

/-- Reads a knowledge base from text. -/
def parseKB? (s : String) : Option KB := ((parseRecords s).mapM parseRec?).map kbOfRecs

theorem clean_fields_of_kbRecs {kb : KB} (h : KB.cleanB kb = true) :
    ∀ r ∈ (kbRecs kb).map renderRec, r ≠ [] ∧ ∀ x ∈ r, cleanFieldB x = true := by
  simp only [KB.cleanB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hname, hitems⟩, hlevels⟩, hsub⟩, hinst⟩, hdisj⟩ := h
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨rec, hrec, rfl⟩ := hr
  refine ⟨renderRec_ne_nil rec, ?_⟩
  have hqid : ∀ {q : Qid}, cleanQidB q = true → ∀ x ∈ qidTokens q, cleanFieldB x = true :=
    fun hq => cleanFieldB_of_mem_qidTokens hq
  simp only [kbRecs, List.mem_cons, List.mem_append, List.mem_map] at hrec
  rcases hrec with rfl | hrec
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · rw [List.mem_singleton.1 hx]; exact hname
  rcases hrec with (((hrec | hrec) | hrec) | hrec) | hrec
  · obtain ⟨q, hq, rfl⟩ := hrec
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · exact hqid (hitems q hq) x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_cons.1 hx with rfl | hx
    · exact cleanFieldB_renderNat _
    · exact hqid (hlevels p hp) x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by
      simpa using hsub p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_append.1 hx with hx | hx
    · exact hqid hp'.1 x hx
    · exact hqid hp'.2 x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by
      simpa using hinst p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_append.1 hx with hx | hx
    · exact hqid hp'.1 x hx
    · exact hqid hp'.2 x hx
  · obtain ⟨p, hp, rfl⟩ := hrec
    have hp' : cleanQidB p.1 = true ∧ cleanQidB p.2 = true := by
      simpa using hdisj p hp
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · decide
    rcases List.mem_append.1 hx with hx | hx
    · exact hqid hp'.1 x hx
    · exact hqid hp'.2 x hx

/-- **The file format is lossless**: reading back what the tool wrote returns
exactly the knowledge base that was written. -/
theorem parseKB?_renderKB (kb : KB) (h : KB.cleanB kb = true) : parseKB? (renderKB kb) = some kb := by
  have hne : (kbRecs kb).map renderRec ≠ [] := by simp [kbRecs]
  have hrecs := parseRecords_renderRecords _ hne (clean_fields_of_kbRecs h)
  have hmap : List.mapM (parseRec? ∘ renderRec) (kbRecs kb) = some (kbRecs kb) := by
    induction kbRecs kb with
    | nil => rfl
    | cons r rs ih =>
        simp [List.mapM_cons, Function.comp_apply, parseRec?_renderRec, ih]
  simp [parseKB?, renderKB, hrecs, List.mapM_map, hmap, kbOfRecs_kbRecs]

end Cli
end Wikidata
