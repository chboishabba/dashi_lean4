import RequestProject.Cli.Format
import RequestProject.Enrichment

/-!
# A verified on-disk format for scanned sources

The enrichment tool downloads documents and reduces each of them to a
`Wikidata.ScannedSource`.  A run's scan is stored in a `.scan` file: one
tab-separated line per document,

```
src   https://en.wikipedia.org/wiki/Topology   en   Topology   Q42989 Q12482   P31 P279   https://…
```

with the three list-valued fields written space-separated, and `-` for the empty
list.

As everywhere else in the tool, the codec comes with a round-trip theorem:
`Wikidata.Cli.parseScan?_renderScan` says that reading back a scan the tool has
written returns exactly the scan that was written, provided the fields contain
no separator (`Wikidata.Cli.scanCleanB`, which the tool checks before writing).
-/

namespace Wikidata
namespace Cli

/-! ### Space-separated lists inside a field -/

/-- The separator used inside a list-valued field. -/
def spc : Char := ' '

/-- How the empty list is written. -/
def emptyMark : String := "-"

/-- Renders a list of tokens inside one field. -/
def renderList (xs : List String) : String :=
  if xs.isEmpty then emptyMark else joinChar spc xs

/-- Reads a list of tokens from one field. -/
def parseList (s : String) : List String :=
  if s = emptyMark then [] else splitChar spc s

/-- A token is *clean* when it can be written inside a list-valued field: no
separator of any kind, and not the marker for the empty list. -/
def cleanTokenB (x : String) : Bool :=
  cleanFieldB x && !x.toList.contains spc && x != emptyMark

theorem spc_notMem_of_cleanTokenB {x : String} (h : cleanTokenB x = true) : spc ∉ x.toList := by
  simp only [cleanTokenB, Bool.and_eq_true] at h
  simpa using h.1.2

theorem ne_emptyMark_of_cleanTokenB {x : String} (h : cleanTokenB x = true) : x ≠ emptyMark := by
  simp only [cleanTokenB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-- **Lists inside a field round-trip.** -/
theorem parseList_renderList (xs : List String) (h : ∀ x ∈ xs, cleanTokenB x = true) :
    parseList (renderList xs) = xs := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨ys, y, rfl⟩
  · simp [parseList, renderList]
  · rw [List.concat_eq_append] at h ⊢
    have hne : ys ++ [y] ≠ [] := by simp
    have hsplit : splitChar spc (joinChar spc (ys ++ [y])) = ys ++ [y] :=
      splitChar_joinChar spc _ (fun x hx => spc_notMem_of_cleanTokenB (h x hx)) hne
    have hrender : renderList (ys ++ [y]) = joinChar spc (ys ++ [y]) := by
      simp [renderList, List.isEmpty_iff]
    rw [hrender]
    by_cases hEq : joinChar spc (ys ++ [y]) = emptyMark
    · exfalso
      rw [hEq] at hsplit
      have : splitChar spc emptyMark = [emptyMark] := by decide
      rw [this] at hsplit
      have hy : y ∈ ys ++ [y] := by simp
      rw [← hsplit] at hy
      exact ne_emptyMark_of_cleanTokenB (h y (by rw [← hsplit]; exact hy))
        (by simpa using (List.mem_singleton.1 hy))
    · simp [parseList, hEq, hsplit]

/-! ### One document -/

/-- An item identifier inside a list-valued field.  Only ordinary Wikidata
identifiers can be written; the tool never produces the other kinds when
scanning a source. -/
def qidTok : Qid → String
  | .wd id => id
  | .ont n => "ont:" ++ n
  | .about q => "about:" ++ qidTok q
  | .lvl n => "lvl:" ++ renderNat n

/-- Whether an identifier is an ordinary Wikidata one. -/
def isWdB : Qid → Bool
  | .wd _ => true
  | _ => false

/-- The record of one scanned document. -/
def srcRec (s : ScannedSource) : Record :=
  ["src", s.ref.url, s.ref.lang, s.ref.title,
    renderList (s.mentions.map qidTok), renderList s.predicates, renderList s.cites]

/-- Reads the record of one scanned document. -/
def parseSrcRec? : Record → Option ScannedSource
  | ["src", url, lang, title, ms, ps, cs] =>
      some { ref := ⟨url, lang, title⟩
             mentions := (parseList ms).map Qid.wd
             predicates := parseList ps
             cites := parseList cs }
  | _ => none

/-- A scanned document is *clean* when every field of its record can be written. -/
def cleanSourceB (s : ScannedSource) : Bool :=
  cleanFieldB s.ref.url && cleanFieldB s.ref.lang && cleanFieldB s.ref.title &&
  s.mentions.all isWdB && s.mentions.all (fun q => cleanTokenB (qidTok q)) &&
  s.predicates.all cleanTokenB && s.cites.all cleanTokenB

theorem map_wd_qidTok {ms : List Qid} (h : ∀ q ∈ ms, isWdB q = true) :
    (ms.map qidTok).map Qid.wd = ms := by
  induction ms with
  | nil => simp
  | cons q ms ih =>
      have hq : isWdB q = true := h q List.mem_cons_self
      cases q with
      | wd id => simp [qidTok, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
      | ont n => simp [isWdB] at hq
      | about q => simp [isWdB] at hq
      | lvl n => simp [isWdB] at hq

/-- **One document round-trips.** -/
theorem parseSrcRec?_srcRec (s : ScannedSource) (h : cleanSourceB s = true) :
    parseSrcRec? (srcRec s) = some s := by
  simp only [cleanSourceB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hwd⟩, hm⟩, hp⟩, hc⟩ := h
  have hms : parseList (renderList (s.mentions.map qidTok)) = s.mentions.map qidTok := by
    refine parseList_renderList _ ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact hm q hq
  have hps : parseList (renderList s.predicates) = s.predicates :=
    parseList_renderList _ hp
  have hcs : parseList (renderList s.cites) = s.cites :=
    parseList_renderList _ hc
  simp only [srcRec, parseSrcRec?, hms, hps, hcs, map_wd_qidTok hwd]

/-! ### A whole scan -/

/-- Renders a scan: one line per document. -/
def renderScan (ss : List ScannedSource) : String := renderRecords (ss.map srcRec)

/-- Reads a scan; `none` if any line is malformed. -/
def parseScan? (s : String) : Option (List ScannedSource) :=
  (parseRecords s).mapM parseSrcRec?

/-- Whether a scan can be written. -/
def scanCleanB (ss : List ScannedSource) : Bool := ss.all cleanSourceB

theorem cleanFieldB_renderList {xs : List String} (h : ∀ x ∈ xs, cleanTokenB x = true) :
    cleanFieldB (renderList xs) = true := by
  by_cases hnil : xs.isEmpty
  · simp [renderList, hnil, cleanFieldB, emptyMark]
    decide
  · have : renderList xs = joinChar spc xs := by simp [renderList, hnil]
    rw [this]
    have htab : tab ∉ (joinChar spc xs).toList := by
      simp only [joinChar, String.toList_ofList]
      refine mem_intercalate_singleton (by decide) ?_
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      have hcf : cleanFieldB x = true := by
        have := h x hx
        simp only [cleanTokenB, Bool.and_eq_true] at this
        exact this.1.1
      exact (notMem_of_cleanFieldB hcf).1
    have hnl : nl ∉ (joinChar spc xs).toList := by
      simp only [joinChar, String.toList_ofList]
      refine mem_intercalate_singleton (by decide) ?_
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      have hcf : cleanFieldB x = true := by
        have := h x hx
        simp only [cleanTokenB, Bool.and_eq_true] at this
        exact this.1.1
      exact (notMem_of_cleanFieldB hcf).2
    simp only [cleanFieldB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact ⟨fun hmem => htab hmem, fun hmem => hnl hmem⟩

theorem cleanFieldB_of_mem_srcRec {s : ScannedSource} (h : cleanSourceB s = true) :
    ∀ x ∈ srcRec s, cleanFieldB x = true := by
  simp only [cleanSourceB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, hl⟩, ht⟩, -⟩, hm⟩, hp⟩, hc⟩ := h
  intro x hx
  simp only [srcRec, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact hu
  · exact hl
  · exact ht
  · refine cleanFieldB_renderList ?_
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact hm q hq
  · exact cleanFieldB_renderList hp
  · exact cleanFieldB_renderList hc

/-- **A scan round-trips**: what the tool writes is what it reads back. -/
theorem parseScan?_renderScan (ss : List ScannedSource) (hne : ss ≠ [])
    (h : scanCleanB ss = true) : parseScan? (renderScan ss) = some ss := by
  simp only [scanCleanB, List.all_eq_true] at h
  have hrecs : parseRecords (renderRecords (ss.map srcRec)) = ss.map srcRec := by
    refine parseRecords_renderRecords _ (by simpa using hne) ?_
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    exact ⟨by simp [srcRec], cleanFieldB_of_mem_srcRec (h s hs)⟩
  simp only [parseScan?, renderScan, hrecs]
  induction ss with
  | nil => simp
  | cons s ss ih =>
      have hs : parseSrcRec? (srcRec s) = some s := parseSrcRec?_srcRec s (h s List.mem_cons_self)
      have hrest : (ss.map srcRec).mapM parseSrcRec? = some ss := by
        clear ih hrecs hne
        induction ss with
        | nil => simp
        | cons t ts iht =>
            have ht : parseSrcRec? (srcRec t) = some t :=
              parseSrcRec?_srcRec t (h t (List.mem_cons_of_mem _ List.mem_cons_self))
            have : (ts.map srcRec).mapM parseSrcRec? = some ts :=
              iht fun x hx => h x (by
                rcases List.mem_cons.1 hx with rfl | hx'
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx'))
            simp [List.mapM_cons, ht, this]
      simp [List.mapM_cons, hs, hrest]

end Cli
end Wikidata
