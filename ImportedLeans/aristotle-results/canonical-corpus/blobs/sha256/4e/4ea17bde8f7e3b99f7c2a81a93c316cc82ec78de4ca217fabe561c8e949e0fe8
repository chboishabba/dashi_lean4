import RequestProject.Queries
import RequestProject.Cli.Format

/-!
# A surface syntax for queries

`RequestProject.Queries` gives a query language over knowledge bases together with a
certified evaluator.  This file adds the small textual syntax the command line tool
uses, so a query can be written on the shell:

```
wikidata query corpus.wdkb 'inst ?x Q5' 'sub ?x Q35120' --select x
```

Each argument is one atom, written `KEYWORD ARG …` with `?name` for a variable and a
plain identifier for an item.  The keywords are `sub`, `inst` (the *derived* relations),
`dsub`, `dinst` (only directly asserted statements), `class` and `ne`.

The result is `Wikidata.Cli.parseAtom?_showAtom`: **the surface syntax round-trips** —
printing an atom and reading it back returns the atom, as long as its identifiers are
nonempty, contain no space, and do not begin with `?`.  Combined with
`Wikidata.Query.mem_eval_iff` this pins down what the `query` command computes.
-/

namespace Wikidata
namespace Cli

open Query

/-- The separator of the surface syntax. -/
def sp : Char := ' '

/-- An item identifier, for humans. -/
def qidText : Qid → String
  | .wd id => id
  | .ont n => "ontology:" ++ n
  | .about q => "about(" ++ qidText q ++ ")"
  | .lvl n => "level-" ++ renderNat n

/-- Reads a query term: `?x` is a variable, anything else names an item. -/
def parseTm (s : String) : Tm :=
  match s.toList with
  | '?' :: cs => .var (String.ofList cs)
  | _ => .item (.wd s)

/-- Prints a query term. -/
def showTm : Tm → String
  | .var n => String.ofList ('?' :: n.toList)
  | .item q => qidText q

/-- A term is *surface* when it prints and reads back unambiguously: a nonempty,
space-free variable name, or an ordinary item identifier that is nonempty, space-free
and does not start with `?`. -/
def tmOkB : Tm → Bool
  | .var n => !n.toList.isEmpty && !n.toList.contains sp
  | .item (.wd id) => !id.toList.isEmpty && !id.toList.contains sp && id.toList.head? != some '?'
  | .item _ => false

/-- An atom is *surface* when all its terms are. -/
def atomOkB : Atom → Bool
  | .sub s o | .inst s o | .dsub s o | .dinst s o | .ne s o => tmOkB s && tmOkB o
  | .isClass s => tmOkB s

/-- Prints an atom. -/
def showAtom : Atom → String
  | .sub s o => joinChar sp ["sub", showTm s, showTm o]
  | .inst s o => joinChar sp ["inst", showTm s, showTm o]
  | .dsub s o => joinChar sp ["dsub", showTm s, showTm o]
  | .dinst s o => joinChar sp ["dinst", showTm s, showTm o]
  | .isClass s => joinChar sp ["class", showTm s]
  | .ne s o => joinChar sp ["ne", showTm s, showTm o]

/-- Reads an atom. -/
def parseAtom? (s : String) : Option Atom :=
  match splitChar sp s with
  | ["sub", a, b] => some (.sub (parseTm a) (parseTm b))
  | ["inst", a, b] => some (.inst (parseTm a) (parseTm b))
  | ["dsub", a, b] => some (.dsub (parseTm a) (parseTm b))
  | ["dinst", a, b] => some (.dinst (parseTm a) (parseTm b))
  | ["class", a] => some (.isClass (parseTm a))
  | ["ne", a, b] => some (.ne (parseTm a) (parseTm b))
  | _ => none

/-- Reads a whole query, one atom per argument. -/
def parseQuery? (ss : List String) : Option BGP := ss.mapM parseAtom?

/-- Prints a whole query, one atom per string. -/
def showQuery (q : BGP) : List String := q.map showAtom

/-! ### The syntax round-trips -/

theorem toList_showTm_var (n : String) : (showTm (.var n)).toList = '?' :: n.toList := by
  simp [showTm]

theorem sp_notMem_showTm {t : Tm} (h : tmOkB t = true) : sp ∉ (showTm t).toList := by
  cases t with
  | var n =>
      simp only [tmOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
      rw [toList_showTm_var]
      intro hmem
      rcases List.mem_cons.1 hmem with hc | hc
      · exact absurd hc (by decide)
      · exact absurd hc (by simpa using h.2)
  | item q =>
      cases q with
      | wd id =>
          simp only [tmOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
          have : sp ∉ id.toList := by simpa using h.1.2
          simpa [showTm, qidText] using this
      | ont n => simp [tmOkB] at h
      | about q => simp [tmOkB] at h
      | lvl n => simp [tmOkB] at h

theorem parseTm_showTm {t : Tm} (h : tmOkB t = true) : parseTm (showTm t) = t := by
  cases t with
  | var n =>
      have hl : (showTm (Tm.var n)).toList = '?' :: n.toList := toList_showTm_var n
      unfold parseTm
      rw [hl]
      simp
  | item q =>
      cases q with
      | wd id =>
          simp only [tmOkB, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
          obtain ⟨c, cs, hcs⟩ : ∃ c cs, id.toList = c :: cs := by
            cases hid : id.toList with
            | nil => rw [hid] at h; simp at h
            | cons c cs => exact ⟨c, cs, rfl⟩
          have hc : c ≠ '?' := by
            intro hce
            exact h.2 (by rw [hcs, hce]; rfl)
          have hs : showTm (Tm.item (Qid.wd id)) = id := rfl
          rw [hs]
          unfold parseTm
          rw [hcs]
          split
          · rename_i cs' heq
            exact absurd (List.cons.inj heq).1 hc
          · rfl
      | ont n => simp [tmOkB] at h
      | about q => simp [tmOkB] at h
      | lvl n => simp [tmOkB] at h

theorem splitChar_showAtom_aux (kw : String) (ts : List Tm) (hts : ∀ t ∈ ts, tmOkB t = true)
    (hkw : sp ∉ kw.toList) :
    splitChar sp (joinChar sp (kw :: ts.map showTm)) = kw :: ts.map showTm := by
  refine splitChar_joinChar sp _ ?_ (by simp)
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hkw
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact sp_notMem_showTm (hts t ht)

/-- **The surface syntax round-trips**: printing a surface atom and reading it back
returns the atom. -/
theorem parseAtom?_showAtom {a : Atom} (h : atomOkB a = true) :
    parseAtom? (showAtom a) = some a := by
  cases a with
  | sub s o =>
      simp only [atomOkB, Bool.and_eq_true] at h
      have hsplit := splitChar_showAtom_aux "sub" [s, o]
        (by intro t ht; simp at ht; rcases ht with rfl | rfl; exacts [h.1, h.2]) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h.1, parseTm_showTm h.2]
  | inst s o =>
      simp only [atomOkB, Bool.and_eq_true] at h
      have hsplit := splitChar_showAtom_aux "inst" [s, o]
        (by intro t ht; simp at ht; rcases ht with rfl | rfl; exacts [h.1, h.2]) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h.1, parseTm_showTm h.2]
  | dsub s o =>
      simp only [atomOkB, Bool.and_eq_true] at h
      have hsplit := splitChar_showAtom_aux "dsub" [s, o]
        (by intro t ht; simp at ht; rcases ht with rfl | rfl; exacts [h.1, h.2]) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h.1, parseTm_showTm h.2]
  | dinst s o =>
      simp only [atomOkB, Bool.and_eq_true] at h
      have hsplit := splitChar_showAtom_aux "dinst" [s, o]
        (by intro t ht; simp at ht; rcases ht with rfl | rfl; exacts [h.1, h.2]) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h.1, parseTm_showTm h.2]
  | isClass s =>
      simp only [atomOkB] at h
      have hsplit := splitChar_showAtom_aux "class" [s]
        (by intro t ht; simp at ht; rcases ht with rfl; exact h) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h]
  | ne s o =>
      simp only [atomOkB, Bool.and_eq_true] at h
      have hsplit := splitChar_showAtom_aux "ne" [s, o]
        (by intro t ht; simp at ht; rcases ht with rfl | rfl; exacts [h.1, h.2]) (by decide)
      simp only [List.map_cons, List.map_nil] at hsplit
      rw [showAtom, parseAtom?, hsplit]
      simp [parseTm_showTm h.1, parseTm_showTm h.2]

/-- **Whole queries round-trip.** -/
theorem parseQuery?_showQuery {q : BGP} (h : ∀ a ∈ q, atomOkB a = true) :
    parseQuery? (showQuery q) = some q := by
  induction q with
  | nil => rfl
  | cons a as ih =>
      have ha := parseAtom?_showAtom (h a (by simp))
      have hrest := ih (fun b hb => h b (by simp [hb]))
      simp only [parseQuery?, showQuery, List.map_cons, List.mapM_cons] at hrest ⊢
      simp [ha, hrest]

end Cli
end Wikidata
