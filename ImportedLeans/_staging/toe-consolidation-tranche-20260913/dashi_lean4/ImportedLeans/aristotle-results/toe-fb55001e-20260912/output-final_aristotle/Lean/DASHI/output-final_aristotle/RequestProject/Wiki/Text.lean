import Mathlib

/-!
# Wikitext: an abstract syntax for wiki pages, with a parser and a printer

This file is the *page* layer of the library.  Everything the project has done so
far lives inside Lean: items, statements, diagnostics, reports.  A Wikidata
WikiProject page, on the other hand, is a piece of **wikitext**: prose interleaved
with *template calls* such as `{{Q|Q5}}`, and — inside a template's own source —
*parameter references* such as `{{{1}}}` or `{{{label|(none)}}}`.

The syntax modelled here is the fragment that WikiProject pages actually use:

```
page      ::= (text | template | parameter)*
template  ::= "{{" name ("|" arg)* "}}"
arg       ::= value | key "=" value
parameter ::= "{{{" key ("|" default)? "}}}"
```

Argument values are kept as **raw wikitext strings** rather than as nested trees.
The parser is brace-aware (`Wikidata.Wiki.scanChunk` keeps a stack of the open
groups, so a run of braces closes the group it really belongs to), so
a nested call such as `{{tl|{{Q|Q5}}}}` is read as a single argument whose value is
the string `{{Q|Q5}}`; nesting is recovered simply by parsing that string again.
This keeps the abstract syntax first-order — and therefore `DecidableEq`, `Repr`
and usable in `decide` — without losing any content.

Two facts are proved about the printer/parser pair.

* **Faithfulness** (`Wikidata.Wiki.render_parsePage`): whatever the parser accepts,
  it accepts *exactly*; printing the result gives back the original source
  character for character.  Importing a page therefore never invents and never
  drops content.
* **Round trip** (`Wikidata.Wiki.parsePage_render`): a *clean* page — one passing
  the `Wikidata.Wiki.pageCleanB` hygiene check — prints to wikitext that parses
  back to the very same page.

`RequestProject.Wiki.Template` builds templates on top of this, and
`RequestProject.Wiki.Syntax` provides the `wiki!` / `template!` macros.
-/

namespace Wikidata
namespace Wiki

/-! ## Abstract syntax -/

/-- One argument of a template call: an optional key (`key=value`) and the raw
wikitext of the value. -/
structure Arg where
  /-- `some k` for a named argument `k=v`, `none` for a positional one. -/
  key : Option String
  /-- The argument's value, as raw wikitext. -/
  value : String
  deriving DecidableEq, Repr, Inhabited

/-- A piece of wikitext: plain text, a template call, or a parameter reference. -/
inductive Node where
  /-- Plain text. -/
  | text (s : String)
  /-- A template call `{{name|arg|…}}`. -/
  | tmpl (name : String) (args : List Arg)
  /-- A parameter reference `{{{key}}}` or `{{{key|default}}}`, as used inside a
  template's source. -/
  | param (key : String) (dflt : Option String)
  deriving DecidableEq, Repr, Inhabited

/-- A page is a list of nodes. -/
abbrev Page := List Node

/-- A positional argument. -/
def Arg.pos (v : String) : Arg := ⟨none, v⟩

/-- A named argument. -/
def Arg.named (k v : String) : Arg := ⟨some k, v⟩

/-! ## Printing -/

/-- The characters of one argument. -/
def renderArgChars : Arg → List Char
  | ⟨none, v⟩ => '|' :: v.toList
  | ⟨some k, v⟩ => '|' :: (k.toList ++ '=' :: v.toList)

/-- The characters of a list of arguments. -/
def renderArgsChars : List Arg → List Char
  | [] => []
  | a :: as => renderArgChars a ++ renderArgsChars as

/-- The characters of one node. -/
def renderNode : Node → List Char
  | .text s => s.toList
  | .tmpl n args => '{' :: '{' :: (n.toList ++ renderArgsChars args ++ ['}', '}'])
  | .param k none => '{' :: '{' :: '{' :: (k.toList ++ ['}', '}', '}'])
  | .param k (some d) =>
      '{' :: '{' :: '{' :: (k.toList ++ '|' :: (d.toList ++ ['}', '}', '}']))

/-- The characters of a page. -/
def renderNodes : Page → List Char
  | [] => []
  | n :: ns => renderNode n ++ renderNodes ns

/-- The wikitext of a page. -/
def render (p : Page) : String := String.ofList (renderNodes p)

theorem renderNodes_append (p q : Page) :
    renderNodes (p ++ q) = renderNodes p ++ renderNodes q := by
  induction p with
  | nil => simp [renderNodes]
  | cons n ns ih => simp [renderNodes, ih, List.append_assoc]

/-! ## Scanners -/

/-- Reads a run of plain text: everything up to the next `{{`. -/
def scanText : List Char → List Char × List Char
  | [] => ([], [])
  | '{' :: '{' :: cs => ([], '{' :: '{' :: cs)
  | c :: cs => let r := scanText cs; (c :: r.1, r.2)

theorem scanText_append : ∀ cs : List Char, (scanText cs).1 ++ (scanText cs).2 = cs := by
  intro cs
  induction cs using scanText.induct with
  | case1 => simp [scanText]
  | case2 cs => simp [scanText]
  | case3 c cs _ ih => simp [scanText, ih]

theorem scanText_length : ∀ cs : List Char, (scanText cs).2.length ≤ cs.length := by
  intro cs
  induction cs using scanText.induct with
  | case1 => simp [scanText]
  | case2 cs => simp [scanText]
  | case3 c cs _ ih => simp only [scanText]; simp; omega

/-- Reads the raw wikitext of a template name, an argument or a parameter default:
everything up to the next `|` or `}}` that is not inside a nested group.  `stack`
records the groups currently open, innermost first: `2` for a template call `{{…}}`
and `3` for a parameter reference `{{{…}}}`, so a closing run of braces is matched
against the group it actually closes.  Returns the chunk and the rest of the input,
which begins with `|` or `}}`. -/
def scanChunk : List ℕ → List Char → Option (List Char × List Char)
  | _, [] => none
  | st, '{' :: '{' :: '{' :: cs =>
      (scanChunk (3 :: st) cs).map fun r => ('{' :: '{' :: '{' :: r.1, r.2)
  | st, '{' :: '{' :: cs => (scanChunk (2 :: st) cs).map fun r => ('{' :: '{' :: r.1, r.2)
  | 3 :: st, '}' :: '}' :: '}' :: cs =>
      (scanChunk st cs).map fun r => ('}' :: '}' :: '}' :: r.1, r.2)
  | [], '}' :: '}' :: cs => some ([], '}' :: '}' :: cs)
  | _ :: st, '}' :: '}' :: cs => (scanChunk st cs).map fun r => ('}' :: '}' :: r.1, r.2)
  | [], '|' :: cs => some ([], '|' :: cs)
  | st, '|' :: cs => (scanChunk st cs).map fun r => ('|' :: r.1, r.2)
  | st, c :: cs => (scanChunk st cs).map fun r => (c :: r.1, r.2)

theorem scanChunk_append : ∀ {st : List ℕ} {cs a r : List Char},
    scanChunk st cs = some (a, r) → a ++ r = cs := by
  intro st cs
  induction st, cs using scanChunk.induct
  all_goals intro a r h
  all_goals simp only [scanChunk, Option.map_eq_some_iff] at h
  all_goals
    first
      | (obtain ⟨p, hp, hr⟩ := h
         cases hr
         rename_i ih
         simpa using ih hp)
      | (cases h; simp)
      | simp at h

theorem scanChunk_length {st : List ℕ} {cs a r : List Char}
    (h : scanChunk st cs = some (a, r)) : r.length ≤ cs.length := by
  have happ := scanChunk_append h
  have : a.length + r.length = cs.length := by rw [← happ]; simp
  omega

/-! ## Arguments -/

/-- Characters allowed in an argument key. -/
def keyishB (c : Char) : Bool :=
  c.isAlphanum || c == ' ' || c == '_' || c == '-'

/-- Reads a `key=` prefix of an argument chunk, if there is one. -/
def splitKey : List Char → Option (List Char × List Char)
  | [] => none
  | '=' :: cs => some ([], cs)
  | c :: cs => if keyishB c then (splitKey cs).map fun r => (c :: r.1, r.2) else none

/-- Turns a chunk of raw wikitext into an argument: `key=value` when the part
before the first `=` is a non-empty plain key, and a positional value otherwise. -/
def argOfChunk (cs : List Char) : Arg :=
  match splitKey cs with
  | some (k, v) =>
      if k.isEmpty then ⟨none, String.ofList cs⟩
      else ⟨some (String.ofList k), String.ofList v⟩
  | none => ⟨none, String.ofList cs⟩

/-! ## Parsing -/

/-- Parses the arguments of a template call together with its closing `}}`,
starting at the `|` of the first argument (or at the `}}`). -/
def parseArgsChars : List Char → Option (List Arg × List Char)
  | '}' :: '}' :: cs => some ([], cs)
  | '|' :: cs =>
      match h : scanChunk [] cs with
      | some (chunk, r) =>
          have : r.length < cs.length + 1 := by
            have := scanChunk_length h
            omega
          (parseArgsChars r).map fun p => (argOfChunk chunk :: p.1, p.2)
      | none => none
  | _ => none
termination_by cs => cs.length

private theorem parseArgsChars_length_aux : ∀ (n : ℕ) (cs : List Char), cs.length ≤ n →
    ∀ {args : List Arg} {r : List Char},
      parseArgsChars cs = some (args, r) → r.length < cs.length := by
  intro n
  induction n with
  | zero =>
      intro cs hcs args r h
      have : cs = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp [parseArgsChars] at h
  | succ n ih =>
      intro cs hcs args r h
      unfold parseArgsChars at h
      split at h
      · rename_i cs' _
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hr⟩ := h
        subst hr
        simp
      · rename_i cs' _
        split at h
        · rename_i chunk r' hsc
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hr⟩ := h
          have hlen := scanChunk_length hsc
          have h1 := ih r' (by simp only [List.length_cons] at hcs; omega) hp
          cases hr
          simp only [List.length_cons]
          omega
        · simp at h
      · simp at h

theorem parseArgsChars_length {cs : List Char} {args : List Arg} {r : List Char}
    (h : parseArgsChars cs = some (args, r)) : r.length < cs.length :=
  parseArgsChars_length_aux cs.length cs le_rfl h

/-- Parses a template call, starting just after the opening `{{`. -/
def parseTmplChars (cs : List Char) : Option (Node × List Char) :=
  match scanChunk [] cs with
  | some (nm, r) =>
      (parseArgsChars r).map fun p => (Node.tmpl (String.ofList nm) p.1, p.2)
  | none => none

theorem parseTmplChars_length {cs : List Char} {nd : Node} {r : List Char}
    (h : parseTmplChars cs = some (nd, r)) : r.length < cs.length + 1 := by
  unfold parseTmplChars at h
  split at h
  · rename_i nm r' hsc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, hr⟩ := h
    have h1 := parseArgsChars_length hp
    have h2 := scanChunk_length hsc
    cases hr
    omega
  · simp at h

/-- Parses a parameter reference, starting just after the opening `{{{`. -/
def parseParamChars (cs : List Char) : Option (Node × List Char) :=
  match scanChunk [] cs with
  | some (k, '}' :: '}' :: '}' :: r) => some (Node.param (String.ofList k) none, r)
  | some (k, '|' :: r) =>
      match scanChunk [] r with
      | some (d, '}' :: '}' :: '}' :: r₂) =>
          some (Node.param (String.ofList k) (some (String.ofList d)), r₂)
      | _ => none
  | _ => none

theorem parseParamChars_length {cs : List Char} {nd : Node} {r : List Char}
    (h : parseParamChars cs = some (nd, r)) : r.length < cs.length + 1 := by
  unfold parseParamChars at h
  split at h
  · rename_i k r' hsc
    have := scanChunk_length hsc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hr⟩ := h
    subst hr
    simp only [List.length_cons] at this
    omega
  · rename_i k r' hsc
    split at h
    · rename_i d r₂ hsc2
      have h1 := scanChunk_length hsc
      have h2 := scanChunk_length hsc2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hr⟩ := h
      subst hr
      simp only [List.length_cons] at h1 h2
      omega
    · simp at h
  · simp at h

/-- Parses a page: a sequence of text runs, template calls and parameter
references. -/
def parseNodesChars : List Char → Option Page
  | [] => some []
  | '{' :: '{' :: '{' :: cs =>
      match h : parseParamChars cs with
      | some (nd, r) =>
          have : r.length < cs.length + 3 := by
            have := parseParamChars_length h
            omega
          (parseNodesChars r).map (nd :: ·)
      | none => none
  | '{' :: '{' :: cs =>
      match h : parseTmplChars cs with
      | some (nd, r) =>
          have : r.length < cs.length + 2 := by
            have := parseTmplChars_length h
            omega
          (parseNodesChars r).map (nd :: ·)
      | none => none
  | c :: cs =>
      match hs : scanText (c :: cs) with
      | (x :: t, r) =>
          have : r.length < cs.length + 1 := by
            have h1 := scanText_append (c :: cs)
            rw [hs] at h1
            have h2 := congrArg List.length h1
            simp only [List.length_append, List.length_cons] at h2
            omega
          (parseNodesChars r).map (Node.text (String.ofList (x :: t)) :: ·)
      | ([], _) => none
termination_by cs => cs.length

/-- Parses a page of wikitext. -/
def parsePage (s : String) : Option Page := parseNodesChars s.toList


/-! ## Faithfulness of the parser

Whatever the parser accepts, it accepts exactly: printing the parsed page gives
back the source, character for character.  So importing a page neither invents nor
drops content.
-/

theorem splitKey_append : ∀ (cs : List Char) {k v : List Char},
    splitKey cs = some (k, v) → k ++ '=' :: v = cs := by
  intro cs
  induction cs with
  | nil => intro k v h; simp [splitKey] at h
  | cons c cs ih =>
      intro k v h
      by_cases hc : c = '='
      · subst hc
        simp only [splitKey, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · rw [splitKey.eq_3 c cs (fun hh => absurd hh hc)] at h
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hkv⟩ := h
          cases hkv
          simpa using ih hp
        · simp at h

theorem renderArgChars_argOfChunk (cs : List Char) :
    renderArgChars (argOfChunk cs) = '|' :: cs := by
  unfold argOfChunk
  split
  · rename_i k v hk
    split
    · simp [renderArgChars]
    · have hkv := splitKey_append cs hk
      simp only [renderArgChars, String.toList_ofList]
      rw [hkv]
  · simp [renderArgChars]

private theorem parseArgsChars_sound_aux : ∀ (n : ℕ) (cs : List Char), cs.length ≤ n →
    ∀ {args : List Arg} {r : List Char},
      parseArgsChars cs = some (args, r) → renderArgsChars args ++ '}' :: '}' :: r = cs := by
  intro n
  induction n with
  | zero =>
      intro cs hcs args r h
      have : cs = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp [parseArgsChars] at h
  | succ n ih =>
      intro cs hcs args r h
      unfold parseArgsChars at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [renderArgsChars]
      · rename_i cs' _
        split at h
        · rename_i chunk r' hsc
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hr⟩ := h
          have hlen := scanChunk_length hsc
          have hih := ih r' (by simp only [List.length_cons] at hcs; omega) hp
          have hchunk := scanChunk_append hsc
          cases hr
          simp only [renderArgsChars]
          rw [List.append_assoc, hih, renderArgChars_argOfChunk, ← hchunk, List.cons_append]
        · simp at h
      · simp at h

/-- Printing the arguments read from a template call gives back the source. -/
theorem parseArgsChars_sound {cs : List Char} {args : List Arg} {r : List Char}
    (h : parseArgsChars cs = some (args, r)) :
    renderArgsChars args ++ '}' :: '}' :: r = cs :=
  parseArgsChars_sound_aux cs.length cs le_rfl h

/-- Printing a template call read from the source gives back the source. -/
theorem parseTmplChars_sound {cs : List Char} {nd : Node} {r : List Char}
    (h : parseTmplChars cs = some (nd, r)) : renderNode nd ++ r = '{' :: '{' :: cs := by
  unfold parseTmplChars at h
  split at h
  · rename_i nm r' hsc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, hr⟩ := h
    have h1 := parseArgsChars_sound hp
    have h2 := scanChunk_append hsc
    cases hr
    simp only [renderNode, String.toList_ofList, List.cons_append, List.append_assoc]
    rw [← h2, ← h1]
    simp
  · simp at h

/-- Printing a parameter reference read from the source gives back the source. -/
theorem parseParamChars_sound {cs : List Char} {nd : Node} {r : List Char}
    (h : parseParamChars cs = some (nd, r)) :
    renderNode nd ++ r = '{' :: '{' :: '{' :: cs := by
  unfold parseParamChars at h
  split at h
  · rename_i k r' hsc
    have h2 := scanChunk_append hsc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [renderNode, String.toList_ofList, List.cons_append, List.append_assoc]
    rw [← h2]
    simp
  · rename_i k r' hsc
    split at h
    · rename_i d r₂ hsc2
      have h1 := scanChunk_append hsc
      have h2 := scanChunk_append hsc2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [renderNode, String.toList_ofList, List.cons_append, List.append_assoc]
      rw [← h1, ← h2]
      simp
    · simp at h
  · simp at h

private theorem renderNodes_parseNodesChars_aux : ∀ (n : ℕ) (cs : List Char), cs.length ≤ n →
    ∀ {p : Page}, parseNodesChars cs = some p → renderNodes p = cs := by
  intro n
  induction n with
  | zero =>
      intro cs hcs p h
      have : cs = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp only [parseNodesChars, Option.some.injEq] at h
      cases h
      rfl
  | succ n ih =>
      intro cs hcs p h
      unfold parseNodesChars at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        rfl
      · rename_i cs' _
        split at h
        · rename_i nd r hpp
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨q, hq, rfl⟩ := h
          have hlen := parseParamChars_length hpp
          have h1 := ih r (by simp only [List.length_cons] at hcs; omega) hq
          have h2 := parseParamChars_sound hpp
          simp only [renderNodes]
          rw [h1, h2]
        · simp at h
      · rename_i cs' _
        split at h
        · rename_i nd r hpt
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨q, hq, rfl⟩ := h
          have hlen := parseTmplChars_length hpt
          have h1 := ih r (by simp only [List.length_cons] at hcs; omega) hq
          have h2 := parseTmplChars_sound hpt
          simp only [renderNodes]
          rw [h1, h2]
        · simp at h
      · rename_i c cs' _ _
        split at h
        · rename_i x t r hs
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨q, hq, rfl⟩ := h
          have happ := scanText_append (c :: cs')
          rw [hs] at happ
          have hlen : r.length ≤ n := by
            have := congrArg List.length happ
            simp only [List.length_append, List.length_cons] at this
            simp only [List.length_cons] at hcs
            omega
          have h1 := ih r hlen hq
          simp only [renderNodes, renderNode, String.toList_ofList]
          rw [h1]
          exact happ
        · simp at h

/-- **Faithfulness.**  If a string parses to a page, then printing that page
returns the string. -/
theorem renderNodes_parseNodesChars {cs : List Char} {p : Page}
    (h : parseNodesChars cs = some p) : renderNodes p = cs :=
  renderNodes_parseNodesChars_aux cs.length cs le_rfl h

/-- **Faithfulness**, for strings: importing a page of wikitext and printing it
again returns the original wikitext. -/
theorem render_parsePage {s : String} {p : Page} (h : parsePage s = some p) :
    render p = s := by
  have := renderNodes_parseNodesChars (cs := s.toList) (p := p) h
  simp [render, this]

end Wiki
end Wikidata
