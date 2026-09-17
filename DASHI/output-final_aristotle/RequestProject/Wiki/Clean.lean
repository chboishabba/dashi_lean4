/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Wiki.Text

/-!
# Clean wikitext, and the printer/parser round trip

`RequestProject.Wiki.Text` proves that the parser is *faithful*: everything it
accepts it prints back unchanged.  This file proves the other direction, which is
what a page **generator** needs: a page built inside Lean prints to wikitext that
reads back as the very same page — no template call can silently change shape, and
no text can silently swallow the markup around it.

That is not true of arbitrary pages: `[text "a", text "b"]` and `[text "ab"]` print
to the same string, and a text run containing `{{` would be re-read as a template
call.  `Wikidata.Wiki.pageCleanB` is the hygiene check that rules exactly those
accidents out:

* text runs are non-empty and contain no `{`, and no two of them are adjacent;
* template and parameter names are non-empty and contain no `{`, `}` or `|`;
* an argument value is *balanced*: outside complete nested groups `{{…}}` and
  `{{{…}}}` it contains no `{`, `}` or `|`, so the scanner stops exactly where the
  value ends; a positional value must also not start with a `key=` prefix (or it
  would be re-read as a named argument);
* the key of a named argument is a non-empty run of alphanumerics, spaces, `_`
  and `-`.

`Wikidata.Wiki.parsePage_render` is the round trip; `Wikidata.Wiki.render_injOn`
is the immediate consequence that printing clean pages is injective.
-/

namespace Wikidata
namespace Wiki

/-! ## The hygiene check -/

/-- A character that carries no wiki markup. -/
def plainCharB (c : Char) : Bool := c != '{' && c != '}' && c != '|'

/-- A string with no wiki markup characters. -/
def plainStrB (s : String) : Bool := s.toList.all plainCharB

/-- A text run: non-empty and with no `{`, so it can never grow into `{{`. -/
def textCleanB (s : String) : Bool := s != "" && s.toList.all (· != '{')

/-- A template or parameter name: non-empty and free of markup. -/
def nameCleanB (s : String) : Bool := s != "" && plainStrB s

/-- The key of a named argument. -/
def keyCleanB (k : String) : Bool := k != "" && k.toList.all keyishB

/-- `chunkCleanB st cs` mirrors `Wikidata.Wiki.scanChunk`: it says that scanning
`cs` with the groups `st` open consumes all of `cs` and closes every group, so that
whatever follows `cs` is seen with no group open.  Single `{`, `}` and `|`
characters are only allowed as part of a complete group. -/
def chunkCleanB : List ℕ → List Char → Bool
  | [], [] => true
  | _ :: _, [] => false
  | st, '{' :: '{' :: '{' :: cs => chunkCleanB (3 :: st) cs
  | st, '{' :: '{' :: cs => chunkCleanB (2 :: st) cs
  | [], '}' :: '}' :: _ => false
  | 3 :: st, '}' :: '}' :: '}' :: cs => chunkCleanB st cs
  | 3 :: _, '}' :: '}' :: _ => false
  | 2 :: st, '}' :: '}' :: cs => chunkCleanB st cs
  | _ :: _, '}' :: '}' :: _ => false
  | [], '|' :: _ => false
  | t :: st, '|' :: cs => chunkCleanB (t :: st) cs
  | st, c :: cs => plainCharB c && chunkCleanB st cs

/-- A hygienic argument value or parameter default: balanced wikitext with no
stray markup character and no `|` or `}}` outside a nested group. -/
def valueCleanB (s : String) : Bool := chunkCleanB [] s.toList

/-- A hygienic argument. -/
def argCleanB : Arg → Bool
  | ⟨none, v⟩ => valueCleanB v && (splitKey v.toList).isNone
  | ⟨some k, v⟩ => keyCleanB k && valueCleanB v

/-- A hygienic node. -/
def nodeCleanB : Node → Bool
  | .text s => textCleanB s
  | .tmpl n args => nameCleanB n && args.all argCleanB
  | .param k none => nameCleanB k
  | .param k (some d) => nameCleanB k && valueCleanB d

/-- A hygienic page: every node is hygienic, and no two text runs are adjacent
(two adjacent runs would print as one). -/
def pageCleanB : Page → Bool
  | [] => true
  | .text _ :: .text _ :: _ => false
  | n :: ns => nodeCleanB n && pageCleanB ns

theorem pageCleanB_cons {n : Node} {ns : Page} (h : pageCleanB (n :: ns) = true) :
    nodeCleanB n = true ∧ pageCleanB ns = true := by
  cases n with
  | text s =>
      cases ns with
      | nil => simpa [pageCleanB] using h
      | cons m ms => cases m <;> simp_all [pageCleanB]
  | tmpl nm args => simpa [pageCleanB] using h
  | param k d => simpa [pageCleanB] using h

theorem pageCleanB_text_cons {s : String} {ns : Page} (h : pageCleanB (.text s :: ns) = true) :
    ∀ t, ns.head? ≠ some (.text t) := by
  intro t ht
  cases ns with
  | nil => simp at ht
  | cons m ms =>
      simp only [List.head?_cons, Option.some.injEq] at ht
      subst ht
      simp [pageCleanB] at h

/-! ## Shapes of the remaining input -/

/-- The parser may resume at `rest` in text position: either the input is over, or
a template call starts. -/
def Opens (rest : List Char) : Prop := rest = [] ∨ ∃ r, rest = '{' :: '{' :: r

/-- The parser may resume at `rest` after an argument: another argument starts, or
the call is closed. -/
def ClosesArg (rest : List Char) : Prop :=
  (∃ r, rest = '|' :: r) ∨ (∃ r, rest = '}' :: '}' :: r)

/-! ## Character facts -/

theorem toList_ne_nil {s : String} (h : s ≠ "") : s.toList ≠ [] := by
  intro h0
  exact h (String.toList_inj.mp (by simpa using h0))

theorem plainCharB_ne {c : Char} (h : plainCharB c = true) :
    c ≠ '{' ∧ c ≠ '}' ∧ c ≠ '|' := by
  simp only [plainCharB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem keyishB_plain {c : Char} (h : keyishB c = true) : plainCharB c = true := by
  by_cases h1 : c = '{'
  · subst h1; simp [keyishB] at h
  · by_cases h2 : c = '}'
    · subst h2; simp [keyishB] at h
    · by_cases h3 : c = '|'
      · subst h3; simp [keyishB] at h
      · simp [plainCharB, h1, h2, h3]

theorem keyishB_ne_eq {c : Char} (h : keyishB c = true) : c ≠ '=' := by
  rintro rfl
  simp [keyishB] at h

/-! ## The scanners on clean input -/

theorem scanText_cons_other (c : Char) (cs : List Char) (h1 : c ≠ '{') :
    scanText (c :: cs) = (c :: (scanText cs).1, (scanText cs).2) :=
  scanText.eq_3 c cs (fun _ hc _ => absurd hc h1)

theorem scanChunk_open3 (st : List ℕ) (cs : List Char) :
    scanChunk st ('{' :: '{' :: '{' :: cs) =
      (scanChunk (3 :: st) cs).map fun r => ('{' :: '{' :: '{' :: r.1, r.2) := by
  simp [scanChunk]

theorem scanChunk_open2 (st : List ℕ) (c : Char) (cs : List Char) (h : c ≠ '{') :
    scanChunk st ('{' :: '{' :: c :: cs) =
      (scanChunk (2 :: st) (c :: cs)).map fun r => ('{' :: '{' :: r.1, r.2) :=
  scanChunk.eq_3 st (c :: cs) (fun _ hc => absurd (List.cons.inj hc).1 h)

theorem scanChunk_close3 (st : List ℕ) (cs : List Char) :
    scanChunk (3 :: st) ('}' :: '}' :: '}' :: cs) =
      (scanChunk st cs).map fun r => ('}' :: '}' :: '}' :: r.1, r.2) := by
  simp [scanChunk]

theorem scanChunk_close2 (t : ℕ) (st : List ℕ) (cs : List Char) (h : t ≠ 3) :
    scanChunk (t :: st) ('}' :: '}' :: cs) =
      (scanChunk st cs).map fun r => ('}' :: '}' :: r.1, r.2) :=
  scanChunk.eq_6 t st cs (fun _ ht _ => absurd ht h)

theorem scanChunk_bar (t : ℕ) (st : List ℕ) (cs : List Char) :
    scanChunk (t :: st) ('|' :: cs) =
      (scanChunk (t :: st) cs).map fun r => ('|' :: r.1, r.2) := by
  simp [scanChunk]

theorem scanChunk_cons_other (st : List ℕ) (c : Char) (cs : List Char)
    (h1 : c ≠ '{') (h2 : c ≠ '}') (h3 : c ≠ '|') :
    scanChunk st (c :: cs) = (scanChunk st cs).map fun r => (c :: r.1, r.2) :=
  scanChunk.eq_9 st c cs (fun _ hc _ => absurd hc h1) (fun _ hc _ => absurd hc h1)
    (fun hc => absurd hc h3) (fun _ _ _ hc _ => absurd hc h2) (fun _ _ hc _ => absurd hc h2)
    (fun _ _ _ _ hc _ => absurd hc h2) (fun _ hc => absurd hc h3)

theorem scanText_clean : ∀ (t rest : List Char), (∀ c ∈ t, c ≠ '{') → Opens rest →
    scanText (t ++ rest) = (t, rest) := by
  intro t
  induction t with
  | nil =>
      intro rest _ hr
      rcases hr with rfl | ⟨r, rfl⟩ <;> simp [scanText]
  | cons c t ih =>
      intro rest ht hr
      have hc : c ≠ '{' := ht c (by simp)
      simp only [List.cons_append, scanText_cons_other c _ hc,
        ih rest (fun x hx => ht x (by simp [hx])) hr]

theorem chunkCleanB_cons_other (st : List ℕ) (c : Char) (cs : List Char)
    (h1 : c ≠ '{') (h2 : c ≠ '}') (h3 : c ≠ '|') :
    chunkCleanB st (c :: cs) = (plainCharB c && chunkCleanB st cs) := by
  unfold chunkCleanB
  split <;> simp_all
  rw [chunkCleanB.eq_def]

/-- A run of plain characters may be prefixed to any chunk. -/
theorem chunkCleanB_plain_append : ∀ (pre : List Char) (st : List ℕ) (cs : List Char),
    (∀ c ∈ pre, plainCharB c = true) → chunkCleanB st (pre ++ cs) = chunkCleanB st cs := by
  intro pre
  induction pre with
  | nil => intro st cs _; simp
  | cons c pre ih =>
      intro st cs hpre
      obtain ⟨h1, h2, h3⟩ := plainCharB_ne (hpre c (by simp))
      rw [List.cons_append, chunkCleanB_cons_other st c _ h1 h2 h3,
        ih st cs (fun x hx => hpre x (by simp [hx])), hpre c (by simp), Bool.true_and]

theorem chunkCleanB_of_plain {v : List Char} (h : ∀ c ∈ v, plainCharB c = true) :
    chunkCleanB [] v = true := by
  have := chunkCleanB_plain_append v [] [] h
  simpa [chunkCleanB] using this

/-- **The scanner reads back a clean chunk exactly.** -/
theorem scanChunk_clean : ∀ (st : List ℕ) (v : List Char), chunkCleanB st v = true →
    ∀ rest, ClosesArg rest → scanChunk st (v ++ rest) = some (v, rest) := by
  intro st v
  induction st, v using chunkCleanB.induct with
  | case1 =>
      intro _ rest hr
      rcases hr with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp [scanChunk]
  | case2 t st => intro hv; simp [chunkCleanB] at hv
  | case3 st cs ih =>
      intro hv rest hr
      simp only [chunkCleanB] at hv
      simp only [List.cons_append, scanChunk_open3, ih hv rest hr, Option.map_some]
  | case4 st cs hc ih =>
      intro hv rest hr
      simp only [chunkCleanB] at hv
      match cs, hc with
      | [], _ => simp [chunkCleanB] at hv
      | c :: cs', hc =>
          have hne : c ≠ '{' := fun h => hc cs' (by simp [h])
          have h2 := ih hv rest hr
          simp only [List.cons_append] at h2 ⊢
          rw [scanChunk_open2 st c _ hne, h2]
          simp
  | case5 tail => intro hv; simp [chunkCleanB] at hv
  | case6 st cs ih =>
      intro hv rest hr
      simp only [chunkCleanB] at hv
      simp only [List.cons_append, scanChunk_close3, ih hv rest hr, Option.map_some]
  | case7 tail tail1 h => intro hv; simp [chunkCleanB] at hv
  | case8 st cs ih =>
      intro hv rest hr
      simp only [chunkCleanB] at hv
      simp only [List.cons_append, scanChunk_close2 2 st _ (by decide), ih hv rest hr,
        Option.map_some]
  | case9 head tail tail1 _ _ _ => intro hv; simp [chunkCleanB] at hv
  | case10 tail => intro hv; simp [chunkCleanB] at hv
  | case11 t st cs ih =>
      intro hv rest hr
      simp only [chunkCleanB] at hv
      simp only [List.cons_append, scanChunk_bar, ih hv rest hr, Option.map_some]
  | case12 st c cs h1 h2 h3 h4 h5 h6 h7 h8 h9 ih =>
      intro hv rest hr
      simp only [chunkCleanB, Bool.and_eq_true] at hv
      obtain ⟨e1, e2, e3⟩ := plainCharB_ne hv.1
      simp only [List.cons_append, scanChunk_cons_other st c _ e1 e2 e3, ih hv.2 rest hr,
        Option.map_some]

/-! ## Arguments on clean input -/

theorem splitKey_none_of_no_eq : ∀ (v : List Char), (∀ c ∈ v, c ≠ '=') → splitKey v = none := by
  intro v
  induction v with
  | nil => intro _; rfl
  | cons c v ih =>
      intro hv
      rw [splitKey.eq_3 c v (fun hc => absurd hc (hv c (by simp)))]
      split
      · simp [ih (fun x hx => hv x (by simp [hx]))]
      · rfl

theorem splitKey_named : ∀ (k : List Char) (v : List Char), (∀ c ∈ k, keyishB c = true) →
    splitKey (k ++ '=' :: v) = some (k, v) := by
  intro k
  induction k with
  | nil => intro v _; simp [splitKey]
  | cons c k ih =>
      intro v hk
      have hc : keyishB c = true := hk c (by simp)
      have hne : c ≠ '=' := keyishB_ne_eq hc
      rw [List.cons_append, splitKey.eq_3 c _ (fun hh => absurd hh hne)]
      simp [hc, ih v (fun x hx => hk x (by simp [hx]))]

/-- The raw chunk of an argument: what stands between the `|` and the next `|`
or `}}`. -/
def argChunk : Arg → List Char
  | ⟨none, v⟩ => v.toList
  | ⟨some k, v⟩ => k.toList ++ '=' :: v.toList

theorem renderArgChars_eq (a : Arg) : renderArgChars a = '|' :: argChunk a := by
  cases a with
  | mk key value => cases key <;> simp [renderArgChars, argChunk]

theorem argChunk_clean {a : Arg} (h : argCleanB a = true) :
    chunkCleanB [] (argChunk a) = true := by
  cases a with
  | mk key value =>
      cases key with
      | none =>
          simp only [argCleanB, Bool.and_eq_true] at h
          simpa [argChunk, valueCleanB] using h.1
      | some k =>
          simp only [argCleanB, keyCleanB, Bool.and_eq_true, List.all_eq_true] at h
          have hpre : ∀ c ∈ k.toList ++ ['='], plainCharB c = true := by
            intro c hc
            simp only [List.mem_append, List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact keyishB_plain (h.1.2 c hc)
            · simp [plainCharB]
          have := chunkCleanB_plain_append (k.toList ++ ['=']) [] value.toList hpre
          simpa [argChunk, valueCleanB] using this.trans h.2

theorem argOfChunk_argChunk {a : Arg} (h : argCleanB a = true) : argOfChunk (argChunk a) = a := by
  cases a with
  | mk key value =>
      cases key with
      | none =>
          simp only [argCleanB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
          simp only [argChunk, argOfChunk, h.2, String.ofList_toList]
      | some k =>
          simp only [argCleanB, keyCleanB, Bool.and_eq_true, List.all_eq_true] at h
          have hk : splitKey (k.toList ++ '=' :: value.toList) = some (k.toList, value.toList) :=
            splitKey_named _ _ (fun c hc => h.1.2 c hc)
          have hne : ¬ k.toList.isEmpty = true := by
            have h1 := h.1.1
            simp only [bne_iff_ne, ne_eq] at h1
            simpa [List.isEmpty_iff] using toList_ne_nil h1
          simp only [argChunk, argOfChunk, hk, hne, Bool.false_eq_true, if_false,
            String.ofList_toList]

theorem closesArg_renderArgsChars (args : List Arg) (X : List Char) :
    ClosesArg (renderArgsChars args ++ '}' :: '}' :: X) := by
  cases args with
  | nil => exact Or.inr ⟨X, by simp [renderArgsChars]⟩
  | cons a as =>
      refine Or.inl ⟨argChunk a ++ (renderArgsChars as ++ '}' :: '}' :: X), ?_⟩
      simp [renderArgsChars, renderArgChars_eq]

theorem parseArgsChars_clean : ∀ (args : List Arg) (X : List Char),
    args.all argCleanB = true →
    parseArgsChars (renderArgsChars args ++ '}' :: '}' :: X) = some (args, X) := by
  intro args
  induction args with
  | nil => intro X _; simp [renderArgsChars, parseArgsChars]
  | cons a as ih =>
      intro X hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hsc : scanChunk [] (argChunk a ++ (renderArgsChars as ++ '}' :: '}' :: X)) =
          some (argChunk a, renderArgsChars as ++ '}' :: '}' :: X) :=
        scanChunk_clean _ _ (argChunk_clean hall.1) _ (closesArg_renderArgsChars as X)
      have hgoal : renderArgsChars (a :: as) ++ '}' :: '}' :: X =
          '|' :: (argChunk a ++ (renderArgsChars as ++ '}' :: '}' :: X)) := by
        simp [renderArgsChars, renderArgChars_eq]
      rw [hgoal, parseArgsChars]
      split
      · rename_i chunk r hsc'
        rw [hsc] at hsc'
        simp only [Option.some.injEq, Prod.mk.injEq] at hsc'
        obtain ⟨rfl, rfl⟩ := hsc'
        rw [ih X hall.2, argOfChunk_argChunk hall.1]
        simp
      · rename_i hnone
        rw [hsc] at hnone
        simp at hnone

/-! ## Nodes on clean input -/

theorem parseTmplChars_clean {nm : String} {args : List Arg} (X : List Char)
    (hn : nameCleanB nm = true) (ha : args.all argCleanB = true) :
    parseTmplChars (nm.toList ++ (renderArgsChars args ++ '}' :: '}' :: X)) =
      some (.tmpl nm args, X) := by
  have hplain : ∀ c ∈ nm.toList, plainCharB c = true := by
    simp only [nameCleanB, plainStrB, Bool.and_eq_true, List.all_eq_true] at hn
    exact fun c hc => hn.2 c hc
  have hsc := scanChunk_clean [] nm.toList (chunkCleanB_of_plain hplain)
    (renderArgsChars args ++ '}' :: '}' :: X) (closesArg_renderArgsChars args X)
  unfold parseTmplChars
  rw [hsc]
  dsimp only
  rw [parseArgsChars_clean args X ha]
  simp

theorem parseParamChars_clean_none {k : String} (X : List Char) (hk : nameCleanB k = true) :
    parseParamChars (k.toList ++ '}' :: '}' :: '}' :: X) = some (.param k none, X) := by
  have hplain : ∀ c ∈ k.toList, plainCharB c = true := by
    simp only [nameCleanB, plainStrB, Bool.and_eq_true, List.all_eq_true] at hk
    exact fun c hc => hk.2 c hc
  have hsc : scanChunk [] (k.toList ++ '}' :: '}' :: '}' :: X) =
      some (k.toList, '}' :: '}' :: '}' :: X) :=
    scanChunk_clean _ _ (chunkCleanB_of_plain hplain) _ (Or.inr ⟨'}' :: X, rfl⟩)
  unfold parseParamChars
  rw [hsc]
  simp

theorem parseParamChars_clean_some {k d : String} (X : List Char) (hk : nameCleanB k = true)
    (hd : valueCleanB d = true) :
    parseParamChars (k.toList ++ '|' :: (d.toList ++ '}' :: '}' :: '}' :: X)) =
      some (.param k (some d), X) := by
  have hkplain : ∀ c ∈ k.toList, plainCharB c = true := by
    simp only [nameCleanB, plainStrB, Bool.and_eq_true, List.all_eq_true] at hk
    exact fun c hc => hk.2 c hc
  have hsc1 : scanChunk [] (k.toList ++ '|' :: (d.toList ++ '}' :: '}' :: '}' :: X)) =
      some (k.toList, '|' :: (d.toList ++ '}' :: '}' :: '}' :: X)) :=
    scanChunk_clean _ _ (chunkCleanB_of_plain hkplain) _ (Or.inl ⟨_, rfl⟩)
  have hsc2 : scanChunk [] (d.toList ++ '}' :: '}' :: '}' :: X) =
      some (d.toList, '}' :: '}' :: '}' :: X) :=
    scanChunk_clean _ _ hd _ (Or.inr ⟨'}' :: X, rfl⟩)
  unfold parseParamChars
  rw [hsc1]
  simp only
  rw [hsc2]
  simp

/-! ## Reductions of the page parser -/

theorem parseNodesChars_text_cons {x : Char} {cs : List Char} (hx : x ≠ '{') :
    parseNodesChars (x :: cs) =
      (match scanText (x :: cs) with
       | (y :: t, r) => (parseNodesChars r).map (Node.text (String.ofList (y :: t)) :: ·)
       | ([], _) => none) := by
  rw [parseNodesChars]
  split
  all_goals simp_all

theorem parseNodesChars_tmpl_cons {x : Char} {cs : List Char} (hx : x ≠ '{') :
    parseNodesChars ('{' :: '{' :: x :: cs) =
      (match parseTmplChars (x :: cs) with
       | some (nd, r) => (parseNodesChars r).map (nd :: ·)
       | none => none) := by
  rw [parseNodesChars]
  split
  all_goals simp_all

theorem parseNodesChars_param_cons {cs : List Char} :
    parseNodesChars ('{' :: '{' :: '{' :: cs) =
      (match parseParamChars cs with
       | some (nd, r) => (parseNodesChars r).map (nd :: ·)
       | none => none) := by
  rw [parseNodesChars]
  split
  all_goals simp_all

/-! ## The round trip -/

theorem opens_renderNodes {ns : Page} (h : ∀ t, ns.head? ≠ some (.text t)) (X : List Char)
    (hX : Opens X) : Opens (renderNodes ns ++ X) := by
  cases ns with
  | nil => simpa [renderNodes] using hX
  | cons m ms =>
      cases m with
      | text s => exact absurd rfl (h s)
      | tmpl n args =>
          exact Or.inr ⟨n.toList ++ renderArgsChars args ++ ['}', '}'] ++ (renderNodes ms ++ X), by
            simp [renderNodes, renderNode]⟩
      | param k d =>
          cases d with
          | none =>
              exact Or.inr ⟨'{' :: (k.toList ++ ['}', '}', '}']) ++ (renderNodes ms ++ X), by
                simp [renderNodes, renderNode]⟩
          | some dv =>
              exact Or.inr ⟨'{' :: (k.toList ++ '|' :: (dv.toList ++ ['}', '}', '}'])) ++
                  (renderNodes ms ++ X), by simp [renderNodes, renderNode]⟩

/-- **Round trip.**  Printing a clean page and parsing the result gives the page
back, whatever hygienic continuation follows. -/
theorem parseNodesChars_renderNodes : ∀ (p : Page) (X : List Char), pageCleanB p = true →
    Opens X → parseNodesChars (renderNodes p ++ X) = (parseNodesChars X).map (p ++ ·) := by
  intro p
  induction p with
  | nil => intro X _ _; simp [renderNodes]
  | cons n ns ih =>
      intro X hp hX
      obtain ⟨hn, hns⟩ := pageCleanB_cons hp
      cases n with
      | text s =>
          have hhead := pageCleanB_text_cons hp
          have hopen := opens_renderNodes hhead X hX
          simp only [nodeCleanB, textCleanB, Bool.and_eq_true, bne_iff_ne, ne_eq,
            List.all_eq_true] at hn
          have hne : s.toList ≠ [] := toList_ne_nil hn.1
          have hnobrace : ∀ c ∈ s.toList, c ≠ '{' := by
            intro c hc
            simpa using hn.2 c hc
          obtain ⟨x, t, hxt⟩ : ∃ x t, s.toList = x :: t := by
            cases hs : s.toList with
            | nil => exact absurd hs hne
            | cons x t => exact ⟨x, t, rfl⟩
          have hx : x ≠ '{' := hnobrace x (by simp [hxt])
          have hshape : renderNodes (.text s :: ns) ++ X = x :: (t ++ (renderNodes ns ++ X)) := by
            simp [renderNodes, renderNode, hxt]
          have hscan : scanText (x :: (t ++ (renderNodes ns ++ X))) =
              (x :: t, renderNodes ns ++ X) := by
            have := scanText_clean s.toList (renderNodes ns ++ X) hnobrace hopen
            rwa [hxt, List.cons_append] at this
          rw [hshape, parseNodesChars_text_cons hx, hscan]
          dsimp only
          rw [ih X hns hX]
          have hs : String.ofList (x :: t) = s := by rw [← hxt, String.ofList_toList]
          simp [hs, Function.comp_def]
      | tmpl nm args =>
          simp only [nodeCleanB, Bool.and_eq_true] at hn
          have hplain : ∀ c ∈ nm.toList, plainCharB c = true := by
            have h1 := hn.1
            simp only [nameCleanB, plainStrB, Bool.and_eq_true, List.all_eq_true] at h1
            exact fun c hc => h1.2 c hc
          have hne : nm.toList ≠ [] := by
            have h1 := hn.1
            simp only [nameCleanB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
            exact toList_ne_nil h1.1
          obtain ⟨x, t, hxt⟩ : ∃ x t, nm.toList = x :: t := by
            cases hs : nm.toList with
            | nil => exact absurd hs hne
            | cons x t => exact ⟨x, t, rfl⟩
          have hx : x ≠ '{' := (plainCharB_ne (hplain x (by simp [hxt]))).1
          have hshape : renderNodes (.tmpl nm args :: ns) ++ X =
              '{' :: '{' :: (x :: (t ++ (renderArgsChars args ++
                '}' :: '}' :: (renderNodes ns ++ X)))) := by
            simp [renderNodes, renderNode, hxt]
          have hptmpl : parseTmplChars (x :: (t ++ (renderArgsChars args ++
              '}' :: '}' :: (renderNodes ns ++ X)))) = some (.tmpl nm args, renderNodes ns ++ X) := by
            have := parseTmplChars_clean (nm := nm) (args := args) (renderNodes ns ++ X) hn.1 hn.2
            rwa [hxt, List.cons_append] at this
          rw [hshape, parseNodesChars_tmpl_cons hx, hptmpl]
          dsimp only
          rw [ih X hns hX]
          simp [Function.comp_def]
      | param k d =>
          cases d with
          | none =>
              simp only [nodeCleanB] at hn
              have hshape : renderNodes (.param k none :: ns) ++ X =
                  '{' :: '{' :: '{' :: (k.toList ++ '}' :: '}' :: '}' :: (renderNodes ns ++ X)) := by
                simp [renderNodes, renderNode]
              rw [hshape, parseNodesChars_param_cons,
                parseParamChars_clean_none (k := k) (renderNodes ns ++ X) hn]
              dsimp only
              rw [ih X hns hX]
              simp [Function.comp_def]
          | some dv =>
              simp only [nodeCleanB, Bool.and_eq_true] at hn
              have hshape : renderNodes (.param k (some dv) :: ns) ++ X =
                  '{' :: '{' :: '{' :: (k.toList ++ '|' :: (dv.toList ++
                    '}' :: '}' :: '}' :: (renderNodes ns ++ X))) := by
                simp [renderNodes, renderNode]
              rw [hshape, parseNodesChars_param_cons,
                parseParamChars_clean_some (k := k) (d := dv) (renderNodes ns ++ X) hn.1 hn.2]
              dsimp only
              rw [ih X hns hX]
              simp [Function.comp_def]

/-- **Round trip**, for strings: a clean page prints to wikitext that parses back
to the same page. -/
theorem parsePage_render {p : Page} (h : pageCleanB p = true) : parsePage (render p) = some p := by
  have := parseNodesChars_renderNodes p [] h (Or.inl rfl)
  simp only [List.append_nil] at this
  simp [parsePage, render, this, parseNodesChars]

/-- Printing is injective on clean pages. -/
theorem render_injOn {p q : Page} (hp : pageCleanB p = true) (hq : pageCleanB q = true)
    (h : render p = render q) : p = q := by
  have h1 := parsePage_render hp
  have h2 := parsePage_render hq
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

end Wiki
end Wikidata
