import RequestProject.Publish
import RequestProject.Reports
import RequestProject.Cli.Query

/-!
# The single page report: what the browser reads is what was published

`wikidata onepage` writes **one** HTML file that carries its data, its query engine
and its charts inside itself, so it can be opened from a file or dropped on any
static host.  This file is the model of that page: the *payload* it embeds, the way
it is embedded, and the charts it draws.

The page keeps each ontology in its own inert `<script>` element, verbatim in the
JSON Lines format `wikidata publish` already uses.  Three things are proved about
that arrangement.

* **The embedding is faithful.**  `Wikidata.OnePage.blockPayload_dataBlock` says the
  text a browser reads back out of a data block is exactly the text that was put in,
  and `Wikidata.OnePage.parseJsonl?_blockPayload_dataBlock` composes this with the
  publication round trip: reading the block of a *web safe* knowledge base returns
  that knowledge base, on the nose.  `Wikidata.OnePage.parseDocs?_docs` is the same
  statement for the whole corpus at once.
* **The embedding cannot escape.**  `Wikidata.OnePage.lt_notMem_sanitize` — nothing
  the payload contains can close the script element or open a tag, because no `<`
  survives sanitising; and `Wikidata.OnePage.sanitize_eq_self` says sanitising is the
  identity on the data actually published, so the guarantee costs nothing.
* **The charts count what they claim.**  `Wikidata.OnePage.corpusBars_length` (one bar
  per ontology), `Wikidata.OnePage.corpusBars_count_sum` (the bars add up to the size
  of the corpus), `Wikidata.OnePage.kbBars_length` and
  `Wikidata.OnePage.kbBars_count_sum`.

Finally, the page ships *golden* answers: a handful of queries evaluated by the
certified evaluator when the page is generated, which the browser re-evaluates on
load and compares.  `Wikidata.OnePage.mem_probe_iff` pins down what those answers
mean: for a one-variable query, an item is an answer exactly when the query holds of
it in the abstract ontology of `RequestProject.Core`.
-/

namespace Wikidata
namespace OnePage

open Wikidata.Cli Wikidata.Publish

/-! ## Embedding text inside the page -/

/-- The one character that can end an inert `<script>` block or start a tag. -/
def lt : Char := '<'

/-- A string is *script safe* when it contains no `<`, hence cannot close the
element it is embedded in nor open a new one. -/
def scriptSafeB (s : String) : Bool := !s.toList.contains lt

/-- Makes a string script safe, by blanking every `<`. -/
def sanitize (s : String) : String :=
  String.ofList (s.toList.map fun c => if c = lt then ' ' else c)

/-- A list is unchanged by a map that fixes each of its entries. -/
theorem map_eq_self_of_mem {α : Type*} {l : List α} {f : α → α} (h : ∀ x ∈ l, f x = x) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem lt_notMem_sanitize (s : String) : lt ∉ (sanitize s).toList := by
  simp only [sanitize, String.toList_ofList, List.mem_map, not_exists]
  rintro c ⟨-, hc⟩
  by_cases h : c = lt
  · simp [h] at hc
    exact absurd hc.symm (by decide)
  · simp [h] at hc

/-- **Sanitising makes the payload inert.** -/
theorem scriptSafeB_sanitize (s : String) : scriptSafeB (sanitize s) = true := by
  simpa [scriptSafeB] using lt_notMem_sanitize s

/-- **Sanitising costs nothing** on data that is already script safe. -/
theorem sanitize_eq_self {s : String} (h : scriptSafeB s = true) : sanitize s = s := by
  have h' : lt ∉ s.toList := by
    simpa [scriptSafeB] using h
  have : s.toList.map (fun c => if c = lt then ' ' else c) = s.toList := by
    refine map_eq_self_of_mem ?_
    intro c hc
    have : c ≠ lt := by rintro rfl; exact h' hc
    simp [this]
  simp [sanitize, this]

/-! ## A data block of the page -/

/-- The opening tag of the inert element carrying one ontology. -/
def blockOpen (name : String) : String :=
  "<script type=\"application/x-wdkb-jsonl\" data-name=\"" ++ Report.htmlEscape name ++ "\">\n"

/-- The closing tag of a data block. -/
def blockClose : String := "\n</script>\n"

/-- One ontology, embedded in the page as JSON Lines inside an inert element. -/
def dataBlock (name : String) (doc : String) : String :=
  blockOpen name ++ sanitize doc ++ blockClose

/-- The text a reader takes back out of a data block: everything between the tags. -/
def blockPayload (name : String) (s : String) : String :=
  String.ofList
    (((s.toList.drop (blockOpen name).toList.length).reverse.drop
      blockClose.toList.length).reverse)

/-- **What the page gives back is what was put in.** -/
theorem blockPayload_dataBlock (name doc : String) :
    blockPayload name (dataBlock name doc) = sanitize doc := by
  have hlist : (dataBlock name doc).toList =
      (blockOpen name).toList ++ ((sanitize doc).toList ++ blockClose.toList) := by
    simp [dataBlock, String.toList_append, List.append_assoc]
  rw [blockPayload, hlist, List.drop_left, List.reverse_append,
    List.drop_left' (by simp), List.reverse_reverse]
  simp

/-! ## The corpus the page carries -/

/-- A knowledge base is *web safe* when every field of every published row is JSON
safe and free of `<`: then its JSON Lines can be embedded verbatim. -/
def webSafeKB (kb : KB) : Bool :=
  jsonSafeKB kb && (kbRecs kb).all (fun r => (renderRec r).all scriptSafeB)

theorem scriptSafe_fields {kb : KB} (h : webSafeKB kb = true) :
    ∀ r ∈ kbRecs kb, ∀ x ∈ renderRec r, lt ∉ x.toList := by
  simp only [webSafeKB, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr x hx
  simpa [scriptSafeB] using h.2 r hr x hx

theorem jsonSafeKB_of_webSafeKB {kb : KB} (h : webSafeKB kb = true) : jsonSafeKB kb = true := by
  simp only [webSafeKB, Bool.and_eq_true] at h
  exact h.1

/-- A character absent from every piece is absent from their join. -/
theorem notMem_joinChar {c sep : Char} {xs : List String} (hs : c ≠ sep)
    (h : ∀ x ∈ xs, c ∉ x.toList) : c ∉ (joinChar sep xs).toList := by
  simp only [joinChar, String.toList_ofList]
  refine mem_intercalate_singleton hs ?_
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact h x hx

/-- No `<` reaches a published row when no field carries one. -/
theorem lt_notMem_jsonRow {r : Rec} (h : ∀ x ∈ renderRec r, lt ∉ x.toList) :
    lt ∉ (jsonRow r).toList := by
  have hj : lt ∉ (joinChar comma ((renderRec r).map quote)).toList := by
    refine notMem_joinChar (by decide) ?_
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact notMem_quote (by decide) (h x hx)
  have harr : (jsonRow r).toList =
      '[' :: ((joinChar comma ((renderRec r).map quote)).toList ++ [']']) := by
    simp [jsonRow, jsonArray]
  simp only [harr, List.mem_cons, List.mem_append, not_or]
  exact ⟨by decide, hj, by decide⟩

/-- **A web safe base embeds verbatim**: its JSON Lines contain no `<`. -/
theorem scriptSafeB_jsonlOfKB {kb : KB} (h : webSafeKB kb = true) :
    scriptSafeB (jsonlOfKB kb) = true := by
  have : lt ∉ (jsonlOfKB kb).toList := by
    rw [jsonlOfKB]
    refine notMem_joinChar (by decide) ?_
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨r, hr, rfl⟩ := hl
    exact lt_notMem_jsonRow (scriptSafe_fields h r hr)
  simpa [scriptSafeB] using this

/-- **The page is a lossless carrier**: reading a data block of the page and parsing
it returns exactly the knowledge base the block was made from. -/
theorem parseJsonl?_blockPayload_dataBlock {kb : KB} (h : webSafeKB kb = true) (name : String) :
    parseJsonl? (blockPayload name (dataBlock name (jsonlOfKB kb))) = some kb := by
  rw [blockPayload_dataBlock, sanitize_eq_self (scriptSafeB_jsonlOfKB h)]
  exact parseJsonl?_jsonlOfKB kb (jsonSafeKB_of_webSafeKB h)

/-- The documents the page embeds: one per ontology. -/
def docs (kbs : List KB) : List String := kbs.map jsonlOfKB

/-- Reading the whole corpus back. -/
def parseDocs? (ss : List String) : Option (List KB) := ss.mapM parseJsonl?

/-- **The whole corpus round-trips.** -/
theorem parseDocs?_docs {kbs : List KB} (h : ∀ kb ∈ kbs, jsonSafeKB kb = true) :
    parseDocs? (docs kbs) = some kbs := by
  induction kbs with
  | nil => rfl
  | cons kb kbs ih =>
      have h1 := parseJsonl?_jsonlOfKB kb (h kb List.mem_cons_self)
      have h2 := ih fun k hk => h k (List.mem_cons_of_mem _ hk)
      simp only [docs, List.map_cons, parseDocs?, List.mapM_cons] at h2 ⊢
      simp [h1, h2]

/-- **The sanitised corpus round-trips too**, so the page's own safety measure loses
nothing. -/
theorem parseDocs?_sanitize_docs {kbs : List KB} (h : ∀ kb ∈ kbs, webSafeKB kb = true) :
    parseDocs? ((docs kbs).map sanitize) = some kbs := by
  have hs : (docs kbs).map sanitize = docs kbs := by
    refine map_eq_self_of_mem ?_
    intro d hd
    simp only [docs, List.mem_map] at hd
    obtain ⟨kb, hkb, rfl⟩ := hd
    exact sanitize_eq_self (scriptSafeB_jsonlOfKB (h kb hkb))
  rw [hs]
  exact parseDocs?_docs fun kb hkb => jsonSafeKB_of_webSafeKB (h kb hkb)

/-- **One document per ontology.** -/
theorem length_docs (kbs : List KB) : (docs kbs).length = kbs.length := by
  simp [docs]

/-! ## The charts the page draws -/

open Wikidata.Report

/-- The colour of the bars counting a corpus. -/
def corpusColour : String := "#2b5797"

/-- The bars of the corpus chart: one per ontology, counting its items. -/
def corpusBars (kbs : List KB) : List Bar :=
  kbs.map fun kb => { label := kb.name, count := kb.items.length, colour := corpusColour }

/-- **One bar per ontology.** -/
theorem corpusBars_length (kbs : List KB) : (corpusBars kbs).length = kbs.length := by
  simp [corpusBars]

/-- **The corpus chart counts every item exactly once.** -/
theorem corpusBars_count_sum (kbs : List KB) :
    ((corpusBars kbs).map Bar.count).sum = (kbs.map fun kb => kb.items.length).sum := by
  simp [corpusBars, Function.comp_def]

/-- The bars of the chart of a single ontology: its items and its three kinds of
statement. -/
def kbBars (kb : KB) : List Bar :=
  [{ label := "items", count := kb.items.length, colour := corpusColour },
   { label := "subclass of (P279)", count := kb.sub.length, colour := corpusColour },
   { label := "instance of (P31)", count := kb.inst.length, colour := corpusColour },
   { label := "disjoint", count := kb.disj.length, colour := corpusColour }]

/-- **Four bars: the items and the three kinds of statement.** -/
theorem kbBars_length (kb : KB) : (kbBars kb).length = 4 := rfl

/-- **The chart of one ontology accounts for all of its rows** — every published row
but the header is counted by exactly one bar (`Publish.length_kbRecs`). -/
theorem kbBars_count_sum (kb : KB) :
    ((kbBars kb).map Bar.count).sum + 1 + kb.levels.length = (kbRecs kb).length := by
  rw [length_kbRecs]
  simp [kbBars]
  omega

/-- **The bars are drawn, one line each** (`Report.svgBarLines_length`). -/
theorem corpusChart_lines (kbs : List KB) :
    (svgBarLines (corpusBars kbs)).length = kbs.length := by
  rw [svgBarLines_length, corpusBars_length]

/-! ## The golden answers -/

open Wikidata.Query

/-- A binding produced by the evaluator binds nothing the query does not mention. -/
def BindsWithin (ns : List String) (e e' : Env) : Prop :=
  ∀ m v, e'.lookup m = some v → e.lookup m = some v ∨ m ∈ ns

theorem extendVars_bindsWithin (kb : KB) (ns : List String) (e e' : Env)
    (h : e' ∈ extendVars kb ns e) : BindsWithin ns e e' := by
  induction ns generalizing e with
  | nil =>
      simp only [extendVars, List.mem_singleton] at h
      subst h
      intro m v hm
      exact Or.inl hm
  | cons n ns ih =>
      rw [extendVars] at h
      split at h
      · intro m v hm
        rcases ih e h m v hm with hv | hv
        · exact Or.inl hv
        · exact Or.inr (List.mem_cons_of_mem _ hv)
      · simp only [List.mem_flatMap] at h
        obtain ⟨q, -, hq⟩ := h
        intro m v hm
        rcases ih _ hq m v hm with hv | hv
        · by_cases hmn : m = n
          · exact Or.inr (by simp [hmn])
          · exact Or.inl (by rwa [lookup_cons_ne e n m q hmn] at hv)
        · exact Or.inr (List.mem_cons_of_mem _ hv)

theorem evalFrom_bindsWithin (kb : KB) : ∀ (q : BGP) (e e' : Env),
    e' ∈ evalFrom kb q e → BindsWithin (bgpVars q) e e'
  | [], e, e', h => by
      simp only [evalFrom, List.mem_singleton] at h
      subst h
      intro m v hm
      exact Or.inl hm
  | a :: as, e, e', h => by
      simp only [evalFrom, List.mem_flatMap] at h
      obtain ⟨e₁, he₁, he₂⟩ := h
      have h1 : BindsWithin a.vars e e₁ :=
        extendVars_bindsWithin kb a.vars e e₁ (List.mem_of_mem_filter he₁)
      have h2 : BindsWithin (bgpVars as) e₁ e' := evalFrom_bindsWithin kb as e₁ e' he₂
      have hb : bgpVars (a :: as) = a.vars ++ bgpVars as := by simp [bgpVars]
      intro m v hm
      rcases h2 m v hm with hv | hv
      · rcases h1 m v hv with hv' | hv'
        · exact Or.inl hv'
        · exact Or.inr (by rw [hb]; exact List.mem_append_left _ hv')
      · exact Or.inr (by rw [hb]; exact List.mem_append_right _ hv)

/-- **A one-variable query answers with exactly the items that satisfy it.**  The
golden answers the page ships are computed by this evaluator, so an item appears in
them exactly when the query holds of it in the abstract ontology. -/
theorem mem_probe_iff (kb : KB) (hv : kb.valid = true) (q : BGP) (n : String)
    (hvars : bgpVars q = [n]) (x : Qid) (hx : x ∈ kb.items) :
    (∃ e ∈ eval kb q, e.lookup n = some x) ↔ Sat kb hv (fun _ => x) q := by
  constructor
  · rintro ⟨e, he, hlk⟩
    refine eval_sat kb hv q he ?_
    intro m v hm
    have hb : BindsWithin (bgpVars q) [] e := evalFrom_bindsWithin kb q [] e he
    rcases hb m v hm with hv' | hv'
    · simp at hv'
    · rw [hvars] at hv'
      have hmn : m = n := by simpa using hv'
      subst hmn
      exact (Option.some_injective _ (hlk ▸ hm)).symm ▸ rfl
  · intro hsat
    have hitems : ∀ m ∈ bgpVars q, (fun _ : String => x) m ∈ kb.items := fun _ _ => hx
    obtain ⟨e, he, hag, hcov⟩ := (mem_eval_iff kb hv q (fun _ => x) hitems).2 hsat
    have hn : n ∈ bgpVars q := by simp [hvars]
    obtain ⟨v, hvv⟩ := Option.isSome_iff_exists.1 (hcov n hn)
    exact ⟨e, he, by rw [hvv]; exact congrArg some (hag n v hvv).symm⟩

/-- The answers the page ships for a query, projected onto the output variables;
by `Query.answersT_eq_answers` this is the certified evaluator of
`RequestProject.Queries`. -/
def probeAnswers (kb : KB) (q : BGP) (outs : List String) : List (List Qid) :=
  answersT kb q outs

theorem probeAnswers_eq (kb : KB) (q : BGP) (outs : List String) :
    probeAnswers kb q outs = answers kb q outs :=
  answersT_eq_answers kb q outs

end OnePage
end Wikidata
