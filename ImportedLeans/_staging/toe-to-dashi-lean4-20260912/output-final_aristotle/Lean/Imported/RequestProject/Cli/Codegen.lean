import RequestProject.Cli.Fetch
import RequestProject.Cli.Derive
import RequestProject.FastEval

/-!
# Compiling Wikidata facts to Lean

The `wikidata lean` command turns a knowledge base — typically one just downloaded
from the Wikidata API — into a self-contained Lean module: the statements as a
`Wikidata.KB` literal, the facts they entail as an explicit list, and theorems
tying the two together.

The generated module is *not* trusted: it is an ordinary Lean file that the
compiler re-checks.  What this file contributes is the mathematics the generated
module cites:

* `Cli.subFacts` / `Cli.instFacts` — the facts a knowledge base entails about its
  own items, as a list;
* `Cli.mem_subFacts` / `Cli.mem_instFacts` — exactly which pairs those lists
  contain;
* `Cli.subFacts_sound` / `Cli.instFacts_sound` — **every compiled fact really is a
  consequence of the downloaded statements**, in the abstract semantics of
  `RequestProject.Core` (reflexive–transitive closure of P279, resp. P31 followed
  by P279 steps);
* `Cli.subFacts_complete` / `Cli.instFacts_complete` — **and no consequence
  between declared items is left out**.

The rendering functions (`Cli.qidExpr`, `Cli.leanModule`, …) are plain string
manipulation; they carry no proof obligation, because the file they produce is
checked by Lean itself.
-/

namespace Wikidata
namespace Cli

/-! ### The facts that get compiled -/

/-- The derived `subclass of` facts of a knowledge base: all pairs of *distinct*
declared items `a`, `b` with `a ⊑ b`. -/
def subFacts (kb : KB) : List (Qid × Qid) :=
  let T := kb.closureTable
  kb.items.flatMap fun a =>
    (kb.superclassesOfLT T a).filterMap fun b => if a = b then none else some (a, b)

/-- The derived `instance of` facts of a knowledge base: all pairs of declared
items `a`, `c` with `a : c`. -/
def instFacts (kb : KB) : List (Qid × Qid) :=
  let T := kb.closureTable
  kb.items.flatMap fun a => (kb.classesOfT T a).map fun c => (a, c)

theorem mem_subFacts {kb : KB} {p : Qid × Qid} :
    p ∈ subFacts kb ↔
      p.1 ∈ kb.items ∧ p.2 ∈ kb.items ∧ p.1 ≠ p.2 ∧ kb.isSubclassOf p.1 p.2 = true := by
  obtain ⟨a, b⟩ := p
  simp only [subFacts, KB.superclassesOfLT_eq, List.mem_flatMap, List.mem_filterMap,
    KB.superclassesOfL, List.mem_filter]
  constructor
  · rintro ⟨x, hx, y, ⟨hy, hxy⟩, hif⟩
    by_cases h : x = y
    · rw [if_pos h] at hif; exact absurd hif (by simp)
    · rw [if_neg h] at hif
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hif).symm
      exact ⟨hx, hy, h, hxy⟩
  · rintro ⟨ha, hb, hab, hsub⟩
    exact ⟨a, ha, b, ⟨hb, hsub⟩, by rw [if_neg hab]⟩

theorem mem_instFacts {kb : KB} {p : Qid × Qid} :
    p ∈ instFacts kb ↔
      p.1 ∈ kb.items ∧ p.2 ∈ kb.items ∧ kb.isInstanceOf p.1 p.2 = true := by
  obtain ⟨a, c⟩ := p
  simp only [instFacts, KB.classesOfT_eq, List.mem_flatMap, List.mem_map, KB.classesOf,
    List.mem_filter]
  constructor
  · rintro ⟨x, hx, y, ⟨hy, hxy⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq.symm
    exact ⟨hx, hy, hxy⟩
  · rintro ⟨ha, hc, hinst⟩
    exact ⟨a, ha, c, ⟨hc, hinst⟩, rfl⟩

/-- **Every compiled `subclass of` fact really follows** from the downloaded
statements. -/
theorem subFacts_sound {kb : KB} (hwf : kb.wellFormed = true) {p : Qid × Qid}
    (h : p ∈ subFacts kb) : Relation.ReflTransGen kb.Sub p.1 p.2 :=
  (KB.isSubclassOf_iff hwf _ _).1 (mem_subFacts.1 h).2.2.2

/-- **No entailed `subclass of` fact between declared items is left out.** -/
theorem subFacts_complete {kb : KB} (hwf : kb.wellFormed = true) {a b : Qid}
    (ha : a ∈ kb.items) (hb : b ∈ kb.items) (hab : a ≠ b)
    (h : Relation.ReflTransGen kb.Sub a b) : (a, b) ∈ subFacts kb :=
  mem_subFacts.2 ⟨ha, hb, hab, (KB.isSubclassOf_iff hwf a b).2 h⟩

/-- **Every compiled `instance of` fact really follows** from the downloaded
statements: it is a P31 statement followed by a chain of P279 statements. -/
theorem instFacts_sound {kb : KB} (hwf : kb.wellFormed = true) {p : Qid × Qid}
    (h : p ∈ instFacts kb) : ∃ d, kb.Inst p.1 d ∧ Relation.ReflTransGen kb.Sub d p.2 :=
  (KB.isInstanceOf_iff hwf _ _).1 (mem_instFacts.1 h).2.2

/-- **No entailed `instance of` fact between declared items is left out.** -/
theorem instFacts_complete {kb : KB} (hwf : kb.wellFormed = true) {a c : Qid}
    (ha : a ∈ kb.items) (hc : c ∈ kb.items)
    (h : ∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d c) : (a, c) ∈ instFacts kb :=
  mem_instFacts.2 ⟨ha, hc, (KB.isInstanceOf_iff hwf a c).2 h⟩

/-! ### Rendering Lean source -/

/-- A Lean string literal. -/
def strLit (s : String) : String :=
  "\"" ++ String.ofList ((s.toList.map fun c =>
      if c = '"' || c = '\\' then ['\\', c]
      else if c = '\n' then ['\\', 'n']
      else if c = '\t' then ['\\', 't']
      else [c]).flatten) ++ "\""

/-- An item identifier, as a Lean expression. -/
def qidExpr : Qid → String
  | .wd id => "Qid.wd " ++ strLit id
  | .ont n => "Qid.ont " ++ strLit n
  | .about q => "Qid.about (" ++ qidExpr q ++ ")"
  | .lvl n => "Qid.lvl " ++ toString n

/-- An item identifier, as a fragment of a Lean identifier. -/
def qidIdent : Qid → String
  | .wd id => String.ofList (id.toList.map fun c => if c.isAlphanum then c else '_')
  | .ont n => "ont_" ++ String.ofList (n.toList.map fun c => if c.isAlphanum then c else '_')
  | .about q => "about_" ++ qidIdent q
  | .lvl n => "lvl_" ++ toString n

/-- A Lean list literal, one entry per line. -/
def listLit (entries : List String) : String :=
  if entries.isEmpty then "[]"
  else "[" ++ String.intercalate ",\n   " entries ++ "]"

/-- A pair of items, as a Lean expression. -/
def pairExpr (p : Qid × Qid) : String := "(" ++ qidExpr p.1 ++ ", " ++ qidExpr p.2 ++ ")"

/-- A `(item, level)` pair, as a Lean expression. -/
def levelExpr (p : Qid × ℕ) : String := "(" ++ qidExpr p.1 ++ ", " ++ toString p.2 ++ ")"

/-- The knowledge base itself, as a Lean definition. -/
def kbDef (kb : KB) : String :=
  "def kb : KB where\n" ++
  "  name := " ++ strLit kb.name ++ "\n" ++
  "  items := " ++ listLit (kb.items.map qidExpr) ++ "\n" ++
  "  levels := " ++ listLit (kb.levels.map levelExpr) ++ "\n" ++
  "  sub := " ++ listLit (kb.sub.map pairExpr) ++ "\n" ++
  "  inst := " ++ listLit (kb.inst.map pairExpr) ++ "\n" ++
  "  disj := " ++ listLit (kb.disj.map pairExpr) ++ "\n"

/-- The last component of a dotted module name. -/
def lastComponent (m : String) : String := ((m.splitOn ".").getLast?).getD m

/-- Text with any comment delimiter neutralised, so that it can be placed inside a
Lean comment. -/
def commentSafe (s : String) : String :=
  ((s.replace "/-" "/ -").replace "-/" "- /").replace "\n" " "

/-- The English label of an item, if the generator was given one. -/
def labelOf (labels : List (Qid × String)) (q : Qid) : String :=
  match labels.lookup q with
  | some l => if l.isEmpty then "" else l
  | none => ""

/-- An item with its label, for a comment: `Q5 (human)`. -/
def showLabelled (labels : List (Qid × String)) (q : Qid) : String :=
  let l := labelOf labels q
  let name := match q with | .wd id => id | _ => qidIdent q
  if l.isEmpty then name else name ++ " (" ++ commentSafe l ++ ")"

/-- The label table, as a comment listing the items of the fragment. -/
def labelTable (labels : List (Qid × String)) (items : List Qid) : String :=
  let rows := items.filterMap fun q =>
    let l := labelOf labels q
    if l.isEmpty then none else some ("  " ++ showLabelled labels q)
  if rows.isEmpty then ""
  else "/-! ### The items of this fragment\n\n" ++ String.intercalate "\n" rows ++ "\n-/\n"

/-- A named theorem for one derived `subclass of` fact, proved from the general
soundness theorem by looking the fact up in the compiled list. -/
def subHighlight (labels : List (Qid × String)) (p : Qid × Qid) : String :=
  "/-- " ++ showLabelled labels p.1 ++ " ⊑ " ++ showLabelled labels p.2 ++ " -/\n" ++
  "theorem sub_" ++ qidIdent p.1 ++ "_" ++ qidIdent p.2 ++
    " : Relation.ReflTransGen kb.Sub (" ++ qidExpr p.1 ++ ") (" ++ qidExpr p.2 ++ ") :=\n" ++
  "  derivedSub_sound " ++ pairExpr p ++ " (by decide)\n"

/-- A named theorem for one derived `instance of` fact. -/
def instHighlight (labels : List (Qid × String)) (p : Qid × Qid) : String :=
  "/-- " ++ showLabelled labels p.1 ++ " is an instance of " ++ showLabelled labels p.2 ++ " -/\n" ++
  "theorem inst_" ++ qidIdent p.1 ++ "_" ++ qidIdent p.2 ++
    " : ∃ d, kb.Inst (" ++ qidExpr p.1 ++ ") d ∧ Relation.ReflTransGen kb.Sub d (" ++
    qidExpr p.2 ++ ") :=\n" ++
  "  derivedInst_sound " ++ pairExpr p ++ " (by decide)\n"

/-- The whole generated module.

`decideTac` is the tactic used to evaluate the compiled lists (`decide` for a
fully kernel-checked module, `native_decide` for a large one).  `highlights` is
the number of individual named theorems to emit. -/
def leanModule (moduleName : String) (kb : KB) (decideTac : String)
    (highlights : ℕ) (provenance : String) (labels : List (Qid × String) := []) : String :=
  let ns := lastComponent moduleName
  let sub := subFacts kb
  let inst := instFacts kb
  let hlSub := (sub.take highlights).map (subHighlight labels)
  let hlInst := (inst.take highlights).map (instHighlight labels)
  let valid := kb.validFast
  String.intercalate "\n"
    [ "/-",
      "  " ++ moduleName,
      "",
      "  Machine-generated by `wikidata lean` from " ++ provenance ++ ".",
      "  Do not edit by hand: re-run the tool instead.",
      "",
      "  " ++ toString kb.items.length ++ " items, " ++ toString kb.sub.length ++
        " `subclass of` (P279) and " ++ toString kb.inst.length ++
        " `instance of` (P31) statements,",
      "  entailing " ++ toString (subFacts kb).length ++ " `subclass of` and " ++
        toString (instFacts kb).length ++ " `instance of` facts about these items.",
      "-/",
      "import RequestProject.Cli.Codegen",
      "",
      "set_option maxRecDepth 100000",
      "",
      "namespace Wikidata",
      "namespace Generated",
      "namespace " ++ ns,
      "",
      "open Wikidata Cli",
      "",
      labelTable labels kb.items,
      "/-- The downloaded statements. -/",
      kbDef kb,
      "/-! ### The verdict of the validator on this fragment -/",
      "",
      "/-- The statements only mention declared items, so the certified queries of",
      "`RequestProject.Engine` apply to this base. -/",
      "theorem kb_wellFormed : kb.wellFormed = true := by " ++ decideTac,
      "",
      "/-- Whether the fragment respects the metaclass level discipline",
      "(`level (class) = level (instance) + 1`, and `subclass of` between classes of",
      "the same positive level). -/",
      "theorem kb_levelsOk : kb.levelsOk = " ++ toString kb.levelsOk ++ " := by " ++ decideTac,
      "",
      "/-- Whether the `subclass of` hierarchy of the fragment is free of cycles. -/",
      "theorem kb_acyclic : kb.acyclic = " ++ toString kb.acyclicFast ++
        " := by rw [← KB.acyclicFast_eq]; " ++ decideTac,
      "",
      "/-- Whether declared disjoint classes share no instance. -/",
      "theorem kb_disjointOk : kb.disjointOk = " ++ toString kb.disjointOkFast ++
        " := by rw [← KB.disjointOkFast_eq]; " ++ decideTac,
      "",
      "/-- The verdict of the full validator on the downloaded fragment. -/",
      "theorem kb_valid : kb.valid = " ++ toString valid ++
        " := by rw [← KB.validFast_eq]; " ++ decideTac,
      "",
      if valid then
        "/-- Hence an abstract `Wikidata.Ontology`, to which every theorem of\n" ++
        "`RequestProject.Core` applies. -/\n" ++
        "def onto : Ontology Qid := kb.toOntology kb_valid\n"
      else
        "/-  This fragment does *not* pass the validator: the metaclass levels are\n" ++
        "    inferred, and live Wikidata data does not always fit a strict level\n" ++
        "    discipline.  The subclass and instance facts below do not depend on\n" ++
        "    levels, and are proved from the downloaded statements alone. -/\n",
      "/-- Every `subclass of` fact these statements entail about the items above. -/",
      "def derivedSub : List (Qid × Qid) :=\n  " ++ listLit (sub.map pairExpr),
      "",
      "theorem derivedSub_eq : subFacts kb = derivedSub := by " ++ decideTac,
      "",
      "/-- Each compiled fact is a chain of downloaded P279 statements. -/",
      "theorem derivedSub_sound : ∀ p ∈ derivedSub, Relation.ReflTransGen kb.Sub p.1 p.2 := by",
      "  rw [← derivedSub_eq]",
      "  exact fun _ hp => subFacts_sound kb_wellFormed hp",
      "",
      "/-- Conversely nothing is missing: any such chain between declared items is listed. -/",
      "theorem derivedSub_complete : ∀ a ∈ kb.items, ∀ b ∈ kb.items, a ≠ b →",
      "    Relation.ReflTransGen kb.Sub a b → (a, b) ∈ derivedSub := by",
      "  rw [← derivedSub_eq]",
      "  exact fun _ ha _ hb hab h => subFacts_complete kb_wellFormed ha hb hab h",
      "",
      "/-- Every `instance of` fact these statements entail about the items above. -/",
      "def derivedInst : List (Qid × Qid) :=\n  " ++ listLit (inst.map pairExpr),
      "",
      "theorem derivedInst_eq : instFacts kb = derivedInst := by " ++ decideTac,
      "",
      "/-- Each compiled fact is a downloaded P31 statement followed by downloaded",
      "P279 statements. -/",
      "theorem derivedInst_sound : ∀ p ∈ derivedInst,",
      "    ∃ d, kb.Inst p.1 d ∧ Relation.ReflTransGen kb.Sub d p.2 := by",
      "  rw [← derivedInst_eq]",
      "  exact fun _ hp => instFacts_sound kb_wellFormed hp",
      "",
      "/-- And nothing is missing. -/",
      "theorem derivedInst_complete : ∀ a ∈ kb.items, ∀ c ∈ kb.items,",
      "    (∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d c) → (a, c) ∈ derivedInst := by",
      "  rw [← derivedInst_eq]",
      "  exact fun _ ha _ hc h => instFacts_complete kb_wellFormed ha hc h",
      "",
      "/-! ### Some of the facts, individually -/",
      "",
      String.intercalate "\n" hlSub,
      String.intercalate "\n" hlInst,
      "end " ++ ns,
      "end Generated",
      "end Wikidata",
      "" ]

end Cli
end Wikidata
