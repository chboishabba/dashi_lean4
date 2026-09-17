/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Worklist
import RequestProject.CorpusFrontier

/-!
# Gaps: work that is not a defect

`RequestProject.Diagnostics` reports what is *wrong* with a base.  A curation
project also needs what is *missing*: items the base names and says nothing
about, items nothing links to, classes with nothing under them.  None of these
breaks validity — a base full of gaps is still a certified ontology — so they are
not errors, and none of them can be fixed by a rule.  They are leads.

This file turns three of them into ordinary report rows, so that the worklist
machinery of `RequestProject.Worklist` applies to them unchanged:

* `no-parent` — a declared item with no `subclass of` (P279) and no
  `instance of` (P31) statement.  This is `Wikidata.KB.rootlessL`, whose meaning
  is fixed by `Wikidata.KB.mem_rootlessL_iff`;
* `isolated` — a declared item that occurs in no statement at all, on either
  side (`Wikidata.KB.mem_isolatedL_iff`);
* `childless-class` — an item declared to be a class that no `instance of` and
  no `subclass of` statement points at (`Wikidata.KB.mem_childlessClassL_iff`).

The guarantees:

* `Wikidata.Report.gapRows_severity` — every gap row is a warning: a gap never
  says the base is invalid;
* `Wikidata.Report.rowOfGap_code_mem` — every gap row carries one of the three
  gap codes;
* `Wikidata.KB.isolated_mem_rootlessL` — an isolated item is in particular
  parentless, so the two leads are nested, not independent;
* `Wikidata.Report.gapRows_eq_nil_iff` — an empty gap table means every declared
  item is placed in the hierarchy, mentioned somewhere, and no declared class is
  empty.
-/

namespace Wikidata

namespace KB

variable (kb : KB)

/-- Does any statement of the base mention this item, on either side? -/
def mentionedB (q : Qid) : Bool :=
  kb.sub.any (fun p => p.1 == q || p.2 == q) ||
    kb.inst.any (fun p => p.1 == q || p.2 == q) ||
    kb.disj.any (fun p => p.1 == q || p.2 == q)

/-- The declared items that occur in no statement at all. -/
def isolatedL : List Qid := kb.items.filter fun q => !kb.mentionedB q

/-- Does any statement put something directly under this item? -/
def hasMemberB (c : Qid) : Bool :=
  kb.inst.any (fun p => p.2 == c) || kb.sub.any (fun p => p.2 == c)

/-- The declared classes with nothing under them: no `instance of` and no
`subclass of` statement points at them. -/
def childlessClassL : List Qid :=
  kb.items.filter fun c => kb.isClassB c && !kb.hasMemberB c

variable {kb}

theorem any_pair_eq_false_iff {l : List (Qid × Qid)} {q : Qid} :
    (l.any fun p => p.1 == q || p.2 == q) = false ↔
      (∀ b, (q, b) ∉ l) ∧ (∀ a, (a, q) ∉ l) := by
  simp only [List.any_eq_false, Bool.or_eq_true, beq_iff_eq, not_or]
  constructor
  · intro h
    exact ⟨fun b hb => (h _ hb).1 rfl, fun a ha => (h _ ha).2 rfl⟩
  · rintro ⟨h1, h2⟩ ⟨a, b⟩ hp
    exact ⟨fun hq => h1 b (hq ▸ hp), fun hq => h2 a (hq ▸ hp)⟩

/-- **What an isolated item is**: a declared item that no statement mentions. -/
theorem mem_isolatedL_iff {q : Qid} :
    q ∈ kb.isolatedL ↔ q ∈ kb.items ∧
      (∀ b, ¬ kb.Sub q b) ∧ (∀ a, ¬ kb.Sub a q) ∧
      (∀ c, ¬ kb.Inst q c) ∧ (∀ a, ¬ kb.Inst a q) ∧
      (∀ d, ¬ kb.Disj q d) := by
  simp only [isolatedL, List.mem_filter, mentionedB, Bool.not_eq_true', Bool.or_eq_false_iff,
    any_pair_eq_false_iff, Sub, Inst, Disj, not_or, forall_and]
  tauto

/-- **An isolated item is in particular parentless.** -/
theorem isolated_mem_rootlessL {q : Qid} (h : q ∈ kb.isolatedL) : q ∈ kb.rootlessL := by
  obtain ⟨hq, hs, _, hi, _, _⟩ := mem_isolatedL_iff.1 h
  exact mem_rootlessL_iff.2 ⟨hq, hs, hi⟩

/-- **What a childless class is**: a declared class that no `instance of` and no
`subclass of` statement points at. -/
theorem mem_childlessClassL_iff {c : Qid} :
    c ∈ kb.childlessClassL ↔ c ∈ kb.items ∧ 0 < kb.levelOf c ∧
      (∀ a, ¬ kb.Inst a c) ∧ (∀ a, ¬ kb.Sub a c) := by
  have hpair : ∀ (l : List (Qid × Qid)), (l.any fun p => p.2 == c) = false ↔ ∀ a, (a, c) ∉ l := by
    intro l
    simp only [List.any_eq_false, beq_iff_eq]
    constructor
    · intro h a ha; exact h _ ha rfl
    · rintro h ⟨a, b⟩ hp hb; exact h a (hb ▸ hp)
  simp only [childlessClassL, List.mem_filter, Bool.and_eq_true, isClassB, hasMemberB,
    decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff, hpair, Inst, Sub]

end KB

namespace Report

/-- A gap: something the base does not say, which somebody could go and find
out.  None of these breaks validity. -/
inductive Gap where
  /-- A declared item with no `subclass of` and no `instance of` statement. -/
  | noParent (q : Qid)
  /-- A declared item that occurs in no statement at all. -/
  | isolated (q : Qid)
  /-- A declared class with no instances and no subclasses. -/
  | childlessClass (c : Qid)
deriving DecidableEq, Repr, Inhabited

open Cli (qidText)

/-- A gap, as a row of the same table the diagnostics are reported in. -/
def rowOfGap : Gap → Row
  | .noParent q =>
      { layer := "gap", code := "no-parent", severity := .warning,
        status := .suggestedFix, subject := qidText q, object := "", extra := "",
        message := "declared item with no `subclass of` (P279) and no `instance of` (P31) statement: the base says nothing about what it is",
        fix := "download the item (`wikidata fetch`) or add a P279 or P31 statement" }
  | .isolated q =>
      { layer := "gap", code := "isolated", severity := .warning,
        status := .needsReview, subject := qidText q, object := "", extra := "",
        message := "declared item that occurs in no statement at all",
        fix := "either it is a seed still to be crawled, or the declaration can go; a human decides" }
  | .childlessClass c =>
      { layer := "gap", code := "childless-class", severity := .warning,
        status := .needsReview, subject := qidText c, object := "", extra := "",
        message := "declared class that no `instance of` and no `subclass of` statement points at",
        fix := "download its instances, or check that it is a class at all" }

/-- The gap kinds, as they appear in a report file. -/
def gapCodes : List String := ["no-parent", "isolated", "childless-class"]

theorem gapCodes_nodup : gapCodes.Nodup := by decide

theorem rowOfGap_code_mem (g : Gap) : (rowOfGap g).code ∈ gapCodes := by
  cases g <;> simp [rowOfGap, gapCodes]

/-- **A gap is never an error**: it is a lead, and the base stays valid. -/
theorem rowOfGap_severity (g : Gap) : (rowOfGap g).severity = .warning := by
  cases g <;> rfl

/-- The gaps of a base: parentless items, then isolated items, then childless
classes. -/
def KB.gaps (kb : Wikidata.KB) : List Gap :=
  kb.rootlessL.map Gap.noParent ++ kb.isolatedL.map Gap.isolated ++
    kb.childlessClassL.map Gap.childlessClass

/-- The gap table of a base. -/
def KB.gapRows (kb : Wikidata.KB) : List Row := (KB.gaps kb).map rowOfGap

/-- **Every gap row is a warning.** -/
theorem gapRows_severity (kb : Wikidata.KB) :
    ∀ r ∈ KB.gapRows kb, r.severity = .warning := by
  intro r hr
  obtain ⟨g, _, rfl⟩ := List.mem_map.1 hr
  exact rowOfGap_severity g

/-- **Every gap row carries a gap code.** -/
theorem gapRows_code_mem (kb : Wikidata.KB) :
    ∀ r ∈ KB.gapRows kb, r.code ∈ gapCodes := by
  intro r hr
  obtain ⟨g, _, rfl⟩ := List.mem_map.1 hr
  exact rowOfGap_code_mem g

/-- **An empty gap table is a certificate**: nothing is missing in any of the
three senses. -/
theorem gapRows_eq_nil_iff (kb : Wikidata.KB) :
    KB.gapRows kb = [] ↔
      kb.rootlessL = [] ∧ kb.isolatedL = [] ∧ kb.childlessClassL = [] := by
  simp [KB.gapRows, KB.gaps]

/-- How many rows the gap table has, kind by kind. -/
theorem gapRows_length (kb : Wikidata.KB) :
    (KB.gapRows kb).length =
      kb.rootlessL.length + kb.isolatedL.length + kb.childlessClassL.length := by
  simp [KB.gapRows, KB.gaps, Nat.add_assoc]

/-! ## A worked example -/

open Wikidata.KB (brokenKB)

/-- The defective base of `RequestProject.Diagnostics` has one gap: `Q4` is a
declared class the base places nowhere. -/
example : (KB.gapRows brokenKB).map Row.code = ["no-parent"] := by decide

/-- A base with nothing wrong with it and plenty to do: `Q4` is an instance of
the class `Q1`, `Q2` is a declared class with nothing under it, and `Q3` is
declared and mentioned by no statement at all. -/
def gappyKB : Wikidata.KB where
  name := "gappy"
  items := [Qid.wd "Q1", Qid.wd "Q2", Qid.wd "Q3", Qid.wd "Q4"]
  levels := [(Qid.wd "Q1", 1), (Qid.wd "Q2", 1)]
  inst := [(Qid.wd "Q4", Qid.wd "Q1")]

/-- It is valid and carries no redundant statement: the diagnostics have nothing
to say about it. -/
example : gappyKB.clean = true := by decide

/-- The gap table nevertheless has six leads. -/
example : (KB.gapRows gappyKB).map (fun r => (r.code, r.subject)) =
    [("no-parent", "Q1"), ("no-parent", "Q2"), ("no-parent", "Q3"),
     ("isolated", "Q2"), ("isolated", "Q3"), ("childless-class", "Q2")] := by decide

/-- Grouped into things to work on, biggest first. -/
example : (worklist byCode (KB.gapRows gappyKB)).map (fun t => (t.key, t.size)) =
    [("no-parent", 3), ("isolated", 2), ("childless-class", 1)] := by decide

end Report
end Wikidata
