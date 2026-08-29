import RequestProject.Parenting
import RequestProject.Diagnostics

/-!
# A diagnostic report for the parenting layer

`RequestProject.KinshipDiagnostics` turns the Boolean validator of the classical
`father`/`mother` layer into a list of individually witnessed issues.  This file does
the same for the wider parenting layer of `RequestProject.Parenting`: parenthood or
`spouse` (P26) statements pointing at undeclared items, somebody recorded as their own
parent, a *genetic* statement recorded under the gender-neutral `parent` (P8810)
instead of `father` (P22) or `mother` (P25), two different genetic fathers or genetic
mothers, a cycle in the ancestry, somebody married to themselves, and parenthood
statements between items already related by `subclass of` or `instance of`.

Note what is deliberately *not* an issue: several parents, several adoptive parents,
a stepparent, a surrogate and a donor next to the biological parents.  Those are the
whole point of the layer.

The report is **sound and complete** — `ParentingKB.pErrors_eq_nil_iff` and
`ParentingKB.report_eq_nil_iff_pValid`: it is empty exactly when the layer passes the
validator, so nothing is invented and nothing is missed, and every issue carries its
witness.  Step-parenthood that is not backed by a marriage is reported separately, as
a warning (`ParentingKB.stepWarnings`), since Wikidata records it too.
-/

namespace Wikidata

/-- The kinds of problem a parenting layer can have. -/
inductive ParentIssue where
  /-- A parenthood statement with an endpoint that is not a declared item. -/
  | danglingParent (c pa : Qid)
  /-- A `spouse` (P26) statement with an endpoint that is not a declared item. -/
  | danglingSpouse (a b : Qid)
  /-- Somebody recorded as their own parent. -/
  | selfParent (a : Qid)
  /-- A genetic parenthood statement recorded under the neutral `parent` (P8810)
  rather than `father` (P22) or `mother` (P25). -/
  | untypedGeneticParent (c pa : Qid)
  /-- Somebody recorded with two different genetic parents in the same slot. -/
  | twoGeneticParents (c x y : Qid)
  /-- Two distinct people each descending from the other. -/
  | ancestryCycle (a b : Qid)
  /-- Somebody recorded as their own spouse. -/
  | selfSpouse (a : Qid)
  /-- A parenthood statement between items already related by `subclass of` or
  `instance of`. -/
  | parentClassConfusion (c pa : Qid)
  /-- A stepparent who is not recorded as the spouse of a parent of the child.  This
  is a warning, not an error. -/
  | unsupportedStepparent (c pa : Qid)
deriving DecidableEq, Repr, Inhabited

namespace ParentingKB

variable (k : ParentingKB)

/-! ### The individual checks -/

/-- Parenthood statements with an undeclared endpoint. -/
def danglingParentIssues : List ParentIssue :=
  (k.edges.filter (fun e => !(e.child ∈ k.base.items && e.parent ∈ k.base.items))).map
    (fun e => ParentIssue.danglingParent e.child e.parent)

/-- P26 statements with an undeclared endpoint. -/
def danglingSpouseIssues : List ParentIssue :=
  (k.spouses.filter (fun r => !(r.1 ∈ k.base.items && r.2 ∈ k.base.items))).map
    (fun r => ParentIssue.danglingSpouse r.1 r.2)

/-- People recorded as their own parent. -/
def selfParentIssues : List ParentIssue :=
  (k.edges.filter (fun e => e.child == e.parent)).map
    (fun e => ParentIssue.selfParent e.child)

/-- Genetic statements filed under the neutral `parent` (P8810). -/
def untypedGeneticIssues : List ParentIssue :=
  (k.edges.filter (fun e => !(!e.role.isGenetic || e.slot.isGendered))).map
    (fun e => ParentIssue.untypedGeneticParent e.child e.parent)

/-- People recorded with two different genetic parents in one slot. -/
def twoGeneticParentIssues : List ParentIssue :=
  ((k.edges.product k.edges).filter
    (fun p => (p.1.role.isGenetic && p.2.role.isGenetic && p.1.child == p.2.child &&
      p.1.slot == p.2.slot) && p.1.parent != p.2.parent)).map
    (fun p => ParentIssue.twoGeneticParents p.1.child p.1.parent p.2.parent)

/-- Genuine cycles in the ancestry. -/
def ancestryCycleIssues : List ParentIssue :=
  ((k.base.items.product k.base.items).filter
    (fun p => k.descendsFromB p.1 p.2 && k.descendsFromB p.2 p.1 && p.1 != p.2)).map
    (fun p => ParentIssue.ancestryCycle p.1 p.2)

/-- People recorded as their own spouse. -/
def selfSpouseIssues : List ParentIssue :=
  (k.spouses.filter (fun r => r.1 == r.2)).map (fun r => ParentIssue.selfSpouse r.1)

/-- Parenthood statements confusing the genealogy with the taxonomy. -/
def parentClassConfusionIssues : List ParentIssue :=
  (k.edges.filter
    (fun e => !(!k.base.isSubclassOf e.child e.parent &&
      !k.base.isInstanceOf e.child e.parent))).map
    (fun e => ParentIssue.parentClassConfusion e.child e.parent)

/-- Step-parenthood not backed by a marriage: a **warning**, not an error. -/
def stepWarnings : List ParentIssue :=
  (k.edges.filter (fun e => !(e.role != ParentRole.step ||
    k.base.items.any (fun pa => pa ∈ k.parentsL e.child && k.spouseB pa e.parent)))).map
    (fun e => ParentIssue.unsupportedStepparent e.child e.parent)

/-- The full error report of a parenting layer (the underlying taxonomy is reported
separately, by `KB.errors`). -/
def pErrors : List ParentIssue :=
  k.danglingParentIssues ++ k.danglingSpouseIssues ++ k.selfParentIssues ++
    k.untypedGeneticIssues ++ k.twoGeneticParentIssues ++ k.ancestryCycleIssues ++
    k.selfSpouseIssues ++ k.parentClassConfusionIssues

variable {k}

/-! ### Each check matches its Boolean counterpart -/

theorem danglingParentIssues_eq_nil_iff :
    k.danglingParentIssues = [] ↔
      k.edges.all (fun e => e.child ∈ k.base.items && e.parent ∈ k.base.items) = true := by
  simp [danglingParentIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingSpouseIssues_eq_nil_iff :
    k.danglingSpouseIssues = [] ↔
      k.spouses.all (fun r => r.1 ∈ k.base.items && r.2 ∈ k.base.items) = true := by
  simp [danglingSpouseIssues, List.filter_eq_nil_iff, List.all_eq_true]

/-- The two dangling checks together are exactly well-formedness of the layer, given a
well-formed taxonomy. -/
theorem pWellFormed_iff (hbase : k.base.wellFormed = true) :
    k.pWellFormed = true ↔
      k.danglingParentIssues = [] ∧ k.danglingSpouseIssues = [] := by
  simp only [pWellFormed, Bool.and_eq_true, hbase, true_and,
    danglingParentIssues_eq_nil_iff, danglingSpouseIssues_eq_nil_iff]

theorem selfParentIssues_eq_nil_iff : k.selfParentIssues = [] ↔ k.noSelfParent = true := by
  simp [selfParentIssues, noSelfParent, List.filter_eq_nil_iff, List.all_eq_true]

theorem untypedGeneticIssues_eq_nil_iff :
    k.untypedGeneticIssues = [] ↔ k.geneticSlotsTyped = true := by
  simp [untypedGeneticIssues, geneticSlotsTyped, List.filter_eq_nil_iff, List.all_eq_true,
    imp_iff_not_or, Bool.not_eq_true]

theorem twoGeneticParentIssues_eq_nil_iff :
    k.twoGeneticParentIssues = [] ↔ k.singleGeneticParents = true := by
  rw [twoGeneticParentIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [singleGeneticParents, List.all_eq_true]
    rintro e he e' he'
    have hp := h (a := (e, e')) (List.pair_mem_product.2 ⟨he, he'⟩)
    revert hp
    cases h1 : (e.role.isGenetic && e'.role.isGenetic && (e.child == e'.child) &&
      (e.slot == e'.slot)) <;> cases h2 : (e.parent == e'.parent) <;> simp_all
  · rintro h ⟨e, e'⟩ hp
    obtain ⟨he, he'⟩ := List.pair_mem_product.1 hp
    simp only [singleGeneticParents, List.all_eq_true] at h
    have hall := h e he e' he'
    revert hall
    cases h1 : (e.role.isGenetic && e'.role.isGenetic && (e.child == e'.child) &&
      (e.slot == e'.slot)) <;> cases h2 : (e.parent == e'.parent) <;> simp_all

theorem ancestryCycleIssues_eq_nil_iff :
    k.ancestryCycleIssues = [] ↔ k.pAcyclic = true := by
  rw [ancestryCycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [pAcyclic, List.all_eq_true]
    intro a ha b hb
    have hp := h (a := (a, b)) (List.pair_mem_product.2 ⟨ha, hb⟩)
    revert hp
    cases hab : k.descendsFromB a b <;> cases hba : k.descendsFromB b a <;>
      cases heq : (a == b) <;> simp_all
  · rintro h ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := List.pair_mem_product.1 hp
    simp only [pAcyclic, List.all_eq_true] at h
    have hall := h a ha b hb
    revert hall
    cases hab : k.descendsFromB a b <;> cases hba : k.descendsFromB b a <;>
      cases heq : (a == b) <;> simp_all

theorem selfSpouseIssues_eq_nil_iff : k.selfSpouseIssues = [] ↔ k.noSelfSpouse = true := by
  simp [selfSpouseIssues, noSelfSpouse, List.filter_eq_nil_iff, List.all_eq_true]

theorem parentClassConfusionIssues_eq_nil_iff :
    k.parentClassConfusionIssues = [] ↔ k.noParentClassConfusion = true := by
  simp [parentClassConfusionIssues, noParentClassConfusion, List.filter_eq_nil_iff,
    List.all_eq_true]

theorem stepWarnings_eq_nil_iff : k.stepWarnings = [] ↔ k.stepConsistent = true := by
  simp [stepWarnings, stepConsistent, List.filter_eq_nil_iff, List.all_eq_true,
    imp_iff_not_or]

/-! ### The report is sound and complete -/

/-- **The parenting error report is empty exactly when the parenting layer passes its
checks** (given a well-formed underlying taxonomy). -/
theorem pErrors_eq_nil_iff (hbase : k.base.wellFormed = true) :
    k.pErrors = [] ↔ k.pLayerValid = true := by
  rw [pErrors]
  simp only [List.append_eq_nil_iff, pLayerValid, Bool.and_eq_true,
    pWellFormed_iff hbase, selfParentIssues_eq_nil_iff, untypedGeneticIssues_eq_nil_iff,
    twoGeneticParentIssues_eq_nil_iff, ancestryCycleIssues_eq_nil_iff,
    selfSpouseIssues_eq_nil_iff, parentClassConfusionIssues_eq_nil_iff]

/-- **The full report**: the taxonomy report and the parenting report are both empty
exactly when the whole layer is valid. -/
theorem report_eq_nil_iff_pValid :
    (k.base.errors = [] ∧ k.pErrors = []) ↔ k.pValid = true := by
  constructor
  · rintro ⟨hb, hp⟩
    have hvalid : k.base.valid = true := KB.errors_eq_nil_iff_valid.1 hb
    have hwf : k.base.wellFormed = true := KB.valid_wellFormed hvalid
    simp only [pValid, Bool.and_eq_true]
    exact ⟨hvalid, (pErrors_eq_nil_iff hwf).1 hp⟩
  · intro h
    simp only [pValid, Bool.and_eq_true] at h
    have hwf : k.base.wellFormed = true := KB.valid_wellFormed h.1
    exact ⟨KB.errors_eq_nil_iff_valid.2 h.1, (pErrors_eq_nil_iff hwf).2 h.2⟩

end ParentingKB

end Wikidata
