import RequestProject.Redundancy

/-!
# A diagnostic report for a Wikidata knowledge base

`Wikidata:WikiProject Ontology` spends much of its effort on *finding and describing
modelling problems*: statements pointing at items that are not there, `instance of`
used where `subclass of` is meant (a metaclass level mismatch), genuine cycles in the
class hierarchy, items instantiating two classes declared disjoint, and — as a matter
of style rather than of correctness — subclass statements that are already implied.

`Wikidata.KB.valid` (in `RequestProject.Engine`) answers "is this base sound?" with a
single Boolean. This file turns that Boolean into a **report**: a list of concrete,
individually witnessed issues.

* `Wikidata.Issue` enumerates the kinds of problem;
* `Wikidata.KB.errors` collects the ones that break validity, `Wikidata.KB.warnings`
  the redundant subclass statements of `RequestProject.Redundancy`;
* `Wikidata.KB.errors_eq_nil_iff_valid` — the report is **sound and complete**: it is
  empty exactly when the base is valid, so nothing is invented and nothing is missed;
* every reported issue comes with its witness (`Wikidata.KB.mem_cycleIssues_iff`,
  `Wikidata.KB.mem_disjointIssues_iff`, …), so a report can be acted on;
* `Wikidata.KB.warning_prunable` — every warning can be fixed by a deletion that
  changes no derived fact and preserves validity.
-/

namespace Wikidata

/-- A modelling problem found in a knowledge base. -/
inductive Issue where
  /-- A `subclass of` statement with an endpoint that is not a declared item. -/
  | danglingSub (a b : Qid)
  /-- An `instance of` statement with an endpoint that is not a declared item. -/
  | danglingInst (a c : Qid)
  /-- A disjointness declaration with an endpoint that is not a declared item. -/
  | danglingDisj (c d : Qid)
  /-- An `instance of` statement whose value does not sit one metaclass level up. -/
  | levelMismatchInst (a c : Qid)
  /-- A `subclass of` statement between items of different metaclass levels, or on an
  individual. -/
  | levelMismatchSub (a b : Qid)
  /-- Two distinct classes that are subclasses of each other. -/
  | subclassCycle (a b : Qid)
  /-- An item instantiating two classes declared disjoint. -/
  | disjointViolation (c d a : Qid)
  /-- A `subclass of` statement that is already implied by the others. -/
  | redundantSubclass (a b : Qid)
deriving DecidableEq, Repr, Inhabited

namespace KB

variable (kb : KB)

/-! ### The individual checks -/

/-- `subclass of` statements with an undeclared endpoint. -/
def danglingSubIssues : List Issue :=
  (kb.sub.filter (fun r => !(r.1 ∈ kb.items && r.2 ∈ kb.items))).map
    (fun r => Issue.danglingSub r.1 r.2)

/-- `instance of` statements with an undeclared endpoint. -/
def danglingInstIssues : List Issue :=
  (kb.inst.filter (fun r => !(r.1 ∈ kb.items && r.2 ∈ kb.items))).map
    (fun r => Issue.danglingInst r.1 r.2)

/-- Disjointness declarations with an undeclared endpoint. -/
def danglingDisjIssues : List Issue :=
  (kb.disj.filter (fun r => !(r.1 ∈ kb.items && r.2 ∈ kb.items))).map
    (fun r => Issue.danglingDisj r.1 r.2)

/-- `instance of` statements violating the metaclass level discipline. -/
def levelInstIssues : List Issue :=
  (kb.inst.filter (fun r => !(kb.levelOf r.2 == kb.levelOf r.1 + 1))).map
    (fun r => Issue.levelMismatchInst r.1 r.2)

/-- `subclass of` statements violating the metaclass level discipline. -/
def levelSubIssues : List Issue :=
  (kb.sub.filter (fun r => !((kb.levelOf r.1 == kb.levelOf r.2) && (0 < kb.levelOf r.1)))).map
    (fun r => Issue.levelMismatchSub r.1 r.2)

/-- Genuine cycles in the class hierarchy. -/
def cycleIssues : List Issue :=
  ((kb.items.product kb.items).filter
    (fun p => kb.isSubclassOf p.1 p.2 && kb.isSubclassOf p.2 p.1 && p.1 != p.2)).map
    (fun p => Issue.subclassCycle p.1 p.2)

/-- Items instantiating two classes declared disjoint. -/
def disjointIssues : List Issue :=
  ((kb.disj.product kb.items).filter
    (fun p => kb.isInstanceOf p.2 p.1.1 && kb.isInstanceOf p.2 p.1.2)).map
    (fun p => Issue.disjointViolation p.1.1 p.1.2 p.2)

/-- The full error report of a knowledge base. -/
def errors : List Issue :=
  kb.danglingSubIssues ++ kb.danglingInstIssues ++ kb.danglingDisjIssues ++
    kb.levelInstIssues ++ kb.levelSubIssues ++ kb.cycleIssues ++ kb.disjointIssues

/-- The style warnings of a knowledge base: its redundant `subclass of` statements. -/
def warnings : List Issue :=
  kb.redundantSubL.map (fun r => Issue.redundantSubclass r.1 r.2)

/-- The base is clean: no errors and no warnings. -/
def clean : Bool := kb.errors.isEmpty && kb.warnings.isEmpty

variable {kb}

/-! ### Each check matches its Boolean counterpart -/

theorem danglingSubIssues_eq_nil_iff :
    kb.danglingSubIssues = [] ↔
      kb.sub.all (fun r => r.1 ∈ kb.items && r.2 ∈ kb.items) = true := by
  simp [danglingSubIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingInstIssues_eq_nil_iff :
    kb.danglingInstIssues = [] ↔
      kb.inst.all (fun r => r.1 ∈ kb.items && r.2 ∈ kb.items) = true := by
  simp [danglingInstIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingDisjIssues_eq_nil_iff :
    kb.danglingDisjIssues = [] ↔
      kb.disj.all (fun r => r.1 ∈ kb.items && r.2 ∈ kb.items) = true := by
  simp [danglingDisjIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem levelInstIssues_eq_nil_iff :
    kb.levelInstIssues = [] ↔
      kb.inst.all (fun r => kb.levelOf r.2 == kb.levelOf r.1 + 1) = true := by
  simp [levelInstIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem levelSubIssues_eq_nil_iff :
    kb.levelSubIssues = [] ↔
      kb.sub.all (fun r => (kb.levelOf r.1 == kb.levelOf r.2) && (0 < kb.levelOf r.1)) = true := by
  simp [levelSubIssues, List.filter_eq_nil_iff, List.all_eq_true, Nat.pos_iff_ne_zero]

theorem cycleIssues_eq_nil_iff : kb.cycleIssues = [] ↔ kb.acyclic = true := by
  rw [cycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [acyclic, List.all_eq_true]
    intro a ha b hb
    have hp := h (a := (a, b)) (List.pair_mem_product.2 ⟨ha, hb⟩)
    revert hp
    cases hab : kb.isSubclassOf a b <;> cases hba : kb.isSubclassOf b a <;>
      cases heq : (a == b) <;> simp_all
  · rintro h ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb
    revert hall
    cases hab : kb.isSubclassOf a b <;> cases hba : kb.isSubclassOf b a <;>
      cases heq : (a == b) <;> simp_all

theorem disjointIssues_eq_nil_iff : kb.disjointIssues = [] ↔ kb.disjointOk = true := by
  rw [disjointIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [disjointOk, List.all_eq_true]
    rintro ⟨c, d⟩ hcd a ha
    have hp := h (a := ((c, d), a)) (List.pair_mem_product.2 ⟨hcd, ha⟩)
    revert hp
    cases h1 : kb.isInstanceOf a c <;> cases h2 : kb.isInstanceOf a d <;> simp_all
  · rintro h ⟨⟨c, d⟩, a⟩ hp
    obtain ⟨hcd, ha⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h (c, d) hcd) a ha
    revert hall
    cases h1 : kb.isInstanceOf a c <;> cases h2 : kb.isInstanceOf a d <;> simp_all

/-! ### The report is sound and complete -/

/-- **The error report is empty exactly when the knowledge base is valid.** -/
theorem errors_eq_nil_iff_valid : kb.errors = [] ↔ kb.valid = true := by
  rw [errors]
  simp only [List.append_eq_nil_iff, danglingSubIssues_eq_nil_iff, danglingInstIssues_eq_nil_iff,
    danglingDisjIssues_eq_nil_iff, levelInstIssues_eq_nil_iff, levelSubIssues_eq_nil_iff,
    cycleIssues_eq_nil_iff, disjointIssues_eq_nil_iff, valid, wellFormed, levelsOk,
    Bool.and_eq_true]
  tauto

/-- A knowledge base with no errors is a Wikidata ontology. -/
theorem valid_of_errors_eq_nil (h : kb.errors = []) : kb.valid = true :=
  errors_eq_nil_iff_valid.1 h

/-! ### Every reported issue comes with its witness -/

theorem mem_danglingSubIssues_iff {a b : Qid} :
    Issue.danglingSub a b ∈ kb.danglingSubIssues ↔
      (a, b) ∈ kb.sub ∧ ¬(a ∈ kb.items ∧ b ∈ kb.items) := by
  simp only [danglingSubIssues, List.mem_map, List.mem_filter, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Prod.exists, Issue.danglingSub.injEq]
  constructor
  · rintro ⟨x, y, ⟨hmem, hcond⟩, rfl, rfl⟩
    exact ⟨hmem, by tauto⟩
  · rintro ⟨hmem, hcond⟩
    exact ⟨a, b, ⟨hmem, by tauto⟩, rfl, rfl⟩

theorem mem_danglingInstIssues_iff {a c : Qid} :
    Issue.danglingInst a c ∈ kb.danglingInstIssues ↔
      (a, c) ∈ kb.inst ∧ ¬(a ∈ kb.items ∧ c ∈ kb.items) := by
  simp only [danglingInstIssues, List.mem_map, List.mem_filter, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Prod.exists, Issue.danglingInst.injEq]
  constructor
  · rintro ⟨x, y, ⟨hmem, hcond⟩, rfl, rfl⟩
    exact ⟨hmem, by tauto⟩
  · rintro ⟨hmem, hcond⟩
    exact ⟨a, c, ⟨hmem, by tauto⟩, rfl, rfl⟩

theorem mem_levelInstIssues_iff {a c : Qid} :
    Issue.levelMismatchInst a c ∈ kb.levelInstIssues ↔
      (a, c) ∈ kb.inst ∧ kb.levelOf c ≠ kb.levelOf a + 1 := by
  simp [levelInstIssues, List.mem_map, List.mem_filter]

/-- A reported cycle really is one: two distinct items, each a derived subclass of the
other. -/
theorem mem_cycleIssues_iff {a b : Qid} :
    Issue.subclassCycle a b ∈ kb.cycleIssues ↔
      a ∈ kb.items ∧ b ∈ kb.items ∧ kb.isSubclassOf a b = true ∧
        kb.isSubclassOf b a = true ∧ a ≠ b := by
  rw [cycleIssues]
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hp, heq⟩ := List.mem_map.1 h
    obtain ⟨hmem, hcond⟩ := List.mem_filter.1 hp
    simp only [Issue.subclassCycle.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hx, hy⟩ := List.pair_mem_product.1 hmem
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    exact ⟨hx, hy, hcond.1.1, hcond.1.2, hcond.2⟩
  · rintro ⟨hx, hy, h1, h2, h3⟩
    refine List.mem_map.2 ⟨(a, b), List.mem_filter.2 ⟨List.pair_mem_product.2 ⟨hx, hy⟩, ?_⟩, rfl⟩
    simp [h1, h2, h3]

/-- A reported disjointness violation really is one. -/
theorem mem_disjointIssues_iff {c d a : Qid} :
    Issue.disjointViolation c d a ∈ kb.disjointIssues ↔
      (c, d) ∈ kb.disj ∧ a ∈ kb.items ∧ kb.isInstanceOf a c = true ∧
        kb.isInstanceOf a d = true := by
  rw [disjointIssues]
  constructor
  · intro h
    obtain ⟨⟨⟨x, y⟩, z⟩, hp, heq⟩ := List.mem_map.1 h
    obtain ⟨hmem, hcond⟩ := List.mem_filter.1 hp
    simp only [Issue.disjointViolation.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨hxy, hz⟩ := List.pair_mem_product.1 hmem
    simp only [Bool.and_eq_true] at hcond
    exact ⟨hxy, hz, hcond.1, hcond.2⟩
  · rintro ⟨hcd, ha, h1, h2⟩
    refine List.mem_map.2 ⟨((c, d), a),
      List.mem_filter.2 ⟨List.pair_mem_product.2 ⟨hcd, ha⟩, ?_⟩, rfl⟩
    simp [h1, h2]

/-- A reported cycle contradicts validity — which is the content of the completeness
statement, seen from the other side. -/
theorem not_mem_cycleIssues_of_valid (hv : kb.valid = true) (a b : Qid) :
    Issue.subclassCycle a b ∉ kb.cycleIssues := by
  intro h
  obtain ⟨-, -, h1, h2, hne⟩ := mem_cycleIssues_iff.1 h
  have hwf := valid_wellFormed hv
  exact hne (subclass_antisymm hv ((isSubclassOf_iff hwf a b).1 h1)
    ((isSubclassOf_iff hwf b a).1 h2))

/-! ### Warnings -/

theorem mem_warnings_iff {a b : Qid} :
    Issue.redundantSubclass a b ∈ kb.warnings ↔
      (a, b) ∈ kb.sub ∧ kb.isRedundantSubB (a, b) = true := by
  rw [warnings, redundantSubL]
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hp, heq⟩ := List.mem_map.1 h
    obtain ⟨hmem, hred⟩ := List.mem_filter.1 hp
    simp only [Issue.redundantSubclass.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨hmem, hred⟩
  · rintro ⟨hmem, hred⟩
    exact List.mem_map.2 ⟨(a, b), List.mem_filter.2 ⟨hmem, hred⟩, rfl⟩

/-- **Every warning can be acted on**: deleting the statement it reports changes no
derived subclass or instance fact, and keeps the base valid. -/
theorem warning_prunable (hv : kb.valid = true) {a b : Qid}
    (hw : Issue.redundantSubclass a b ∈ kb.warnings) :
    (kb.dropSub (a, b)).valid = true ∧
    (∀ x y, (kb.dropSub (a, b)).isSubclassOf x y = kb.isSubclassOf x y) ∧
    (∀ x c, (kb.dropSub (a, b)).isInstanceOf x c = kb.isInstanceOf x c) := by
  have hred := (mem_warnings_iff.1 hw).2
  exact ⟨dropSub_valid hv hred, fun x y => dropSub_isSubclassOf hv hred x y,
    fun x c => dropSub_isInstanceOf hv hred x c⟩

/-- A valid base with no redundant statements is clean, and conversely. -/
theorem clean_iff : kb.clean = true ↔ kb.valid = true ∧ kb.redundantSubL = [] := by
  simp only [clean, Bool.and_eq_true, List.isEmpty_iff, errors_eq_nil_iff_valid, warnings,
    List.map_eq_nil_iff]

/-! ### A worked fragment: a base with three problems

`Q1` and `Q2` are declared subclasses of each other (a cycle), `Q3` is an instance of
`Q1` and of `Q4` although `Q1` and `Q4` are declared disjoint, and there is a
statement about an undeclared item `Q9`. -/

/-- A knowledge base with several modelling problems. -/
def brokenKB : KB where
  name := "broken"
  items := [Qid.wd "Q1", Qid.wd "Q2", Qid.wd "Q3", Qid.wd "Q4"]
  levels := [(Qid.wd "Q1", 1), (Qid.wd "Q2", 1), (Qid.wd "Q4", 1)]
  sub := [(Qid.wd "Q1", Qid.wd "Q2"), (Qid.wd "Q2", Qid.wd "Q1"),
          (Qid.wd "Q1", Qid.wd "Q9")]
  inst := [(Qid.wd "Q3", Qid.wd "Q1"), (Qid.wd "Q3", Qid.wd "Q4")]
  disj := [(Qid.wd "Q1", Qid.wd "Q4")]

theorem brokenKB_not_valid : brokenKB.valid = false := by decide

/-- The dangling statement is reported, with its witness. -/
theorem brokenKB_dangling :
    brokenKB.danglingSubIssues = [Issue.danglingSub (Qid.wd "Q1") (Qid.wd "Q9")] := by decide

/-- Both directions of the cycle are reported. -/
theorem brokenKB_cycles :
    brokenKB.cycleIssues =
      [Issue.subclassCycle (Qid.wd "Q1") (Qid.wd "Q2"),
       Issue.subclassCycle (Qid.wd "Q2") (Qid.wd "Q1")] := by decide

/-- The disjointness violation is reported, naming the offending item. -/
theorem brokenKB_disjoint :
    brokenKB.disjointIssues =
      [Issue.disjointViolation (Qid.wd "Q1") (Qid.wd "Q4") (Qid.wd "Q3")] := by decide

/-- The report of the healthy base of `RequestProject.Redundancy` is empty apart from
the redundancy warning. -/
theorem redundantKB_report :
    redundantKB.errors = [] ∧
    redundantKB.warnings = [Issue.redundantSubclass (Qid.wd "Q5") (Qid.wd "Q35120")] := by
  decide

/-- After pruning, the base is clean. -/
theorem redundantKB_pruned_clean :
    (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).clean = true := by decide

end KB

end Wikidata
