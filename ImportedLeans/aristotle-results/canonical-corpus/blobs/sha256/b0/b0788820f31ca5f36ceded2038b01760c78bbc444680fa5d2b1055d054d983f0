import RequestProject.Engine
import RequestProject.Diagnostics
import RequestProject.Cli.Derive

/-!
# Evaluating a knowledge base quickly

`KB.isSubclassOf` recomputes the transitive closure of the `subclass of` graph on
every call, which is fine for a handful of items and hopeless for a fragment of
Wikidata with a few hundred: the validator asks the question once per *pair* of
items.

This file computes the closure **once**, as a table (`KB.closureTable`), and
re-expresses the expensive checks in terms of it.  Every fast version is proved
equal to the original, so nothing about the meaning of the checks changes:

* `KB.isSubclassOfT_closureTable`, `KB.isInstanceOfT_closureTable` — the queries;
* `KB.superclassesOfLT_eq`, `KB.classesOfT_eq` — their list-valued forms;
* `KB.acyclicFast_eq`, `KB.disjointOkFast_eq`, `KB.validFast_eq` — the validator;
* `KB.cycleIssuesFast_eq`, `KB.disjointIssuesFast_eq`, `KB.errorsFast_eq` — the
  diagnostic report.

The command line tool and the Lean code generator use the fast versions and cite
these equalities, so their output is exactly the output of the definitions the
rest of the project reasons about.
-/

namespace Wikidata
namespace KB

variable (kb : KB)

/-! ### The closure table -/

/-- All superclasses of every declared item, computed once. -/
def closureTable : List (Qid × Finset Qid) := kb.items.map fun a => (a, kb.superclasses a)

/-- The superclasses of an item, read off a table (falling back on recomputation
for items the table does not mention). -/
def closureLookup (T : List (Qid × Finset Qid)) (a : Qid) : Finset Qid :=
  (T.lookup a).getD (kb.superclasses a)

variable {kb}

theorem lookup_map_self {l : List Qid} {f : Qid → Finset Qid} {a : Qid} (ha : a ∈ l) :
    (l.map fun x => (x, f x)).lookup a = some (f a) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      by_cases h : a = x
      · subst h; simp
      · have hbeq : (a == x) = false := by simpa using h
        have hx : a ∈ xs := by
          rcases List.mem_cons.1 ha with h' | h'
          · exact absurd h' h
          · exact h'
        simp only [List.map_cons, List.lookup_cons, hbeq]
        exact ih hx

theorem lookup_map_self_none {l : List Qid} {f : Qid → Finset Qid} {a : Qid} (ha : a ∉ l) :
    (l.map fun x => (x, f x)).lookup a = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : a ≠ x := fun h => ha (h ▸ List.mem_cons_self ..)
      have hbeq : (a == x) = false := by simpa using hx
      simp only [List.map_cons, List.lookup_cons, hbeq]
      exact ih fun h => ha (List.mem_cons_of_mem _ h)

/-- **The table is faithful**: looking an item up in `closureTable` returns its
superclasses. -/
@[simp] theorem closureLookup_closureTable (a : Qid) :
    kb.closureLookup kb.closureTable a = kb.superclasses a := by
  by_cases ha : a ∈ kb.items
  · simp [closureLookup, closureTable, lookup_map_self ha]
  · simp [closureLookup, closureTable, lookup_map_self_none ha]

variable (kb)

/-! ### Queries against a table -/

/-- Derived `subclass of`, answered from a table. -/
def isSubclassOfT (T : List (Qid × Finset Qid)) (a b : Qid) : Bool := b ∈ kb.closureLookup T a

/-- All classes an item is an instance of, answered from a table. -/
def instClosureT (T : List (Qid × Finset Qid)) (a : Qid) : Finset Qid :=
  ((kb.directClassesL a).map (kb.closureLookup T)).foldr (· ∪ ·) ∅

/-- Derived `instance of`, answered from a table. -/
def isInstanceOfT (T : List (Qid × Finset Qid)) (a c : Qid) : Bool := c ∈ kb.instClosureT T a

/-- The declared superclasses of an item, answered from a table. -/
def superclassesOfLT (T : List (Qid × Finset Qid)) (a : Qid) : List Qid :=
  let S := kb.closureLookup T a
  kb.items.filter fun c => c ∈ S

/-- The declared classes of an item, answered from a table. -/
def classesOfT (T : List (Qid × Finset Qid)) (a : Qid) : List Qid :=
  let S := kb.instClosureT T a
  kb.items.filter fun c => c ∈ S

variable {kb}

theorem mem_foldr_union {α : Type*} [DecidableEq α] (l : List (Finset α)) (x : α) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons s t ih => simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons,
      exists_eq_or_imp]

@[simp] theorem isSubclassOfT_closureTable (a b : Qid) :
    kb.isSubclassOfT kb.closureTable a b = kb.isSubclassOf a b := by
  simp [isSubclassOfT, isSubclassOf]

@[simp] theorem isInstanceOfT_closureTable (a c : Qid) :
    kb.isInstanceOfT kb.closureTable a c = kb.isInstanceOf a c := by
  rw [Bool.eq_iff_iff]
  simp only [isInstanceOfT, instClosureT, isInstanceOf, decide_eq_true_eq, List.any_eq_true,
    isSubclassOf, mem_foldr_union, List.mem_map, closureLookup_closureTable]
  constructor
  · rintro ⟨s, ⟨d, hd, rfl⟩, hc⟩
    exact ⟨d, hd, by simpa using hc⟩
  · rintro ⟨d, hd, hc⟩
    exact ⟨_, ⟨d, hd, rfl⟩, by simpa using hc⟩

@[simp] theorem superclassesOfLT_eq (a : Qid) :
    kb.superclassesOfLT kb.closureTable a = kb.superclassesOfL a := by
  simp [superclassesOfLT, superclassesOfL, isSubclassOf]

@[simp] theorem classesOfT_eq (a : Qid) :
    kb.classesOfT kb.closureTable a = kb.classesOf a := by
  simp only [classesOfT, classesOf]
  refine List.filter_congr fun c _ => ?_
  have := isInstanceOfT_closureTable (kb := kb) a c
  simp only [isInstanceOfT] at this
  simp [this]

/-! ### The validator, in one pass -/

variable (kb)

/-- Acyclicity of the class hierarchy, checked against a single closure table. -/
def acyclicFast : Bool :=
  let T := kb.closureTable
  kb.items.all fun a => kb.items.all fun b =>
    !(kb.isSubclassOfT T a b && kb.isSubclassOfT T b a) || a == b

/-- Disjointness, checked against a single closure table. -/
def disjointOkFast : Bool :=
  let T := kb.closureTable
  kb.disj.all fun p => kb.items.all fun a =>
    !(kb.isInstanceOfT T a p.1 && kb.isInstanceOfT T a p.2)

/-- The full validity check, in one pass over a closure table. -/
def validFast : Bool := kb.wellFormed && kb.levelsOk && kb.acyclicFast && kb.disjointOkFast

variable {kb}

@[simp] theorem acyclicFast_eq : kb.acyclicFast = kb.acyclic := by
  simp [acyclicFast, acyclic]

@[simp] theorem disjointOkFast_eq : kb.disjointOkFast = kb.disjointOk := by
  simp [disjointOkFast, disjointOk]

/-- **The fast validator is the validator.** -/
@[simp] theorem validFast_eq : kb.validFast = kb.valid := by
  simp [validFast, valid]

/-! ### The diagnostic report, in one pass -/

variable (kb)

/-- Cycles in the class hierarchy, found against a single closure table. -/
def cycleIssuesFast : List Issue :=
  let T := kb.closureTable
  ((kb.items.product kb.items).filter
    (fun p => kb.isSubclassOfT T p.1 p.2 && kb.isSubclassOfT T p.2 p.1 && p.1 != p.2)).map
    (fun p => Issue.subclassCycle p.1 p.2)

/-- Instances of declared disjoint classes, found against a single closure table. -/
def disjointIssuesFast : List Issue :=
  let T := kb.closureTable
  ((kb.disj.product kb.items).filter
    (fun p => kb.isInstanceOfT T p.2 p.1.1 && kb.isInstanceOfT T p.2 p.1.2)).map
    (fun p => Issue.disjointViolation p.1.1 p.1.2 p.2)

/-- The full error report, computed in one pass over a closure table. -/
def errorsFast : List Issue :=
  kb.danglingSubIssues ++ kb.danglingInstIssues ++ kb.danglingDisjIssues ++
    kb.levelInstIssues ++ kb.levelSubIssues ++ kb.cycleIssuesFast ++ kb.disjointIssuesFast

variable {kb}

@[simp] theorem cycleIssuesFast_eq : kb.cycleIssuesFast = kb.cycleIssues := by
  simp [cycleIssuesFast, cycleIssues]

@[simp] theorem disjointIssuesFast_eq : kb.disjointIssuesFast = kb.disjointIssues := by
  simp [disjointIssuesFast, disjointIssues]

/-- **The fast report is the report.** -/
@[simp] theorem errorsFast_eq : kb.errorsFast = kb.errors := by
  simp [errorsFast, errors]

/-- The fast report is empty exactly when the knowledge base is valid. -/
theorem errorsFast_eq_nil_iff_valid : kb.errorsFast = [] ↔ kb.valid = true := by
  rw [errorsFast_eq, errors_eq_nil_iff_valid]

/-! ### Entailment, in one pass -/

variable (kb)

/-- `kb.EntailsT kb'` checks, against a single closure table for `kb`, that every
statement of `kb'` is derivable in `kb`. -/
def EntailsT (kb' : KB) : Bool :=
  let T := kb.closureTable
  kb'.sub.all (fun p => kb.isSubclassOfT T p.1 p.2) &&
    kb'.inst.all (fun p => kb.isInstanceOfT T p.1 p.2)

/-- `kb.EntailsAllT kbs` checks all of `kbs` at once, building the closure table
of `kb` only once. -/
def EntailsAllT (kbs : List KB) : Bool :=
  let T := kb.closureTable
  kbs.all fun kb' =>
    kb'.sub.all (fun p => kb.isSubclassOfT T p.1 p.2) &&
      kb'.inst.all (fun p => kb.isInstanceOfT T p.1 p.2)

variable {kb}

@[simp] theorem EntailsT_eq (kb' : KB) : kb.EntailsT kb' = kb.Entails kb' := by
  simp [EntailsT, Entails]

/-- **Checking many bases in one pass is checking each of them.** -/
@[simp] theorem EntailsAllT_eq (kbs : List KB) :
    kb.EntailsAllT kbs = kbs.all (fun kb' => kb.Entails kb') := by
  simp [EntailsAllT, Entails]

/-! ### Instances and metaclasses, in one pass -/

variable (kb)

/-- The declared instances of a class, answered from a table. -/
def instancesOfT (T : List (Qid × Finset Qid)) (c : Qid) : List Qid :=
  kb.items.filter fun a => kb.isInstanceOfT T a c

/-- Whether a class has instances, answered from a table. -/
def hasInstanceBT (T : List (Qid × Finset Qid)) (c : Qid) : Bool :=
  !(kb.instancesOfT T c).isEmpty

/-- Whether an item is a metaclass, answered from a table. -/
def isMetaclassBT (T : List (Qid × Finset Qid)) (c : Qid) : Bool :=
  (kb.instancesOfT T c).any fun a => kb.hasInstanceBT T a

variable {kb}

@[simp] theorem instancesOfT_eq (c : Qid) :
    kb.instancesOfT kb.closureTable c = kb.instancesOf c := by
  simp [instancesOfT, instancesOf]

@[simp] theorem hasInstanceBT_eq (c : Qid) :
    kb.hasInstanceBT kb.closureTable c = kb.hasInstanceB c := by
  simp [hasInstanceBT, hasInstanceB]

@[simp] theorem isMetaclassBT_eq (c : Qid) :
    kb.isMetaclassBT kb.closureTable c = kb.isMetaclassB c := by
  simp [isMetaclassBT, isMetaclassB]

/-! ### Fact construction, in one pass -/

variable (kb)

/-- The derivable but unasserted `subclass of` statements, in one pass over a
closure table. -/
def newSubLFast : List (Qid × Qid) :=
  let T := kb.closureTable
  (kb.items.flatMap fun a => (kb.superclassesOfLT T a).map fun b => (a, b)).filter
    fun p => (p.1 != p.2) && !kb.sub.contains p

/-- The derivable but unasserted `instance of` statements, in one pass over a
closure table. -/
def newInstLFast : List (Qid × Qid) :=
  let T := kb.closureTable
  (kb.items.flatMap fun a => (kb.classesOfT T a).map fun c => (a, c)).filter
    fun p => !kb.inst.contains p

/-- Saturation, in one pass over a closure table. -/
def saturateFast : KB := { kb with sub := kb.sub ++ kb.newSubLFast, inst := kb.inst ++ kb.newInstLFast }

variable {kb}

@[simp] theorem newSubLFast_eq : kb.newSubLFast = kb.newSubL := by
  simp [newSubLFast, newSubL]

@[simp] theorem newInstLFast_eq : kb.newInstLFast = kb.newInstL := by
  simp [newInstLFast, newInstL]

/-- **The fast saturation is the saturation.** -/
@[simp] theorem saturateFast_eq : kb.saturateFast = kb.saturate := by
  simp [saturateFast, saturate]

end KB
end Wikidata
