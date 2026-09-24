import RequestProject.FastEval
import RequestProject.Cli.Codegen

/-!
# A defect report for downloaded Wikidata data

`Wikidata:WikiProject Ontology` is, in practice, a clean-up project: the work is
finding statements that should not be there and saying what to do about them.
`RequestProject.Diagnostics` already turns the validator into a list of
individually witnessed issues.  This file adds what is needed to run that report
over *large* downloaded fragments and to act on it in bulk.  Everything is
computed against **one** closure table (`KB.closureTable`), which is what makes
a base with a couple of thousand statements practical:

* `KB.redundantSubLFast` — the redundant `subclass of` statements
  (`KB.redundantSubLFast_eq`: it is `KB.redundantSubL`);
* `KB.cyclicItems` — the items that lie on a `subclass of` cycle
  (`KB.mem_cyclicItems`), and `KB.no_ontology_of_cyclicItems`: a base with one is
  modelled by no abstract `Wikidata.Ontology` at all, so a cycle is an error and
  not a matter of taste;
* `KB.instAndSubL` — the pairs a base asserts *both* `instance of` and `subclass
  of` for (`KB.mem_instAndSubL`), Wikidata's commonest class/instance confusion;
* `KB.defectCounts` — the three counts, from a single pass;
* `KB.pruneRedundant` — the base with *all* the redundant statements deleted at
  once.  Deleting one is always lossless (`KB.dropSub_isSubclassOf`), deleting
  all of them at once need not be — in a cyclic hierarchy every statement of a
  cycle looks redundant — so the tool checks: `KB.prunePreservesB` asks whether
  every deleted statement is still derivable, and `KB.pruneRedundant_lossless` /
  `KB.pruneRedundant_lossless_inst` turn a positive answer into the statement
  that *every* subclass and instance query is answered exactly as before.

`RequestProject.DefectReport` runs all of this over the downloaded corpus and
records what it finds.
-/

namespace Wikidata
namespace KB

variable (kb : KB)

/-! ### Redundant `subclass of` statements, quickly -/

/-- The direct superclasses of an item that are declared items themselves. -/
def directSupersL (a : Qid) : List Qid := (kb.supersL a).filter (fun c => c ∈ kb.items)

/-- Redundancy of a `subclass of` statement, decided against a closure table:
the statement is asserted, and its value is already reachable from its subject
through some *other* direct superclass. -/
def isRedundantSubT (T : List (Qid × Finset Qid)) (e : Qid × Qid) : Bool :=
  (e ∈ kb.sub) &&
    (kb.directSupersL e.1).any fun c => (c != e.1) && (c != e.2) && kb.isSubclassOfT T c e.2

/-- All redundant `subclass of` statements, against a given closure table. -/
def redundantSubLT (T : List (Qid × Finset Qid)) : List (Qid × Qid) :=
  kb.sub.filter (kb.isRedundantSubT T)

/-- All redundant `subclass of` statements, found in one pass over the closure
table. -/
def redundantSubLFast : List (Qid × Qid) := kb.redundantSubLT kb.closureTable

variable {kb}

theorem mem_supersL {a c : Qid} : c ∈ kb.supersL a ↔ (a, c) ∈ kb.sub := by
  simp only [supersL, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hmem, hx⟩, rfl⟩
    simpa using hx ▸ hmem
  · intro h
    exact ⟨(a, c), ⟨h, rfl⟩, rfl⟩

theorem mem_directSupersL {a c : Qid} :
    c ∈ kb.directSupersL a ↔ (a, c) ∈ kb.sub ∧ c ∈ kb.items := by
  simp [directSupersL, List.mem_filter, mem_supersL]

/-- The fast redundancy check is the redundancy check. -/
@[simp] theorem isRedundantSubT_closureTable (e : Qid × Qid) :
    kb.isRedundantSubT kb.closureTable e = kb.isRedundantSubB e := by
  rw [Bool.eq_iff_iff]
  simp only [isRedundantSubT, isRedundantSubB, isSubclassOfT_closureTable, Bool.and_eq_true,
    List.any_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, mem_directSupersL]
  refine and_congr_right fun _ => ?_
  tauto

/-- **The fast list of redundant statements is the list of redundant
statements.** -/
@[simp] theorem redundantSubLFast_eq : kb.redundantSubLFast = kb.redundantSubL := by
  rw [redundantSubLFast, redundantSubLT, redundantSubL]
  exact List.filter_congr fun e _ => by rw [isRedundantSubT_closureTable]

/-! ### Cycles in the class hierarchy -/

variable (kb)

/-- The items that lie on a `subclass of` cycle, read off a closure table: the
items `a` for which some other item of the table is both above and below `a`. -/
def cyclicItemsT (T : List (Qid × Finset Qid)) : List Qid :=
  T.filterMap fun p =>
    if T.any (fun q => (p.1 != q.1) && (q.1 ∈ p.2) && (p.1 ∈ q.2)) then some p.1 else none

/-- The declared items that lie on a `subclass of` cycle. -/
def cyclicItems : List Qid := cyclicItemsT kb.closureTable

variable {kb}

theorem mem_closureTable {p : Qid × Finset Qid} :
    p ∈ kb.closureTable ↔ p.1 ∈ kb.items ∧ p.2 = kb.superclasses p.1 := by
  obtain ⟨a, S⟩ := p
  simp only [closureTable, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem mem_cyclicItems {a : Qid} :
    a ∈ kb.cyclicItems ↔
      a ∈ kb.items ∧ ∃ b ∈ kb.items, a ≠ b ∧
        kb.isSubclassOf a b = true ∧ kb.isSubclassOf b a = true := by
  constructor
  · intro ha
    rw [cyclicItems, cyclicItemsT, List.mem_filterMap] at ha
    obtain ⟨p, hp, hif⟩ := ha
    obtain ⟨hp1, hp2⟩ := mem_closureTable.1 hp
    split at hif
    · rename_i hcond
      obtain rfl : p.1 = a := Option.some.inj hif
      obtain ⟨q, hq, hqcond⟩ := List.any_eq_true.1 hcond
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hqcond
      obtain ⟨⟨hne, hqa⟩, haq⟩ := hqcond
      obtain ⟨hq1, hq2⟩ := mem_closureTable.1 hq
      refine ⟨hp1, q.1, hq1, hne, ?_, ?_⟩
      · simpa [isSubclassOf, hp2] using hqa
      · simpa [isSubclassOf, hq2] using haq
    · exact absurd hif (by simp)
  · rintro ⟨ha, b, hb, hne, h1, h2⟩
    rw [cyclicItems, cyclicItemsT, List.mem_filterMap]
    refine ⟨(a, kb.superclasses a), mem_closureTable.2 ⟨ha, rfl⟩, ?_⟩
    rw [if_pos]
    refine List.any_eq_true.2 ⟨(b, kb.superclasses b), mem_closureTable.2 ⟨hb, rfl⟩, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨hne, by simpa [isSubclassOf] using h1⟩, by simpa [isSubclassOf] using h2⟩

/-- **A cycle is an error, not a matter of taste**: no abstract Wikidata
ontology has exactly the `subclass of` statements of a base with a cyclic item,
because the class hierarchy of an `Ontology` is antisymmetric. -/
theorem no_ontology_of_cyclicItems (hwf : kb.wellFormed = true) {a : Qid}
    (ha : a ∈ kb.cyclicItems) (O : Ontology Qid) (hO : O.P279 = kb.Sub) : False := by
  obtain ⟨-, b, -, hne, h1, h2⟩ := mem_cyclicItems.1 ha
  exact hne (O.P279_antisymm (hO ▸ (isSubclassOf_iff hwf a b).1 h1)
    (hO ▸ (isSubclassOf_iff hwf b a).1 h2))

/-! ### `instance of` and `subclass of` asserted between the same two items -/

variable (kb)

/-- The pairs the base asserts both `instance of` (P31) and `subclass of` (P279)
for.  At most one of the two statements can be intended: `a` is either a member
of the class `c` or a kind of it. -/
def instAndSubL : List (Qid × Qid) := kb.inst.filter fun p => p ∈ kb.sub

/-- The three counts of the defect report, from a single pass over the closure
table: items on a cycle, redundant `subclass of` statements, and pairs asserted
both ways. -/
def defectCounts : ℕ × ℕ × ℕ :=
  let T := kb.closureTable
  ((cyclicItemsT T).length, (kb.redundantSubLT T).length, kb.instAndSubL.length)

variable {kb}

theorem defectCounts_eq :
    kb.defectCounts =
      (kb.cyclicItems.length, kb.redundantSubL.length, kb.instAndSubL.length) := by
  rw [defectCounts, ← redundantSubLFast_eq, redundantSubLFast, cyclicItems]

theorem mem_instAndSubL {p : Qid × Qid} :
    p ∈ kb.instAndSubL ↔ p ∈ kb.inst ∧ p ∈ kb.sub := by
  simp [instAndSubL, List.mem_filter]

/-- A confused pair really is derived twice over: the subject is both an
instance of the class and a subclass of it. -/
theorem instAndSubL_derives (hwf : kb.wellFormed = true) {p : Qid × Qid}
    (hp : p ∈ kb.instAndSubL) :
    kb.isInstanceOf p.1 p.2 = true ∧ kb.isSubclassOf p.1 p.2 = true := by
  obtain ⟨hinst, hsub⟩ := mem_instAndSubL.1 hp
  exact ⟨isInstanceOf_of_inst hinst,
    (isSubclassOf_iff hwf _ _).2 (Relation.ReflTransGen.single hsub)⟩

/-! ### Deleting all the redundant statements at once -/

variable (kb)

/-- The base with every redundant `subclass of` statement deleted. -/
def pruneRedundant : KB :=
  let T := kb.closureTable
  { kb with sub := kb.sub.filter fun e => !kb.isRedundantSubT T e }

/-- The check that the bulk deletion lost nothing: every deleted statement is
still derivable in the pruned base.  Deleting one redundant statement is always
lossless; deleting all of them at once need not be, when the hierarchy has
cycles, so this is checked rather than assumed. -/
def prunePreservesB : Bool :=
  let P := kb.pruneRedundant
  let T := P.closureTable
  kb.sub.all fun e => P.isSubclassOfT T e.1 e.2

variable {kb}

@[simp] theorem pruneRedundant_items : kb.pruneRedundant.items = kb.items := rfl

@[simp] theorem pruneRedundant_inst : kb.pruneRedundant.inst = kb.inst := rfl

@[simp] theorem pruneRedundant_disj : kb.pruneRedundant.disj = kb.disj := rfl

theorem pruneRedundant_sub_subset {e : Qid × Qid} (he : e ∈ kb.pruneRedundant.sub) :
    e ∈ kb.sub :=
  (List.mem_filter.1 he).1

theorem pruneRedundant_wellFormed (hwf : kb.wellFormed = true) :
    kb.pruneRedundant.wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf ⊢
  exact ⟨⟨fun e he => hwf.1.1 e (pruneRedundant_sub_subset he), hwf.1.2⟩, hwf.2⟩

/-- What the pruned base derives, the original derives: it has fewer
statements. -/
theorem pruneRedundant_isSubclassOf_le (hwf : kb.wellFormed = true) {a b : Qid}
    (h : kb.pruneRedundant.isSubclassOf a b = true) : kb.isSubclassOf a b = true := by
  refine (isSubclassOf_iff hwf a b).2 ?_
  refine Relation.ReflTransGen.mono ?_ ((isSubclassOf_iff (pruneRedundant_wellFormed hwf) a b).1 h)
  intro x y hxy
  exact pruneRedundant_sub_subset hxy

/-- **The bulk deletion is lossless when the check passes**: the pruned base
answers every `subclass of` query exactly as the original does. -/
theorem pruneRedundant_lossless (hwf : kb.wellFormed = true) (h : kb.prunePreservesB = true)
    (a b : Qid) : kb.pruneRedundant.isSubclassOf a b = kb.isSubclassOf a b := by
  have hstep : ∀ e ∈ kb.sub, kb.pruneRedundant.isSubclassOf e.1 e.2 = true := by
    simp only [prunePreservesB, List.all_eq_true] at h
    intro e he
    simpa using h e he
  rw [Bool.eq_iff_iff]
  refine ⟨fun hp => pruneRedundant_isSubclassOf_le hwf hp, fun hk => ?_⟩
  have hchain := (isSubclassOf_iff hwf a b).1 hk
  clear hk
  refine (isSubclassOf_iff (pruneRedundant_wellFormed hwf) a b).2 ?_
  induction hchain with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact ih.trans ((isSubclassOf_iff (pruneRedundant_wellFormed hwf) _ _).1 (hstep _ hyz))

/-- … and every `instance of` query too. -/
theorem pruneRedundant_lossless_inst (hwf : kb.wellFormed = true) (h : kb.prunePreservesB = true)
    (a c : Qid) : kb.pruneRedundant.isInstanceOf a c = kb.isInstanceOf a c := by
  simp only [isInstanceOf, directClassesL, pruneRedundant_inst]
  exact List.any_congr rfl fun d => pruneRedundant_lossless hwf h d c

end KB
end Wikidata
