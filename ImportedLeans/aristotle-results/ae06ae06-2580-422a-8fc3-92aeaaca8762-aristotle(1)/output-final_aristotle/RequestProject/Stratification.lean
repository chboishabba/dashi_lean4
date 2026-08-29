import RequestProject.Engine

/-!
# Stratifying the class hierarchy: height, strata and linear extensions

The `subclass of` (P279) hierarchy of a validated knowledge base is a finite
partial order (`RequestProject.Core`).  This file makes its *shape* explicit and
computable.

To each item is attached its **height**

    height q = number of superclasses of q (itself included),

which is computed by the engine.  The results are:

* a class has strictly greater height than each of its proper superclasses
  (`height_lt_of_proper`), so `height` is a **linear extension** of the subclass
  order: it maps the hierarchy into `ℕ` reversing the order strictly
  (`exists_linear_extension`);
* consequently the strict superclass relation is **well founded**
  (`properSuper_wf`): every ascent through the hierarchy terminates, which is what
  makes inheritance reasoning by induction on classes legitimate;
* the height of an item is bounded by the size of the knowledge base
  (`height_le_card`), so every strictly ascending chain of classes has fewer
  members than the base has items (`chain_lt_card`);
* the items split into **strata** by height (`stratum`), each item lying in
  exactly one, and every P279 edge going from a stratum to a strictly lower one
  (`height_lt_of_sub`).

Nothing here needs a new Wikidata notion: it is the structure theory of the
hierarchy the engine already computes.
-/

namespace Wikidata
namespace KB

variable {kb : KB}

/-! ### Height -/

theorem mem_superclasses_iff {a b : Qid} :
    b ∈ kb.superclasses a ↔ kb.isSubclassOf a b = true := by
  simp [isSubclassOf]

theorem self_mem_superclasses (kb : KB) (a : Qid) : a ∈ kb.superclasses a :=
  mem_superclasses_iff.2 (isSubclassOf_refl kb a)

/-- The **height** of an item: the number of its superclasses, itself included.
An item with no proper superclass has height `1`. -/
def height (kb : KB) (q : Qid) : ℕ := (kb.superclasses q).card

theorem height_pos (kb : KB) (a : Qid) : 0 < kb.height a :=
  Finset.card_pos.2 ⟨a, self_mem_superclasses kb a⟩

/-- Superclass sets shrink as one goes up the hierarchy. -/
theorem superclasses_subset_of_isSubclassOf (hwf : kb.wellFormed = true) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) : kb.superclasses b ⊆ kb.superclasses a := by
  intro x hx
  exact mem_superclasses_iff.2 (isSubclassOf_trans hwf hab (mem_superclasses_iff.1 hx))

/-- A proper superclass has *strictly* fewer superclasses. -/
theorem superclasses_ssubset_of_proper (hv : kb.valid = true) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) (hne : a ≠ b) :
    kb.superclasses b ⊂ kb.superclasses a := by
  have hwf := valid_wellFormed hv
  refine ⟨superclasses_subset_of_isSubclassOf hwf hab, fun hsub => ?_⟩
  have ha : a ∈ kb.superclasses b := hsub (self_mem_superclasses kb a)
  have hba : kb.isSubclassOf b a = true := mem_superclasses_iff.1 ha
  exact hne (subclass_antisymm hv ((isSubclassOf_iff hwf a b).1 hab)
    ((isSubclassOf_iff hwf b a).1 hba))

/-- **Height is a linear extension of the subclass order**: a proper subclass is
strictly higher. -/
theorem height_lt_of_proper (hv : kb.valid = true) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) (hne : a ≠ b) : kb.height b < kb.height a :=
  Finset.card_lt_card (superclasses_ssubset_of_proper hv hab hne)

/-- Every P279 edge of a validated base drops the height strictly, unless it is a
loop at a single item. -/
theorem height_lt_of_sub (hv : kb.valid = true) {a b : Qid} (hab : kb.Sub a b) (hne : a ≠ b) :
    kb.height b < kb.height a :=
  height_lt_of_proper hv
    ((isSubclassOf_iff (valid_wellFormed hv) a b).2 (Relation.ReflTransGen.single hab)) hne

/-- Two items of the same height are comparable only if they are equal: the
hierarchy has no "horizontal" subclass edges. -/
theorem eq_of_isSubclassOf_of_height_eq (hv : kb.valid = true) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) (h : kb.height a = kb.height b) : a = b := by
  by_contra hne
  have := height_lt_of_proper hv hab hne
  omega

/-- The subclass order of a validated knowledge base admits a linear extension into
the natural numbers: `height` reverses it strictly. -/
theorem exists_linear_extension (hv : kb.valid = true) :
    ∃ f : Qid → ℕ, ∀ a b : Qid, kb.isSubclassOf a b = true → a ≠ b → f b < f a :=
  ⟨kb.height, fun _ _ hab hne => height_lt_of_proper hv hab hne⟩

/-! ### Well-foundedness -/

/-- `ProperSuper kb a b` : `a` is a proper superclass of `b`. -/
def ProperSuper (kb : KB) (a b : Qid) : Prop := kb.isSubclassOf b a = true ∧ b ≠ a

/-- **Ascending the class hierarchy terminates.** Since height strictly drops at
each step upwards, the proper-superclass relation of a validated knowledge base is
well founded, so properties of classes may be proved by induction on superclasses. -/
theorem properSuper_wf (hv : kb.valid = true) : WellFounded kb.ProperSuper := by
  refine Subrelation.wf (r := InvImage (· < ·) kb.height) ?_ (InvImage.wf kb.height Nat.lt_wfRel.wf)
  rintro a b ⟨hba, hne⟩
  exact height_lt_of_proper hv hba hne

/-! ### Bounds -/

theorem superclasses_subset_allF (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∈ kb.items) :
    kb.superclasses a ⊆ kb.allF :=
  Reach.iter_subset_all kb.supers (supers_subset_all hwf) (mem_allF.2 ha) _

/-- The height of an item is bounded by the size of the knowledge base. -/
theorem height_le_card (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∈ kb.items) :
    kb.height a ≤ kb.allF.card :=
  Finset.card_le_card (superclasses_subset_allF hwf ha)

/-- Along a chain of proper subclass steps the height drops by at least one per
step. -/
theorem height_add_le (hv : kb.valid = true) (f : ℕ → Qid) (n : ℕ)
    (hchain : ∀ i < n, kb.isSubclassOf (f i) (f (i + 1)) = true ∧ f i ≠ f (i + 1)) :
    kb.height (f n) + n ≤ kb.height (f 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk := hchain k (Nat.lt_succ_self k)
      have hlt : kb.height (f (k + 1)) < kb.height (f k) :=
        height_lt_of_proper hv hk.1 hk.2
      have := ih (fun i hi => hchain i (Nat.lt_succ_of_lt hi))
      omega

/-- **Chains are short**: a strictly ascending chain of classes in a validated
knowledge base has fewer steps than the base has items. -/
theorem chain_lt_card (hv : kb.valid = true) (f : ℕ → Qid) (n : ℕ) (hf : f 0 ∈ kb.items)
    (hchain : ∀ i < n, kb.isSubclassOf (f i) (f (i + 1)) = true ∧ f i ≠ f (i + 1)) :
    n < kb.allF.card := by
  have h1 := height_add_le hv f n hchain
  have h2 := height_le_card (valid_wellFormed hv) hf
  have h3 := height_pos kb (f n)
  omega

/-! ### A topological order -/

/-- The items sorted by decreasing height: an executable **topological order** of
the class hierarchy, in which every class precedes its proper superclasses. -/
def topoSort (kb : KB) : List Qid :=
  kb.items.mergeSort (fun a b => decide (kb.height b ≤ kb.height a))

theorem topoSort_perm (kb : KB) : (kb.topoSort).Perm kb.items := List.mergeSort_perm _ _

theorem mem_topoSort {a : Qid} : a ∈ kb.topoSort ↔ a ∈ kb.items := (topoSort_perm kb).mem_iff

theorem topoSort_pairwise (kb : KB) :
    List.Pairwise (fun a b => kb.height b ≤ kb.height a) kb.topoSort := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (kb.height b ≤ kb.height a))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) kb.items
  simpa [topoSort] using h

/-- **The sort really is a topological order**: a class occurs strictly before each
of its proper superclasses. -/
theorem idxOf_lt_idxOf_of_proper (hv : kb.valid = true) {a b : Qid} (ha : a ∈ kb.items)
    (hb : b ∈ kb.items) (hab : kb.isSubclassOf a b = true) (hne : a ≠ b) :
    kb.topoSort.idxOf a < kb.topoSort.idxOf b := by
  have hia : kb.topoSort.idxOf a < kb.topoSort.length :=
    List.idxOf_lt_length_iff.2 (mem_topoSort.2 ha)
  have hib : kb.topoSort.idxOf b < kb.topoSort.length :=
    List.idxOf_lt_length_iff.2 (mem_topoSort.2 hb)
  have hheight : kb.height b < kb.height a := height_lt_of_proper hv hab hne
  have h1 : kb.topoSort[kb.topoSort.idxOf a] = a := List.getElem_idxOf hia
  have h2 : kb.topoSort[kb.topoSort.idxOf b] = b := List.getElem_idxOf hib
  rcases lt_trichotomy (kb.topoSort.idxOf a) (kb.topoSort.idxOf b) with hlt | heq | hgt
  · exact hlt
  · simp only [heq] at h1
    exact absurd (h1.symm.trans h2) hne
  · have := (List.pairwise_iff_getElem.1 (topoSort_pairwise kb)) _ _ hib hia hgt
    rw [h1, h2] at this
    omega

/-! ### Strata -/

/-- The items of a given height. -/
def stratum (kb : KB) (n : ℕ) : List Qid := kb.items.filter (fun q => kb.height q == n)

theorem mem_stratum_iff {n : ℕ} {q : Qid} :
    q ∈ kb.stratum n ↔ q ∈ kb.items ∧ kb.height q = n := by
  simp [stratum, List.mem_filter]

/-- Every item lies in exactly one stratum. -/
theorem mem_stratum_unique {n m : ℕ} {q : Qid} (hn : q ∈ kb.stratum n) (hm : q ∈ kb.stratum m) :
    n = m := by
  rw [mem_stratum_iff] at hn hm
  exact hn.2.symm.trans hm.2

theorem mem_stratum_height {q : Qid} (hq : q ∈ kb.items) : q ∈ kb.stratum (kb.height q) :=
  mem_stratum_iff.2 ⟨hq, rfl⟩

/-- There is no stratum `0`: every item has height at least one. -/
theorem stratum_zero (kb : KB) : kb.stratum 0 = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun q hq => ?_
  have h0 := (mem_stratum_iff.1 hq).2
  have := height_pos kb q
  omega

/-- A P279 edge always leads to a strictly lower stratum. -/
theorem stratum_lt_of_sub (hv : kb.valid = true) {a b : Qid} {m n : ℕ} (hab : kb.Sub a b)
    (hne : a ≠ b) (ha : a ∈ kb.stratum m) (hb : b ∈ kb.stratum n) : n < m := by
  rw [mem_stratum_iff] at ha hb
  rw [← ha.2, ← hb.2]
  exact height_lt_of_sub hv hab hne

end KB

/-! ## A worked fragment

A four-level hierarchy: `human` ⊑ `person` ⊑ `object` ⊑ `entity`, together with
`painting` ⊑ `object`.  The heights measure the distance to the top, so `human`
lies in stratum `4`, `painting` in stratum `3`, and the strata are computed. -/

namespace StratumExample

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- `entity` (Q35120), `object` (Q488383), `person` (Q215627), `human` (Q5) and
`painting` (Q3305213). -/
def tower : KB where
  name := "wd-strata"
  items := [Q "Q5", Q "Q215627", Q "Q488383", Q "Q35120", Q "Q3305213"]
  levels := [(Q "Q5", 1), (Q "Q215627", 1), (Q "Q488383", 1), (Q "Q35120", 1),
             (Q "Q3305213", 1)]
  sub := [(Q "Q5", Q "Q215627"), (Q "Q215627", Q "Q488383"), (Q "Q488383", Q "Q35120"),
          (Q "Q3305213", Q "Q488383")]

set_option maxRecDepth 100000 in
theorem tower_valid : tower.valid = true := by decide

set_option maxRecDepth 100000 in
/-- `human` has four superclasses (itself, person, object, entity). -/
theorem height_human : tower.height (Q "Q5") = 4 := by decide

set_option maxRecDepth 100000 in
theorem height_painting : tower.height (Q "Q3305213") = 3 := by decide

set_option maxRecDepth 100000 in
/-- The top of the hierarchy is the unique item of height one. -/
theorem stratum_one : tower.stratum 1 = [Q "Q35120"] := by decide

set_option maxRecDepth 100000 in
/-- `painting` and `person` sit at the same height, and are indeed incomparable. -/
theorem stratum_three : tower.stratum 3 = [Q "Q215627", Q "Q3305213"] := by decide

set_option maxRecDepth 100000 in
theorem painting_person_incomparable :
    tower.isSubclassOf (Q "Q3305213") (Q "Q215627") = false ∧
      tower.isSubclassOf (Q "Q215627") (Q "Q3305213") = false := by decide

set_option maxRecDepth 100000 in
/-- In the computed topological order `human` comes before `entity`, as the general
theorem `KB.idxOf_lt_idxOf_of_proper` guarantees for every proper subclass pair. -/
theorem human_before_entity :
    tower.topoSort.idxOf (Q "Q5") < tower.topoSort.idxOf (Q "Q35120") :=
  KB.idxOf_lt_idxOf_of_proper tower_valid (by decide) (by decide) (by decide) (by decide)

/-- Items of equal height are never related by `subclass of` — an instance of the
general theorem `KB.eq_of_isSubclassOf_of_height_eq`. -/
theorem person_ne_painting_of_subclass
    (h : tower.isSubclassOf (Q "Q215627") (Q "Q3305213") = true) : False := by
  have := KB.eq_of_isSubclassOf_of_height_eq tower_valid h (by decide)
  simp [Q] at this

end StratumExample

end Wikidata
