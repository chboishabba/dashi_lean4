import RequestProject.Engine

/-!
# Redundant `subclass of` statements, and their lossless removal

A recurring clean-up task of *Wikidata:WikiProject Ontology* is the removal of
**redundant `subclass of` (P279) statements**: a direct statement `a P279 b` is
redundant when `b` is already reachable from `a` through some other class `c`, so
that the statement adds nothing to the derived hierarchy.

This file makes that precise and proves the clean-up **lossless**:

* `Wikidata.KB.isRedundantSubB` decides redundancy of a statement;
* `Wikidata.KB.dropSub` deletes a statement;
* `Wikidata.KB.dropSub_isSubclassOf` and `Wikidata.KB.dropSub_isInstanceOf`: after
  deleting a redundant statement the engine answers **exactly** the same subclass
  and instance queries as before — nothing is lost and nothing is gained;
* `Wikidata.KB.dropSub_valid`: validity is preserved, so the pruned base is still a
  Wikidata ontology;
* `Wikidata.KB.dropSub_length_lt`: the base gets strictly smaller, so repeated
  pruning terminates.

The combinatorial core is stated for an arbitrary relation
(`Wikidata.EdgeRemoval.reflTransGen_iff_of_redundant`): deleting one edge of an
antisymmetric relation that is "shortcut" by a detour does not change its
reflexive–transitive closure. Antisymmetry is what makes this true — in a cyclic
graph the detour may itself run through the deleted edge.
-/

namespace Wikidata

/-! ## Deleting one edge from a relation -/

namespace EdgeRemoval

variable {α : Type*} {R R' : α → α → Prop} {a b : α}

/-- The hypothesis relating `R'` to `R`: `R'` is `R` with the edge `(a, b)` deleted. -/
def IsDeletion (R R' : α → α → Prop) (a b : α) : Prop :=
  ∀ x y, R' x y ↔ (R x y ∧ ¬(x = a ∧ y = b))

theorem le_of_isDeletion (h : IsDeletion R R' a b) {x y : α} (hxy : R' x y) : R x y :=
  ((h x y).1 hxy).1

theorem reflTransGen_mono_of_isDeletion (h : IsDeletion R R' a b) {x y : α}
    (hxy : Relation.ReflTransGen R' x y) : Relation.ReflTransGen R x y :=
  Relation.ReflTransGen.mono (fun _ _ hst => le_of_isDeletion h hst) hxy

/-- A path that never reaches `a` never uses an edge out of `a`, so it survives the
deletion. -/
theorem reflTransGen_of_not_reach (h : IsDeletion R R' a b) {x y : α}
    (hxy : Relation.ReflTransGen R x y) (hx : ¬ Relation.ReflTransGen R x a) :
    Relation.ReflTransGen R' x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxw hwy ih =>
      refine Relation.ReflTransGen.tail ih ((h _ _).2 ⟨hwy, ?_⟩)
      rintro ⟨rfl, rfl⟩
      exact hx hxw

/-- **The detour survives the deletion.** If `a` has an edge to some `c` distinct from
`a` and from `b`, and `b` is reachable from `c`, then `b` is still reachable from `a`
after deleting the edge `(a, b)` — provided the reachability relation is
antisymmetric. -/
theorem reflTransGen_of_redundant (h : IsDeletion R R' a b)
    (hanti : ∀ {x y : α}, Relation.ReflTransGen R x y → Relation.ReflTransGen R y x → x = y)
    {c : α} (hac : R a c) (hca : c ≠ a) (hcb' : c ≠ b)
    (hcb : Relation.ReflTransGen R c b) : Relation.ReflTransGen R' a b := by
  have hnot : ¬ Relation.ReflTransGen R c a := fun hx =>
    hca (hanti hx (Relation.ReflTransGen.single hac))
  refine Relation.ReflTransGen.head ((h _ _).2 ⟨hac, ?_⟩)
    (reflTransGen_of_not_reach h hcb hnot)
  rintro ⟨-, rfl⟩
  exact hcb' rfl

/-- **Deleting a redundant edge does not change reachability.** -/
theorem reflTransGen_iff_of_redundant (h : IsDeletion R R' a b)
    (hanti : ∀ {x y : α}, Relation.ReflTransGen R x y → Relation.ReflTransGen R y x → x = y)
    {c : α} (hac : R a c) (hca : c ≠ a) (hcb' : c ≠ b)
    (hcb : Relation.ReflTransGen R c b) (x y : α) :
    Relation.ReflTransGen R' x y ↔ Relation.ReflTransGen R x y := by
  refine ⟨reflTransGen_mono_of_isDeletion h, fun hxy => ?_⟩
  have step : ∀ u v : α, R u v → Relation.ReflTransGen R' u v := by
    intro u v huv
    by_cases hab : u = a ∧ v = b
    · obtain ⟨rfl, rfl⟩ := hab
      exact reflTransGen_of_redundant h hanti hac hca hcb' hcb
    · exact Relation.ReflTransGen.single ((h _ _).2 ⟨huv, hab⟩)
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hwy ih => exact ih.trans (step _ _ hwy)

end EdgeRemoval

namespace KB

/-! ## Redundant statements of a knowledge base -/

/-- The knowledge base with all copies of the `subclass of` statement `e` deleted. -/
def dropSub (kb : KB) (e : Qid × Qid) : KB :=
  { kb with sub := kb.sub.filter (fun r => r != e) }

/-- Decides whether a `subclass of` statement is **redundant**: it is asserted, and its
value is already reachable from its subject through a different direct superclass. -/
def isRedundantSubB (kb : KB) (e : Qid × Qid) : Bool :=
  (e ∈ kb.sub) &&
    kb.items.any (fun c =>
      (c != e.1) && (c != e.2) && ((e.1, c) ∈ kb.sub) && kb.isSubclassOf c e.2)

/-- All redundant `subclass of` statements of a knowledge base. -/
def redundantSubL (kb : KB) : List (Qid × Qid) := kb.sub.filter (fun e => kb.isRedundantSubB e)

variable {kb : KB} {e : Qid × Qid}

@[simp] theorem dropSub_items : (kb.dropSub e).items = kb.items := rfl

@[simp] theorem dropSub_inst : (kb.dropSub e).inst = kb.inst := rfl

@[simp] theorem dropSub_disj : (kb.dropSub e).disj = kb.disj := rfl

@[simp] theorem dropSub_levels : (kb.dropSub e).levels = kb.levels := rfl

@[simp] theorem dropSub_levelOf (q : Qid) : (kb.dropSub e).levelOf q = kb.levelOf q := rfl

theorem dropSub_sub_subset {r : Qid × Qid} (hr : r ∈ (kb.dropSub e).sub) : r ∈ kb.sub :=
  (List.mem_filter.1 hr).1

theorem dropSub_Sub_iff {x y : Qid} :
    (kb.dropSub e).Sub x y ↔ (kb.Sub x y ∧ ¬(x = e.1 ∧ y = e.2)) := by
  simp [dropSub, Sub, List.mem_filter, Prod.ext_iff]

theorem dropSub_isDeletion (kb : KB) (e : Qid × Qid) :
    EdgeRemoval.IsDeletion kb.Sub (kb.dropSub e).Sub e.1 e.2 :=
  fun _ _ => dropSub_Sub_iff

theorem dropSub_wellFormed (h : kb.wellFormed = true) : (kb.dropSub e).wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨fun r hr => h.1.1 r (dropSub_sub_subset hr), fun r hr => h.1.2 r hr⟩,
    fun r hr => h.2 r hr⟩

theorem dropSub_levelsOk (h : kb.levelsOk = true) : (kb.dropSub e).levelsOk = true := by
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun r hr => h.1 r hr, fun r hr => h.2 r (dropSub_sub_subset hr)⟩

/-- Unfolding the redundancy check. -/
theorem isRedundantSubB_iff :
    kb.isRedundantSubB e = true ↔
      e ∈ kb.sub ∧ ∃ c ∈ kb.items, c ≠ e.1 ∧ c ≠ e.2 ∧ (e.1, c) ∈ kb.sub ∧
        kb.isSubclassOf c e.2 = true := by
  simp only [isRedundantSubB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨he, c, hc, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩; exact ⟨he, c, hc, h1, h2, h3, h4⟩
  · rintro ⟨he, c, hc, h1, h2, h3, h4⟩; exact ⟨he, c, hc, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

/-- **Removing a redundant `subclass of` statement is lossless**: the pruned base
derives exactly the same subclass facts. -/
theorem dropSub_isSubclassOf (hv : kb.valid = true) (hred : kb.isRedundantSubB e = true)
    (x y : Qid) : (kb.dropSub e).isSubclassOf x y = kb.isSubclassOf x y := by
  have hwf := valid_wellFormed hv
  obtain ⟨-, c, -, hca, hcb', hac, hcb⟩ := isRedundantSubB_iff.1 hred
  have hiff := EdgeRemoval.reflTransGen_iff_of_redundant (dropSub_isDeletion kb e)
    (fun {x y} h h' => subclass_antisymm hv h h') (c := c) hac hca hcb'
    ((isSubclassOf_iff hwf c e.2).1 hcb) x y
  rw [Bool.eq_iff_iff, isSubclassOf_iff (dropSub_wellFormed hwf) x y,
    isSubclassOf_iff hwf x y]
  exact hiff

/-- The pruned base derives exactly the same `instance of` facts. -/
theorem dropSub_isInstanceOf (hv : kb.valid = true) (hred : kb.isRedundantSubB e = true)
    (x c : Qid) : (kb.dropSub e).isInstanceOf x c = kb.isInstanceOf x c := by
  have hwf := valid_wellFormed hv
  rw [Bool.eq_iff_iff, isInstanceOf_iff (dropSub_wellFormed hwf) x c,
    isInstanceOf_iff hwf x c]
  have hsub : ∀ u v : Qid, Relation.ReflTransGen (kb.dropSub e).Sub u v ↔
      Relation.ReflTransGen kb.Sub u v := by
    intro u v
    rw [← isSubclassOf_iff (dropSub_wellFormed hwf) u v, ← isSubclassOf_iff hwf u v,
      dropSub_isSubclassOf hv hred u v]
  constructor
  · rintro ⟨d, hd, hdc⟩; exact ⟨d, hd, (hsub d c).1 hdc⟩
  · rintro ⟨d, hd, hdc⟩; exact ⟨d, hd, (hsub d c).2 hdc⟩

theorem dropSub_acyclic (hv : kb.valid = true) (hred : kb.isRedundantSubB e = true) :
    (kb.dropSub e).acyclic = true := by
  have hac := valid_acyclic hv
  simp only [acyclic, List.all_eq_true, dropSub_items] at hac ⊢
  intro a ha b hb
  rw [dropSub_isSubclassOf hv hred, dropSub_isSubclassOf hv hred]
  exact hac a ha b hb

theorem dropSub_disjointOk (hv : kb.valid = true) (hred : kb.isRedundantSubB e = true) :
    (kb.dropSub e).disjointOk = true := by
  have hd := valid_disjointOk hv
  simp only [disjointOk, List.all_eq_true, dropSub_items, dropSub_disj] at hd ⊢
  intro r hr a ha
  rw [dropSub_isInstanceOf hv hred, dropSub_isInstanceOf hv hred]
  exact hd r hr a ha

/-- **Pruning a redundant statement preserves validity**, so the result is again a
Wikidata ontology. -/
theorem dropSub_valid (hv : kb.valid = true) (hred : kb.isRedundantSubB e = true) :
    (kb.dropSub e).valid = true := by
  simp only [valid, Bool.and_eq_true]
  exact ⟨⟨⟨dropSub_wellFormed (valid_wellFormed hv), dropSub_levelsOk (valid_levelsOk hv)⟩,
    dropSub_acyclic hv hred⟩, dropSub_disjointOk hv hred⟩

/-- Pruning makes the base strictly smaller, so repeated pruning terminates. -/
theorem dropSub_length_lt (he : e ∈ kb.sub) : (kb.dropSub e).sub.length < kb.sub.length := by
  show (kb.sub.filter (fun r => r != e)).length < kb.sub.length
  rw [← List.countP_eq_length_filter]
  exact List.countP_lt_length_iff.2 ⟨e, he, by simp⟩

/-- Every statement listed as redundant really is. -/
theorem isRedundantSubB_of_mem_redundantSubL (h : e ∈ kb.redundantSubL) :
    kb.isRedundantSubB e = true := by
  simpa using (List.mem_filter.1 h).2

/-! ## A worked fragment

`Q5` (human) is a subclass of `Q215627` (person), which is a subclass of `Q35120`
(entity); the direct statement `Q5 P279 Q35120` adds nothing. -/

/-- A knowledge base with one redundant `subclass of` statement. -/
def redundantKB : KB where
  name := "redundant"
  items := [Qid.wd "Q42", Qid.wd "Q5", Qid.wd "Q215627", Qid.wd "Q35120"]
  levels := [(Qid.wd "Q5", 1), (Qid.wd "Q215627", 1), (Qid.wd "Q35120", 1)]
  sub := [(Qid.wd "Q5", Qid.wd "Q215627"), (Qid.wd "Q215627", Qid.wd "Q35120"),
          (Qid.wd "Q5", Qid.wd "Q35120")]
  inst := [(Qid.wd "Q42", Qid.wd "Q5")]

theorem redundantKB_valid : redundantKB.valid = true := by decide

/-- The linter finds exactly the shortcut statement. -/
theorem redundantKB_redundant :
    redundantKB.redundantSubL = [(Qid.wd "Q5", Qid.wd "Q35120")] := by decide

/-- The other two statements are not redundant. -/
theorem redundantKB_not_redundant :
    redundantKB.isRedundantSubB (Qid.wd "Q5", Qid.wd "Q215627") = false ∧
    redundantKB.isRedundantSubB (Qid.wd "Q215627", Qid.wd "Q35120") = false := by decide

/-- The pruned base is still valid and still derives `Q5 ⊑ Q35120` and
`Q42 : Q35120`. -/
theorem redundantKB_pruned :
    (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).valid = true ∧
    (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).isSubclassOf
      (Qid.wd "Q5") (Qid.wd "Q35120") = true ∧
    (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).isInstanceOf
      (Qid.wd "Q42") (Qid.wd "Q35120") = true := by decide

/-- Deleting a *non*-redundant statement does lose information: once the shortcut has
been pruned, dropping `Q215627 P279 Q35120` leaves a base that no longer knows that a
human is an entity. -/
theorem redundantKB_pruning_nonredundant_loses :
    ((redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).dropSub
      (Qid.wd "Q215627", Qid.wd "Q35120")).isSubclassOf
      (Qid.wd "Q5") (Qid.wd "Q35120") = false := by decide

end KB

end Wikidata
