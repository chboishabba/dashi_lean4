import RequestProject.Engine

/-!
# Reasoning about other ontologies: import and entailment

`KB.merge` imports one knowledge base into another, and `KB.Entails kb kb'`
("`kb` entails `kb'`") is the computable check that every statement asserted by
`kb'` is *derivable* in `kb`.

The main results are:

* `KB.entails_subclass` / `KB.entails_instance`: entailment of the asserted
  statements automatically transfers all *derived* facts, so an entailing
  knowledge base answers every subclass and instance query at least as
  affirmatively as the entailed one;
* `KB.entails_refl`, `KB.entails_trans`: entailment is a preorder on well-formed
  knowledge bases;
* `KB.merge_entails_left` / `KB.merge_entails_right`: importing an ontology
  preserves everything it knew — nothing is lost by merging.

Validity, on the other hand, is *not* preserved by merging: two individually
valid ontologies can contradict each other. This is why `KB.valid` has to be
re-run on the merge; see `RequestProject.Examples`.
-/

namespace Wikidata
namespace KB

/-- Import one knowledge base into another. -/
def merge (kb kb' : KB) : KB where
  name := kb.name ++ " + " ++ kb'.name
  items := kb.items ++ kb'.items
  levels := kb.levels ++ kb'.levels
  sub := kb.sub ++ kb'.sub
  inst := kb.inst ++ kb'.inst
  disj := kb.disj ++ kb'.disj

/-- `kb.Entails kb'` checks that every statement asserted by `kb'` is derivable
in `kb`. -/
def Entails (kb kb' : KB) : Bool :=
  kb'.sub.all (fun p => kb.isSubclassOf p.1 p.2) &&
  kb'.inst.all (fun p => kb.isInstanceOf p.1 p.2)

variable {kb kb' kb'' : KB}

theorem entails_sub (h : kb.Entails kb' = true) {a b : Qid} (hab : kb'.Sub a b) :
    kb.isSubclassOf a b = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 (a, b) hab

theorem entails_inst (h : kb.Entails kb' = true) {a c : Qid} (hac : kb'.Inst a c) :
    kb.isInstanceOf a c = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 (a, c) hac

theorem reflTransGen_sub_of_entails (hwf : kb.wellFormed = true) (h : kb.Entails kb' = true)
    {a b : Qid} (hab : Relation.ReflTransGen kb'.Sub a b) :
    Relation.ReflTransGen kb.Sub a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
      exact ih.trans ((isSubclassOf_iff hwf _ _).1 (entails_sub h hxy))

/-- Entailment transfers *derived* subclass facts, not just asserted ones. -/
theorem entails_subclass (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (h : kb.Entails kb' = true) {a b : Qid} (hab : kb'.isSubclassOf a b = true) :
    kb.isSubclassOf a b = true :=
  (isSubclassOf_iff hwf a b).2
    (reflTransGen_sub_of_entails hwf h ((isSubclassOf_iff hwf' a b).1 hab))

/-- Entailment transfers *derived* instance facts. -/
theorem entails_instance (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (h : kb.Entails kb' = true) {a c : Qid} (hac : kb'.isInstanceOf a c = true) :
    kb.isInstanceOf a c = true := by
  obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf' a c).1 hac
  have h1 : kb.isInstanceOf a d = true := entails_inst h hd
  obtain ⟨e, he, hed⟩ := (isInstanceOf_iff hwf a d).1 h1
  refine (isInstanceOf_iff hwf a c).2 ⟨e, he, hed.trans ?_⟩
  have : kb.isSubclassOf d c = true :=
    entails_subclass hwf hwf' h ((isSubclassOf_iff hwf' d c).2 hdc)
  exact (isSubclassOf_iff hwf d c).1 this

theorem entails_refl (hwf : kb.wellFormed = true) : kb.Entails kb = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    exact (isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single (by simpa [Sub] using hp))
  · intro p hp
    exact (isInstanceOf_iff hwf p.1 p.2).2 ⟨p.2, by simpa [Inst] using hp, Relation.ReflTransGen.refl⟩

theorem entails_trans (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (h1 : kb.Entails kb' = true) (h2 : kb'.Entails kb'' = true) : kb.Entails kb'' = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro p hp
    exact entails_subclass hwf hwf' h1 (entails_sub h2 (by simpa [Sub] using hp))
  · intro p hp
    exact entails_instance hwf hwf' h1 (entails_inst h2 (by simpa [Inst] using hp))

/-! ### Merging -/

@[simp] theorem merge_sub : (kb.merge kb').sub = kb.sub ++ kb'.sub := rfl
@[simp] theorem merge_inst : (kb.merge kb').inst = kb.inst ++ kb'.inst := rfl
@[simp] theorem merge_items : (kb.merge kb').items = kb.items ++ kb'.items := rfl
@[simp] theorem merge_disj : (kb.merge kb').disj = kb.disj ++ kb'.disj := rfl

theorem sub_merge_left {a b : Qid} (h : kb.Sub a b) : (kb.merge kb').Sub a b := by
  simpa [Sub] using Or.inl h

theorem sub_merge_right {a b : Qid} (h : kb'.Sub a b) : (kb.merge kb').Sub a b := by
  simpa [Sub] using Or.inr h

theorem inst_merge_left {a c : Qid} (h : kb.Inst a c) : (kb.merge kb').Inst a c := by
  simpa [Inst] using Or.inl h

theorem inst_merge_right {a c : Qid} (h : kb'.Inst a c) : (kb.merge kb').Inst a c := by
  simpa [Inst] using Or.inr h

theorem wellFormed_merge (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.merge kb').wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    merge_sub, merge_inst, merge_disj, merge_items, List.mem_append] at *
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro p hp <;> rcases hp with hp | hp
  · exact ⟨Or.inl (hwf.1.1 p hp).1, Or.inl (hwf.1.1 p hp).2⟩
  · exact ⟨Or.inr (hwf'.1.1 p hp).1, Or.inr (hwf'.1.1 p hp).2⟩
  · exact ⟨Or.inl (hwf.1.2 p hp).1, Or.inl (hwf.1.2 p hp).2⟩
  · exact ⟨Or.inr (hwf'.1.2 p hp).1, Or.inr (hwf'.1.2 p hp).2⟩
  · exact ⟨Or.inl (hwf.2 p hp).1, Or.inl (hwf.2 p hp).2⟩
  · exact ⟨Or.inr (hwf'.2 p hp).1, Or.inr (hwf'.2 p hp).2⟩

/-- Importing an ontology preserves everything it asserted. -/
theorem merge_entails_left (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.merge kb').Entails kb = true := by
  have hm := wellFormed_merge hwf hwf'
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    exact (isSubclassOf_iff hm p.1 p.2).2
      (Relation.ReflTransGen.single (sub_merge_left (by simpa [Sub] using hp)))
  · intro p hp
    exact (isInstanceOf_iff hm p.1 p.2).2
      ⟨p.2, inst_merge_left (by simpa [Inst] using hp), Relation.ReflTransGen.refl⟩

theorem merge_entails_right (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.merge kb').Entails kb' = true := by
  have hm := wellFormed_merge hwf hwf'
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    exact (isSubclassOf_iff hm p.1 p.2).2
      (Relation.ReflTransGen.single (sub_merge_right (by simpa [Sub] using hp)))
  · intro p hp
    exact (isInstanceOf_iff hm p.1 p.2).2
      ⟨p.2, inst_merge_right (by simpa [Inst] using hp), Relation.ReflTransGen.refl⟩

/-- Monotonicity of the subclass engine under import. -/
theorem isSubclassOf_merge_left (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    {a b : Qid} (h : kb.isSubclassOf a b = true) : (kb.merge kb').isSubclassOf a b = true :=
  entails_subclass (wellFormed_merge hwf hwf') hwf (merge_entails_left hwf hwf') h

/-- Monotonicity of the instance engine under import. -/
theorem isInstanceOf_merge_left (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    {a c : Qid} (h : kb.isInstanceOf a c = true) : (kb.merge kb').isInstanceOf a c = true :=
  entails_instance (wellFormed_merge hwf hwf') hwf (merge_entails_left hwf hwf') h

theorem isSubclassOf_merge_right (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    {a b : Qid} (h : kb'.isSubclassOf a b = true) : (kb.merge kb').isSubclassOf a b = true :=
  entails_subclass (wellFormed_merge hwf hwf') hwf' (merge_entails_right hwf hwf') h

theorem isInstanceOf_merge_right (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    {a c : Qid} (h : kb'.isInstanceOf a c = true) : (kb.merge kb').isInstanceOf a c = true :=
  entails_instance (wellFormed_merge hwf hwf') hwf' (merge_entails_right hwf hwf') h

end KB
end Wikidata
