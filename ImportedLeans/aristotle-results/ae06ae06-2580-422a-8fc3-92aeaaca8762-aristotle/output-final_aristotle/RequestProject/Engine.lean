import RequestProject.Core
import RequestProject.Reachability

/-!
# An executable Wikidata ontology

A `KB` ("knowledge base") is a finite, fully computable Wikidata-style ontology:
a list of item identifiers (QIDs), a table of metaclass levels, and lists of
`subclass of` (P279), `instance of` (P31) and `disjoint with` statements.

Everything one wants to ask of it is decided by a Boolean function:
`KB.isSubclassOf`, `KB.isInstanceOf`, `KB.classesOf`, `KB.instancesOf`, and the
validator `KB.valid`.

The point of the file is that these computations are *certified*: for a
well-formed knowledge base the Boolean functions agree exactly with the abstract
semantics (`Relation.ReflTransGen` of the P279 statements, and P31 followed by
P279*), and a knowledge base passing `KB.valid` yields an abstract
`Wikidata.Ontology` (`KB.toOntology`), so all theorems of `RequestProject.Core`
apply to it.
-/

namespace Wikidata

/-- An item identifier.

Besides ordinary Wikidata entities (`Qid.wd "Q5"`), identifiers can name an
ontology (`Qid.ont`), can name another item at the meta level (`Qid.about`), and
can name the class of all items of a given metaclass level (`Qid.lvl`). These last
three constructors are what lets a knowledge base carry a description of itself
and of other knowledge bases; see `RequestProject.SelfDescription`. -/
inductive Qid where
  /-- An ordinary Wikidata entity, given by its identifier, e.g. `Q5`. -/
  | wd (id : String)
  /-- The item naming the ontology (knowledge base) called `name`. -/
  | ont (name : String)
  /-- The item naming, at the meta level, the item `q`. -/
  | about (q : Qid)
  /-- The class of all items of metaclass level `n`. -/
  | lvl (n : ℕ)
deriving DecidableEq, Repr, Inhabited

/-- A finite, executable Wikidata-style ontology. -/
structure KB where
  /-- A human readable name for this knowledge base. -/
  name : String := "ontology"
  /-- The items of the ontology. -/
  items : List Qid
  /-- The metaclass level of each item (missing entries default to `0`). -/
  levels : List (Qid × ℕ) := []
  /-- Direct `subclass of` (P279) statements. -/
  sub : List (Qid × Qid) := []
  /-- Direct `instance of` (P31) statements. -/
  inst : List (Qid × Qid) := []
  /-- Declared disjointness between classes. -/
  disj : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace KB

variable (kb : KB)

/-! ### The computational engine -/

/-- The declared metaclass level of an item. -/
def levelOf (q : Qid) : ℕ := (kb.levels.lookup q).getD 0

/-- The items of the knowledge base, as a `Finset`. -/
def allF : Finset Qid := kb.items.toFinset

/-- The direct superclasses of an item. -/
def supersL (q : Qid) : List Qid := (kb.sub.filter (fun p => p.1 == q)).map Prod.snd

/-- The direct superclasses of an item, as a `Finset`. -/
def supers (q : Qid) : Finset Qid := (kb.supersL q).toFinset

/-- All superclasses of an item, computed by saturating the P279 graph. -/
def superclasses (q : Qid) : Finset Qid := Reach.reach kb.supers kb.allF q

/-- Decides derived `subclass of`. -/
def isSubclassOf (a b : Qid) : Bool := b ∈ kb.superclasses a

/-- The classes an item is a *direct* instance of. -/
def directClassesL (a : Qid) : List Qid := (kb.inst.filter (fun p => p.1 == a)).map Prod.snd

/-- Decides derived `instance of`: a P31 statement followed by P279 steps. -/
def isInstanceOf (a c : Qid) : Bool := (kb.directClassesL a).any (fun d => kb.isSubclassOf d c)

/-- All classes (among the items) that `a` is an instance of. -/
def classesOf (a : Qid) : List Qid := kb.items.filter (fun c => kb.isInstanceOf a c)

/-- All superclasses (among the items) of `a`. -/
def superclassesOfL (a : Qid) : List Qid := kb.items.filter (fun c => kb.isSubclassOf a c)

/-- All instances (among the items) of the class `c`. -/
def instancesOf (c : Qid) : List Qid := kb.items.filter (fun a => kb.isInstanceOf a c)

/-- Decides whether an item has instances. -/
def hasInstanceB (c : Qid) : Bool := !(kb.instancesOf c).isEmpty

/-- Decides classhood: an item of level at least `1`. -/
def isClassB (c : Qid) : Bool := 0 < kb.levelOf c

/-- Decides individualhood: an item of level `0`. -/
def isIndividualB (a : Qid) : Bool := kb.levelOf a == 0

/-- Decides metaclasshood: an item having an instance which itself has instances. -/
def isMetaclassB (c : Qid) : Bool := (kb.instancesOf c).any (fun a => kb.hasInstanceB a)

/-! ### The validator -/

/-- All statements mention declared items. -/
def wellFormed : Bool :=
  kb.sub.all (fun p => p.1 ∈ kb.items && p.2 ∈ kb.items) &&
  kb.inst.all (fun p => p.1 ∈ kb.items && p.2 ∈ kb.items) &&
  kb.disj.all (fun p => p.1 ∈ kb.items && p.2 ∈ kb.items)

/-- Statements respect the metaclass level discipline. -/
def levelsOk : Bool :=
  kb.inst.all (fun p => kb.levelOf p.2 == kb.levelOf p.1 + 1) &&
  kb.sub.all (fun p => (kb.levelOf p.1 == kb.levelOf p.2) && (0 < kb.levelOf p.1))

/-- The class hierarchy has no genuine cycles. -/
def acyclic : Bool :=
  kb.items.all (fun a => kb.items.all
    (fun b => !(kb.isSubclassOf a b && kb.isSubclassOf b a) || a == b))

/-- Declared disjoint classes share no instance. -/
def disjointOk : Bool :=
  kb.disj.all (fun p => kb.items.all (fun a => !(kb.isInstanceOf a p.1 && kb.isInstanceOf a p.2)))

/-- The full validity check. -/
def valid : Bool := kb.wellFormed && kb.levelsOk && kb.acyclic && kb.disjointOk

/-! ### Semantics -/

/-- The `subclass of` statements, as a relation. -/
def Sub (a b : Qid) : Prop := (a, b) ∈ kb.sub

/-- The `instance of` statements, as a relation. -/
def Inst (a c : Qid) : Prop := (a, c) ∈ kb.inst

/-- Declared disjointness, as a (symmetric) relation. -/
def Disj (c d : Qid) : Prop := (c, d) ∈ kb.disj ∨ (d, c) ∈ kb.disj

variable {kb}

theorem mem_supers {a b : Qid} : b ∈ kb.supers a ↔ kb.Sub a b := by
  simp [supers, supersL, Sub, List.mem_filter, List.mem_map]

theorem succ_eq_sub (kb : KB) : (fun u v => v ∈ kb.supers u) = kb.Sub := by
  funext u v; exact propext mem_supers

/-- Both endpoints of a P279 statement of a well-formed knowledge base are items. -/
theorem wf_sub (hwf : kb.wellFormed = true) {a b : Qid} (h : kb.Sub a b) :
    a ∈ kb.items ∧ b ∈ kb.items := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have := hwf.1.1 (a, b) h
  simpa using this

/-- Both endpoints of a P31 statement of a well-formed knowledge base are items. -/
theorem wf_inst (hwf : kb.wellFormed = true) {a c : Qid} (h : kb.Inst a c) :
    a ∈ kb.items ∧ c ∈ kb.items := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have := hwf.1.2 (a, c) h
  simpa using this

theorem supers_subset_all (hwf : kb.wellFormed = true) (y : Qid) : kb.supers y ⊆ kb.allF := by
  intro b hb
  have hsub : kb.Sub y b := mem_supers.1 hb
  simpa [allF] using (wf_sub hwf hsub).2

theorem mem_allF {a : Qid} : a ∈ kb.allF ↔ a ∈ kb.items := by simp [allF]

theorem isSubclassOf_iff_of_mem (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∈ kb.items)
    (b : Qid) : kb.isSubclassOf a b = true ↔ Relation.ReflTransGen kb.Sub a b := by
  have h := Reach.mem_reach_iff kb.supers (supers_subset_all hwf) (mem_allF.2 ha) b
  rw [succ_eq_sub] at h
  simpa [isSubclassOf, superclasses] using h

/-- Items with no P279 statements out of them have no proper superclasses. -/
theorem eq_of_reflTransGen_sub_of_not_mem {a b : Qid} (hwf : kb.wellFormed = true)
    (ha : a ∉ kb.items) (h : Relation.ReflTransGen kb.Sub a b) : a = b := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
  · exact h.symm
  · exact absurd (wf_sub hwf (Relation.TransGen.head'_iff.1 h).choose_spec.1).1 ha

theorem supers_eq_empty_of_not_mem (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∉ kb.items) :
    kb.supers a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 ?_
  intro b hb
  exact ha (wf_sub hwf (mem_supers.1 hb)).1

theorem superclasses_eq_singleton_of_supers_empty {a : Qid} (h : kb.supers a = ∅) :
    kb.superclasses a = {a} := by
  have : ∀ n, Reach.iter kb.supers n a = {a} := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [Reach.iter_succ, ih]; simp [Reach.step, h]
  simpa [superclasses, Reach.reach] using this _

/-- **Certified subclass computation**: in a well-formed knowledge base the Boolean
check `isSubclassOf` decides the reflexive–transitive closure of the P279
statements. -/
theorem isSubclassOf_iff (hwf : kb.wellFormed = true) (a b : Qid) :
    kb.isSubclassOf a b = true ↔ Relation.ReflTransGen kb.Sub a b := by
  by_cases ha : a ∈ kb.items
  · exact isSubclassOf_iff_of_mem hwf ha b
  · rw [isSubclassOf, superclasses_eq_singleton_of_supers_empty
      (supers_eq_empty_of_not_mem hwf ha)]
    simp only [Finset.mem_singleton, decide_eq_true_eq]
    constructor
    · rintro rfl; exact Relation.ReflTransGen.refl
    · intro h; exact (eq_of_reflTransGen_sub_of_not_mem hwf ha h).symm

theorem inst_mem_items {a c : Qid} (hwf : kb.wellFormed = true) (h : kb.Inst a c) :
    a ∈ kb.items ∧ c ∈ kb.items := wf_inst hwf h

theorem mem_directClassesL {a d : Qid} : d ∈ kb.directClassesL a ↔ kb.Inst a d := by
  simp [directClassesL, Inst, List.mem_filter, List.mem_map]

/-- **Certified instance computation**. -/
theorem isInstanceOf_iff (hwf : kb.wellFormed = true) (a c : Qid) :
    kb.isInstanceOf a c = true ↔ ∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d c := by
  simp only [isInstanceOf, List.any_eq_true]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hd' : kb.Inst a d := mem_directClassesL.1 hd
    exact ⟨d, hd', (isSubclassOf_iff hwf d c).1 (by simpa using hdc)⟩
  · rintro ⟨d, hd, hdc⟩
    exact ⟨d, mem_directClassesL.2 hd, by simpa using (isSubclassOf_iff hwf d c).2 hdc⟩

/-- Derived `subclass of`, as computed by the engine, is transitive. -/
theorem isSubclassOf_trans (hwf : kb.wellFormed = true) {a b c : Qid}
    (hab : kb.isSubclassOf a b = true) (hbc : kb.isSubclassOf b c = true) :
    kb.isSubclassOf a c = true :=
  (isSubclassOf_iff hwf a c).2
    (((isSubclassOf_iff hwf a b).1 hab).trans ((isSubclassOf_iff hwf b c).1 hbc))

/-- Derived `instance of` composes with derived `subclass of`: this is inheritance,
in computational form. -/
theorem isInstanceOf_trans_subclass (hwf : kb.wellFormed = true) {a c d : Qid}
    (hac : kb.isInstanceOf a c = true) (hcd : kb.isSubclassOf c d = true) :
    kb.isInstanceOf a d = true := by
  obtain ⟨e, he, hec⟩ := (isInstanceOf_iff hwf a c).1 hac
  exact (isInstanceOf_iff hwf a d).2 ⟨e, he, hec.trans ((isSubclassOf_iff hwf c d).1 hcd)⟩

theorem isSubclassOf_refl (kb : KB) (a : Qid) : kb.isSubclassOf a a = true := by
  simpa [isSubclassOf, superclasses] using Reach.mem_reach_self kb.supers kb.allF a

theorem isInstanceOf_of_inst {a c : Qid} (h : kb.Inst a c) : kb.isInstanceOf a c = true := by
  simp only [isInstanceOf, List.any_eq_true]
  exact ⟨c, mem_directClassesL.2 h, isSubclassOf_refl kb c⟩

theorem mem_instancesOf {a c : Qid} :
    a ∈ kb.instancesOf c ↔ a ∈ kb.items ∧ kb.isInstanceOf a c = true := by
  simp [instancesOf, List.mem_filter]

theorem hasInstanceB_eq_true {a c : Qid} (ha : a ∈ kb.items) (h : kb.isInstanceOf a c = true) :
    kb.hasInstanceB c = true := by
  have hmem : a ∈ kb.instancesOf c := mem_instancesOf.2 ⟨ha, h⟩
  simpa [hasInstanceB, List.isEmpty_iff] using List.ne_nil_of_mem hmem

theorem isMetaclassB_eq_true {a c : Qid} (ha : a ∈ kb.items) (h : kb.isInstanceOf a c = true)
    (hb : kb.hasInstanceB a = true) : kb.isMetaclassB c = true := by
  simp only [isMetaclassB, List.any_eq_true]
  exact ⟨a, mem_instancesOf.2 ⟨ha, h⟩, hb⟩

/-- A knowledge base with no `subclass of` statements has only trivial subclass
relations. -/
theorem isSubclassOf_eq_of_sub_nil (h : kb.sub = []) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) : a = b := by
  have hs : kb.supers a = ∅ := by simp [supers, supersL, h]
  rw [isSubclassOf, superclasses_eq_singleton_of_supers_empty hs] at hab
  simpa [eq_comm] using hab

theorem acyclic_of_sub_nil (h : kb.sub = []) : kb.acyclic = true := by
  simp only [acyclic, List.all_eq_true]
  intro a _ b _
  by_cases hab : kb.isSubclassOf a b = true
  · have : a = b := isSubclassOf_eq_of_sub_nil h hab
    subst this; simp
  · simp [hab]

/-! ### From a validated knowledge base to an abstract ontology -/

theorem valid_wellFormed (h : kb.valid = true) : kb.wellFormed = true := by
  simp only [valid, Bool.and_eq_true] at h; tauto

theorem valid_levelsOk (h : kb.valid = true) : kb.levelsOk = true := by
  simp only [valid, Bool.and_eq_true] at h; tauto

theorem valid_acyclic (h : kb.valid = true) : kb.acyclic = true := by
  simp only [valid, Bool.and_eq_true] at h; tauto

theorem valid_disjointOk (h : kb.valid = true) : kb.disjointOk = true := by
  simp only [valid, Bool.and_eq_true] at h; tauto

theorem level_inst (h : kb.levelsOk = true) {a c : Qid} (hac : kb.Inst a c) :
    kb.levelOf c = kb.levelOf a + 1 := by
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have := h.1 (a, c) hac
  simpa using this

theorem level_sub (h : kb.levelsOk = true) {a b : Qid} (hab : kb.Sub a b) :
    kb.levelOf a = kb.levelOf b ∧ 0 < kb.levelOf a := by
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have := h.2 (a, b) hab
  simpa using this

theorem subclass_antisymm (hv : kb.valid = true) {a b : Qid}
    (hab : Relation.ReflTransGen kb.Sub a b) (hba : Relation.ReflTransGen kb.Sub b a) : a = b := by
  have hwf := valid_wellFormed hv
  by_cases ha : a ∈ kb.items
  · by_cases hb : b ∈ kb.items
    · have h1 : kb.isSubclassOf a b = true := (isSubclassOf_iff hwf a b).2 hab
      have h2 : kb.isSubclassOf b a = true := (isSubclassOf_iff hwf b a).2 hba
      have hac := valid_acyclic hv
      have := List.all_eq_true.1 (List.all_eq_true.1 hac a ha) b hb
      simp [h1, h2] at this
      exact this
    · exact (eq_of_reflTransGen_sub_of_not_mem hwf hb hba).symm
  · exact eq_of_reflTransGen_sub_of_not_mem hwf ha hab

/-- A validated knowledge base is an abstract Wikidata ontology, so every theorem
of `RequestProject.Core` applies to it. -/
def toOntology (kb : KB) (hv : kb.valid = true) : Ontology Qid where
  P279 := kb.Sub
  P31 := kb.Inst
  level := kb.levelOf
  level_P31 h := level_inst (valid_levelsOk hv) h
  level_P279 h := (level_sub (valid_levelsOk hv) h).1
  P279_isClass h := (level_sub (valid_levelsOk hv) h).2
  P279_antisymm h h' := subclass_antisymm hv h h'

@[simp] theorem toOntology_P279 (hv : kb.valid = true) : (kb.toOntology hv).P279 = kb.Sub := rfl
@[simp] theorem toOntology_P31 (hv : kb.valid = true) : (kb.toOntology hv).P31 = kb.Inst := rfl
@[simp] theorem toOntology_level (hv : kb.valid = true) :
    (kb.toOntology hv).level = kb.levelOf := rfl

/-- The Boolean subclass check computes the abstract derived `subclass of`. -/
theorem isSubclassOf_iff_subclassOf (hv : kb.valid = true) (a b : Qid) :
    kb.isSubclassOf a b = true ↔ (kb.toOntology hv).SubclassOf a b :=
  isSubclassOf_iff (valid_wellFormed hv) a b

/-- The Boolean instance check computes the abstract derived `instance of`. -/
theorem isInstanceOf_iff_instanceOf (hv : kb.valid = true) (a c : Qid) :
    kb.isInstanceOf a c = true ↔ (kb.toOntology hv).InstanceOf a c :=
  isInstanceOf_iff (valid_wellFormed hv) a c

/-- A validated knowledge base with its disjointness declarations is an abstract
ontology with disjointness. -/
def toWithDisjointness (kb : KB) (hv : kb.valid = true) : Ontology.WithDisjointness Qid where
  toOntology := kb.toOntology hv
  DisjointWith := kb.Disj
  disjointWith_symm h := h.symm
  disjointWith_spec := by
    rintro a c d hcd hac had
    have hwf := valid_wellFormed hv
    have key : ∀ {c d : Qid}, (c, d) ∈ kb.disj → (kb.toOntology hv).InstanceOf a c →
        (kb.toOntology hv).InstanceOf a d → False := by
      intro c d hmem h1 h2
      have hd := valid_disjointOk hv
      have ha : a ∈ kb.items := by
        obtain ⟨e, he, _⟩ := h1
        exact (inst_mem_items hwf he).1
      have := List.all_eq_true.1 (List.all_eq_true.1 hd _ hmem) a ha
      have e1 : kb.isInstanceOf a c = true := (isInstanceOf_iff_instanceOf hv a c).2 h1
      have e2 : kb.isInstanceOf a d = true := (isInstanceOf_iff_instanceOf hv a d).2 h2
      simp [e1, e2] at this
    rcases hcd with h | h
    · exact key h hac had
    · exact key h had hac

end KB

end Wikidata
