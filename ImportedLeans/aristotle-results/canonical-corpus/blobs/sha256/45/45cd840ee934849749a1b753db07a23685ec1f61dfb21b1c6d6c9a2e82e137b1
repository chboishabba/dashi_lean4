import Mathlib

/-!
# An abstract model of the Wikidata ontology layer

This file formalises the ontology layer of Wikidata as described by
*Wikidata:WikiProject Ontology*: items are related by

* `P279` — *subclass of* (direct statements), and
* `P31`  — *instance of* (direct statements),

and every item sits at a **metaclass level**: individuals at level `0`, classes of
individuals at level `1`, classes of classes (metaclasses) at level `2`, and so on.

The two structural rules of the Wikidata ontology are:

* `subclass of` is transitive (so the *derived* subclass relation is its
  reflexive–transitive closure), and
* `instance of` composes with `subclass of` on the right: if `a` is an instance of
  `c` and `c` is a subclass of `d`, then `a` is an instance of `d`.
  (`instance of` itself is **not** transitive; see `RequestProject.Examples`.)

The level discipline is captured by the axioms `level_P31` and `level_P279`, and the
class hierarchy is required to be antisymmetric (no genuine subclass cycles).
-/

namespace Wikidata

/-- An abstract Wikidata-style ontology on a type of items `I`. -/
structure Ontology (I : Type*) where
  /-- Direct `subclass of` (P279) statements. -/
  P279 : I → I → Prop
  /-- Direct `instance of` (P31) statements. -/
  P31 : I → I → Prop
  /-- The metaclass level: `0` for individuals, `1` for classes of individuals,
  `2` for metaclasses, etc. -/
  level : I → ℕ
  /-- An instance sits exactly one level below its class. -/
  level_P31 : ∀ {a c}, P31 a c → level c = level a + 1
  /-- A class and its superclasses sit at the same level. -/
  level_P279 : ∀ {a b}, P279 a b → level a = level b
  /-- Only classes participate in `subclass of` statements. -/
  P279_isClass : ∀ {a b}, P279 a b → 0 < level a
  /-- The class hierarchy has no genuine cycles. -/
  P279_antisymm : ∀ {a b}, Relation.ReflTransGen P279 a b → Relation.ReflTransGen P279 b a → a = b

namespace Ontology

variable {I : Type*} (O : Ontology I)

/-- Derived `subclass of`: the reflexive–transitive closure of the direct P279
statements. -/
def SubclassOf (a b : I) : Prop := Relation.ReflTransGen O.P279 a b

/-- Derived `instance of`: a direct P31 statement followed by any number of P279
steps. -/
def InstanceOf (a c : I) : Prop := ∃ d, O.P31 a d ∧ O.SubclassOf d c

/-- An item is a *class* when it sits at level at least `1`. -/
def IsClass (c : I) : Prop := 0 < O.level c

/-- An item is an *individual* when it sits at level `0`. -/
def IsIndividual (a : I) : Prop := O.level a = 0

/-- An item *has instances* when some item is an instance of it. -/
def HasInstance (c : I) : Prop := ∃ a, O.InstanceOf a c

/-- A *metaclass* is a class whose instances are themselves classes with
instances, i.e. it lives at level at least `2`. -/
def IsMetaclass (c : I) : Prop := ∃ a, O.InstanceOf a c ∧ O.HasInstance a

variable {O}

/-! ### The class hierarchy is a partial order -/

@[refl] theorem subclassOf_refl (a : I) : O.SubclassOf a a := Relation.ReflTransGen.refl

theorem subclassOf_of_P279 {a b : I} (h : O.P279 a b) : O.SubclassOf a b :=
  Relation.ReflTransGen.single h

theorem subclassOf_trans {a b c : I} (hab : O.SubclassOf a b) (hbc : O.SubclassOf b c) :
    O.SubclassOf a c := Relation.ReflTransGen.trans hab hbc

theorem subclassOf_antisymm {a b : I} (hab : O.SubclassOf a b) (hba : O.SubclassOf b a) :
    a = b := O.P279_antisymm hab hba

/-- The derived `subclass of` relation is a partial order on items. -/
def subclassPartialOrder (O : Ontology I) : PartialOrder I where
  le a b := O.SubclassOf a b
  le_refl := subclassOf_refl
  le_trans _ _ _ := subclassOf_trans
  le_antisymm _ _ := subclassOf_antisymm

/-! ### Levels -/

theorem level_subclassOf {a b : I} (h : O.SubclassOf a b) : O.level a = O.level b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (O.level_P279 hbc)

theorem instanceOf_of_P31 {a c : I} (h : O.P31 a c) : O.InstanceOf a c :=
  ⟨c, h, subclassOf_refl c⟩

/-- The inheritance rule: instances of a class are instances of all its superclasses. -/
theorem instanceOf_trans_subclassOf {a c d : I} (hac : O.InstanceOf a c)
    (hcd : O.SubclassOf c d) : O.InstanceOf a d := by
  obtain ⟨e, he, hec⟩ := hac
  exact ⟨e, he, subclassOf_trans hec hcd⟩

theorem level_instanceOf {a c : I} (h : O.InstanceOf a c) : O.level c = O.level a + 1 := by
  obtain ⟨d, hd, hdc⟩ := h
  rw [← level_subclassOf hdc]
  exact O.level_P31 hd

/-! ### Basic sanity results about the ontology -/

/-- No item is an instance of itself. -/
theorem not_instanceOf_self (a : I) : ¬ O.InstanceOf a a := by
  intro h; have := level_instanceOf h; omega

/-- `instance of` is asymmetric. -/
theorem instanceOf_asymm {a b : I} (h : O.InstanceOf a b) : ¬ O.InstanceOf b a := by
  intro h'
  have := level_instanceOf h
  have := level_instanceOf h'
  omega

/-- A class is never a subclass of one of its own instances. -/
theorem not_subclassOf_of_instanceOf {a c : I} (h : O.InstanceOf a c) : ¬ O.SubclassOf c a := by
  intro hsub
  have h1 := level_instanceOf h
  have h2 := level_subclassOf hsub
  omega

/-- Along a chain of `instance of` steps the metaclass level strictly increases. -/
theorem level_lt_of_transGen_instanceOf {a b : I}
    (h : Relation.TransGen O.InstanceOf a b) : O.level a < O.level b := by
  induction h with
  | single hab => have := level_instanceOf hab; omega
  | tail _ hbc ih => have := level_instanceOf hbc; omega

/-- The `instance of` relation is acyclic: there are no `instance of` loops of any
length. -/
theorem instanceOf_acyclic (a : I) : ¬ Relation.TransGen O.InstanceOf a a := by
  intro h; have := level_lt_of_transGen_instanceOf h; omega

theorem isClass_of_hasInstance {c : I} (h : O.HasInstance c) : O.IsClass c := by
  obtain ⟨a, ha⟩ := h
  have := level_instanceOf ha
  simp [IsClass]; omega

/-- Anything comparable to a class in the class hierarchy is a class. -/
theorem isClass_of_subclassOf {a b : I} (h : O.SubclassOf a b) (hb : O.IsClass b) :
    O.IsClass a := by
  have := level_subclassOf h; simpa [IsClass, this] using hb

/-- Metaclasses live at level at least `2`. -/
theorem two_le_level_of_isMetaclass {c : I} (h : O.IsMetaclass c) : 2 ≤ O.level c := by
  obtain ⟨a, hac, b, hba⟩ := h
  have h1 := level_instanceOf hac
  have h2 := level_instanceOf hba
  omega

/-- Instances of a metaclass are classes: metaclasses are "classes of classes". -/
theorem isClass_of_instanceOf_metaclass {a c : I} (hmeta : O.IsMetaclass c)
    (h : O.InstanceOf a c) : O.IsClass a := by
  have h1 := two_le_level_of_isMetaclass hmeta
  have h2 := level_instanceOf h
  simp [IsClass]; omega

/-- Individuals have no instances. -/
theorem not_hasInstance_of_isIndividual {a : I} (h : O.IsIndividual a) : ¬ O.HasInstance a :=
  fun hi => by
    have := isClass_of_hasInstance hi
    simp [IsClass, IsIndividual] at *; omega

/-- Individuals have no subclasses. -/
theorem not_P279_of_isIndividual {a b : I} (h : O.IsIndividual a) : ¬ O.P279 b a := by
  intro hba
  have h1 := O.level_P279 hba
  have h2 := O.P279_isClass hba
  simp [IsIndividual] at h
  omega

/-! ### Disjointness -/

/-- An ontology together with *disjointness* declarations between classes: disjoint
classes may not share an instance. -/
structure WithDisjointness (I : Type*) extends Ontology I where
  /-- Declared disjointness between classes. -/
  DisjointWith : I → I → Prop
  /-- Disjointness is symmetric. -/
  disjointWith_symm : ∀ {c d}, DisjointWith c d → DisjointWith d c
  /-- Disjoint classes share no instance. -/
  disjointWith_spec : ∀ {a c d}, DisjointWith c d →
    toOntology.InstanceOf a c → toOntology.InstanceOf a d → False

namespace WithDisjointness

variable {I : Type*} {D : WithDisjointness I}

/-- Disjointness is inherited by subclasses. -/
theorem no_common_instance_of_subclasses {a c d c' d' : I}
    (h : D.DisjointWith c d) (hc : D.toOntology.SubclassOf c' c)
    (hd : D.toOntology.SubclassOf d' d)
    (hac : D.toOntology.InstanceOf a c') (had : D.toOntology.InstanceOf a d') : False :=
  D.disjointWith_spec h (instanceOf_trans_subclassOf hac hc)
    (instanceOf_trans_subclassOf had hd)

/-- A class with instances is not a subclass of a class disjoint from it. -/
theorem not_subclassOf_of_disjointWith {c d : I} (h : D.DisjointWith c d)
    (hc : D.toOntology.HasInstance c) : ¬ D.toOntology.SubclassOf c d := by
  intro hsub
  obtain ⟨a, ha⟩ := hc
  exact D.disjointWith_spec h ha (instanceOf_trans_subclassOf ha hsub)

/-- A class declared disjoint from itself is empty. -/
theorem not_hasInstance_of_selfDisjoint {c : I} (h : D.DisjointWith c c) :
    ¬ D.toOntology.HasInstance c := by
  rintro ⟨a, ha⟩
  exact D.disjointWith_spec h ha ha

end WithDisjointness

end Ontology

end Wikidata
