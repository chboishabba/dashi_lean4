import RequestProject.Core
import RequestProject.Engine

/-!
# The extensional view: classes, extents and the concept lattice

The ontology layer relates items by `instance of` and `subclass of`.  Reading a
class *extensionally*, as the collection of its instances, turns the ontology into
a formal context in the sense of concept analysis, and this file develops that
view.

For a set `A` of items, `commonClasses A` is the set of classes every member of
`A` is an instance of; dually, for a set `C` of classes, `commonInstances C` is
the set of items that are instances of every member of `C`.  These two maps form
an antitone Galois connection (`Wikidata.Ontology.commonInstances_subset_iff`),
so `commonInstances ∘ commonClasses` is a closure operator: extensive, monotone
and idempotent.  Its fixed points are the **extents**, and they are closed under
arbitrary intersections and contain everything (`Wikidata.Ontology.IsExtent`), so
they form a complete lattice — `Wikidata.Ontology.extentCompleteLattice`.

The ontology sits inside this picture: the extension of a class is always an
extent, and the inheritance rule says exactly that the class hierarchy is carried
into inclusion of extents (`Wikidata.Ontology.extension_subset_of_subclassOf`).
The converse fails — two classes can have exactly the same instances without
either being a subclass of the other — and the last section exhibits a valid
knowledge base where that happens, so the extensional reading is strictly coarser
than the asserted hierarchy.
-/

namespace Wikidata

namespace Ontology

variable {I : Type*} (O : Ontology I)

/-- The extension of a class: the items that are instances of it. -/
def extension (c : I) : Set I := {a | O.InstanceOf a c}

/-- The classes shared by all items of a set. -/
def commonClasses (A : Set I) : Set I := {c | ∀ a ∈ A, O.InstanceOf a c}

/-- The items that are instances of every class of a set. -/
def commonInstances (C : Set I) : Set I := {a | ∀ c ∈ C, O.InstanceOf a c}

variable {O}

@[simp] theorem mem_extension {a c : I} : a ∈ O.extension c ↔ O.InstanceOf a c := Iff.rfl

@[simp] theorem mem_commonClasses {A : Set I} {c : I} :
    c ∈ O.commonClasses A ↔ ∀ a ∈ A, O.InstanceOf a c := Iff.rfl

@[simp] theorem mem_commonInstances {C : Set I} {a : I} :
    a ∈ O.commonInstances C ↔ ∀ c ∈ C, O.InstanceOf a c := Iff.rfl

/-- **The Galois connection** between sets of items and sets of classes. -/
theorem commonInstances_subset_iff (A C : Set I) :
    A ⊆ O.commonInstances C ↔ C ⊆ O.commonClasses A := by
  constructor
  · intro h c hc a ha; exact h ha c hc
  · intro h a ha c hc; exact h hc a ha

theorem commonClasses_antitone {A B : Set I} (h : A ⊆ B) :
    O.commonClasses B ⊆ O.commonClasses A := fun _ hc a ha => hc a (h ha)

theorem commonInstances_antitone {C D : Set I} (h : C ⊆ D) :
    O.commonInstances D ⊆ O.commonInstances C := fun _ ha c hc => ha c (h hc)

theorem subset_commonInstances_commonClasses (A : Set I) :
    A ⊆ O.commonInstances (O.commonClasses A) := fun _ ha _ hc => hc _ ha

theorem subset_commonClasses_commonInstances (C : Set I) :
    C ⊆ O.commonClasses (O.commonInstances C) := fun _ hc _ ha => ha _ hc

theorem commonClasses_commonInstances_commonClasses (A : Set I) :
    O.commonClasses (O.commonInstances (O.commonClasses A)) = O.commonClasses A :=
  subset_antisymm (commonClasses_antitone (subset_commonInstances_commonClasses A))
    (subset_commonClasses_commonInstances _)

theorem commonInstances_commonClasses_commonInstances (C : Set I) :
    O.commonInstances (O.commonClasses (O.commonInstances C)) = O.commonInstances C :=
  subset_antisymm (commonInstances_antitone (subset_commonClasses_commonInstances C))
    (subset_commonInstances_commonClasses _)

variable (O) in
/-- The closure operator: the items sharing all the classes shared by `A`. -/
def extentClosure (A : Set I) : Set I := O.commonInstances (O.commonClasses A)

theorem le_extentClosure (A : Set I) : A ⊆ O.extentClosure A :=
  subset_commonInstances_commonClasses A

theorem extentClosure_mono {A B : Set I} (h : A ⊆ B) : O.extentClosure A ⊆ O.extentClosure B :=
  commonInstances_antitone (commonClasses_antitone h)

theorem extentClosure_idem (A : Set I) : O.extentClosure (O.extentClosure A) = O.extentClosure A :=
  commonInstances_commonClasses_commonInstances _

variable (O) in
/-- An **extent** is a set of items closed under the operator above: a set of items
determined by the classes they share. -/
def IsExtent (A : Set I) : Prop := O.extentClosure A = A

theorem isExtent_iff {A : Set I} : O.IsExtent A ↔ O.extentClosure A ⊆ A :=
  ⟨fun h => h.subset, fun h => subset_antisymm h (le_extentClosure A)⟩

theorem isExtent_extentClosure (A : Set I) : O.IsExtent (O.extentClosure A) :=
  extentClosure_idem A

theorem isExtent_commonInstances (C : Set I) : O.IsExtent (O.commonInstances C) :=
  commonInstances_commonClasses_commonInstances C

/-- The extension of a class is an extent. -/
theorem isExtent_extension (c : I) : O.IsExtent (O.extension c) := by
  refine isExtent_iff.2 fun a ha => ?_
  exact ha c (fun x hx => hx)

/-- The whole domain is an extent. -/
theorem isExtent_univ : O.IsExtent (Set.univ : Set I) :=
  isExtent_iff.2 fun _ _ => Set.mem_univ _

/-- **Extents are closed under arbitrary intersections.** -/
theorem isExtent_sInter {S : Set (Set I)} (hS : ∀ A ∈ S, O.IsExtent A) : O.IsExtent (⋂₀ S) := by
  refine isExtent_iff.2 fun a ha => ?_
  intro A hA
  have : O.extentClosure (⋂₀ S) ⊆ O.extentClosure A :=
    extentClosure_mono (Set.sInter_subset_of_mem hA)
  exact (hS A hA) ▸ this ha

/-! ### The complete lattice of extents -/

variable (O)

/-- The extents of an ontology, as a type. -/
def Extent : Type _ := {A : Set I // O.IsExtent A}

namespace Extent

instance : SetLike (O.Extent) I where
  coe A := A.1
  coe_injective' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    exact Subtype.ext h

instance : PartialOrder (O.Extent) := PartialOrder.lift (fun A => (A.1 : Set I))
  (fun _ _ h => Subtype.ext h)

theorem le_def {A B : O.Extent} : A ≤ B ↔ (A.1 : Set I) ⊆ B.1 := Iff.rfl

/-- The infimum of a family of extents is their intersection. -/
instance : InfSet (O.Extent) where
  sInf S :=
    ⟨⋂₀ ((fun A : O.Extent => (A.1 : Set I)) '' S), by
      refine isExtent_sInter ?_
      rintro A ⟨B, -, rfl⟩
      exact B.2⟩

theorem coe_sInf (S : Set (O.Extent)) :
    ((sInf S : O.Extent) : Set I) = ⋂₀ ((fun A : O.Extent => (A.1 : Set I)) '' S) := rfl

/-- **The extents form a complete lattice**, with intersection as meet. -/
noncomputable def completeLattice : CompleteLattice (O.Extent) :=
  completeLatticeOfInf (O.Extent) (by
    intro S
    constructor
    · intro A hA x hx
      exact (Set.mem_sInter.1 hx) _ ⟨A, hA, rfl⟩
    · intro A hA x hx
      refine Set.mem_sInter.2 ?_
      rintro t ⟨B, hB, rfl⟩
      exact hA hB hx)

end Extent

variable {O}

/-! ### The class hierarchy inside the concept lattice -/

/-- **Inheritance is inclusion of extents**: a subclass has a smaller extension. -/
theorem extension_subset_of_subclassOf {c d : I} (h : O.SubclassOf c d) :
    O.extension c ⊆ O.extension d := fun _ ha => instanceOf_trans_subclassOf ha h

/-- The classes shared by the instances of a class include all its superclasses. -/
theorem superclasses_subset_commonClasses {c : I} {d : I} (h : O.SubclassOf c d) :
    d ∈ O.commonClasses (O.extension c) := fun _ ha => instanceOf_trans_subclassOf ha h

/-- A class with instances is an instance-wise lower bound of the classes its
instances share. -/
theorem extension_subset_of_mem_commonClasses {c d : I}
    (h : d ∈ O.commonClasses (O.extension c)) : O.extension c ⊆ O.extension d :=
  fun _ ha => h _ ha

end Ontology

/-! ### Extensional equality is weaker than subsumption

Two classes may have exactly the same instances without either being a subclass of
the other: the extensional reading is strictly coarser than the asserted
hierarchy. -/

namespace ConceptExample

open Wikidata

/-- An item that is an instance of two unrelated classes. -/
def a : Qid := .wd "Q-a"
/-- The first class. -/
def c : Qid := .wd "Q-c"
/-- The second class. -/
def d : Qid := .wd "Q-d"

/-- A knowledge base with two classes having the same single instance and no
`subclass of` statement at all. -/
def twoClasses : KB where
  name := "coextensive classes"
  items := [a, c, d]
  levels := [(a, 0), (c, 1), (d, 1)]
  inst := [(a, c), (a, d)]

theorem twoClasses_valid : twoClasses.valid = true := by decide

/-- The ontology determined by that knowledge base. -/
def O : Ontology Qid := twoClasses.toOntology twoClasses_valid

theorem instanceOf_iff {x y : Qid} : O.InstanceOf x y ↔ (x, y) ∈ twoClasses.inst := by
  constructor
  · rintro ⟨e, he, hec⟩
    have hey : e = y := by
      cases hec with
      | refl => rfl
      | tail _ hstep => simp [O, KB.toOntology, KB.Sub, twoClasses] at hstep
    exact hey ▸ he
  · intro h; exact ⟨y, h, Relation.ReflTransGen.refl⟩

theorem instanceOf_c_iff {x : Qid} : O.InstanceOf x c ↔ x = a := by
  rw [instanceOf_iff]; simp [twoClasses, a, c, d]

theorem instanceOf_d_iff {x : Qid} : O.InstanceOf x d ↔ x = a := by
  rw [instanceOf_iff]; simp [twoClasses, a, c, d]

/-- The two classes are coextensive: they have exactly the same instances. -/
theorem extension_eq : O.extension c = O.extension d := by
  ext x
  rw [Ontology.mem_extension, Ontology.mem_extension, instanceOf_c_iff, instanceOf_d_iff]

/-- Nevertheless neither is a subclass of the other. -/
theorem not_subclassOf : ¬ O.SubclassOf c d := by
  intro h
  have : twoClasses.isSubclassOf c d = true :=
    (KB.isSubclassOf_iff_subclassOf twoClasses_valid c d).2 h
  exact absurd this (by decide)

/-- So a class is not determined by its extension: the extensional view identifies
the two classes, the asserted hierarchy keeps them apart. -/
theorem extension_not_injective : O.extension c = O.extension d ∧ c ≠ d :=
  ⟨extension_eq, by decide⟩

end ConceptExample

end Wikidata
