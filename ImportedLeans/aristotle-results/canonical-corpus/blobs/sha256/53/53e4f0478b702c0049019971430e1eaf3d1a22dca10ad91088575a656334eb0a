import RequestProject.Alignment
import RequestProject.BabySteps

/-!
# Baby steps, part three: aligning two ontologies, one small step at a time

`RequestProject.BabySteps` built a four-item Wikidata fragment by hand and read
off its facts; `RequestProject.BabyStepsProperties` did the same for the property
layer. This file is the third instalment: it takes the very same four-item
fragment `Wikidata.BabySteps.tiny` and *aligns* it with a small upper ontology,
in the sense of `Wikidata.Ontology.Alignment` — a set of `equivalent class`
(P1709) links that is sound, i.e. every asserted statement on the Wikidata side
becomes a derived fact on the other side.

The upper ontology is

```
douglas  --instance of-->  person  --subclass of-->  agent
person   --instance of-->  kindOfOrganism
```

and the links are

```
Q42 (Douglas Adams)  ↦  douglas
Q5  (human)          ↦  person
Q215627 (person)     ↦  agent
Q55983715            ↦  kindOfOrganism
```

Steps 0–2 build the target ontology and the alignment, steps 3–6 read off what
the alignment transports, and steps 7–9 read off its limits: what an alignment
may never do (identify an item with its own class), and how a *lossy* alignment
differs from a conservative one.

As before, nothing here is used by the rest of the development and every step is
a one- or two-line theorem.
-/

namespace Wikidata
namespace BabyStepsAlignment

open Ontology
open BabySteps (tiny)

/-! ## Step 0: the target ontology

Four items again, but this time an upper-ontology-style vocabulary: a person, the
class of persons, the more general class of agents, and a metaclass. -/

/-- The four items of the upper ontology. -/
inductive Ext
  | douglas
  | person
  | agent
  | kindOfOrganism
  deriving DecidableEq, Repr

open Ext

/-- The only *subclass of* statement of the upper ontology: `person ⊑ agent`. -/
def extSub : Ext → Ext → Prop
  | person, agent => True
  | _, _ => False

/-- The *instance of* statements of the upper ontology: `douglas` is a person, and
the class `person` is an instance of the metaclass `kindOfOrganism`. -/
def extInst : Ext → Ext → Prop
  | douglas, person => True
  | person, kindOfOrganism => True
  | _, _ => False

/-- The metaclass levels of the upper ontology. -/
def extLvl : Ext → ℕ
  | douglas => 0
  | person => 1
  | agent => 1
  | kindOfOrganism => 2

instance decExtSub (a b : Ext) : Decidable (extSub a b) := by
  cases a <;> cases b <;> unfold extSub <;> infer_instance

instance decExtInst (a b : Ext) : Decidable (extInst a b) := by
  cases a <;> cases b <;> unfold extInst <;> infer_instance

/-! ## Step 1: the obligations, and the upper ontology itself

Exactly the four checks of `Wikidata.Ontology`, each a finite case analysis. -/

theorem extLvl_inst {a c : Ext} (h : extInst a c) : extLvl c = extLvl a + 1 := by
  cases a <;> cases c <;> simp_all [extInst, extLvl]

theorem extLvl_sub {a b : Ext} (h : extSub a b) : extLvl a = extLvl b := by
  cases a <;> cases b <;> simp_all [extSub, extLvl]

theorem extSub_isClass {a b : Ext} (h : extSub a b) : 0 < extLvl a := by
  cases a <;> cases b <;> simp_all [extSub, extLvl]

/-- A chain of *subclass of* steps in the upper ontology is either empty or the
single step `person ⊑ agent`. -/
theorem reflTransGen_extSub {a b : Ext} (h : Relation.ReflTransGen extSub a b) :
    a = b ∨ (a = person ∧ b = agent) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
      rcases ih with rfl | ⟨rfl, rfl⟩
      · cases a <;> cases c <;> simp_all [extSub]
      · cases c <;> simp_all [extSub]

theorem extSub_antisymm {a b : Ext} (hab : Relation.ReflTransGen extSub a b)
    (hba : Relation.ReflTransGen extSub b a) : a = b := by
  rcases reflTransGen_extSub hab with rfl | ⟨rfl, rfl⟩
  · rfl
  · rcases reflTransGen_extSub hba with h | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- The upper ontology, as an abstract ontology. -/
def upper : Ontology Ext where
  P279 := extSub
  P31 := extInst
  level := extLvl
  level_P31 := extLvl_inst
  level_P279 := extLvl_sub
  P279_isClass := extSub_isClass
  P279_antisymm := extSub_antisymm

/-! ## Step 2: the links, and the alignment

An alignment is a map on items plus a proof that each asserted statement lands in
the *derived* relations of the target. Both proofs are one case analysis. -/

/-- The `equivalent class` links. Note that the Wikidata class `person` is linked
to the *broader* upper-ontology class `agent`: an alignment need not be exact. -/
def link : BabySteps.Item → Ext
  | .adams => douglas
  | .human => person
  | .person => agent
  | .organismName => kindOfOrganism

/-- The links are injective: no two of our four items are conflated. -/
theorem link_injective : Function.Injective link := by
  intro a b h; cases a <;> cases b <;> simp_all [link]

/-- The links form an alignment of `tiny` into `upper`. -/
def align : Alignment tiny upper where
  map := link
  map_P279 := by
    intro a b h
    cases a <;> cases b <;> simp_all [tiny, BabySteps.sub, link]
    exact subclassOf_of_P279 (O := upper) trivial
  map_P31 := by
    intro a c h
    cases a <;> cases c <;> simp_all [tiny, BabySteps.inst, link] <;>
      exact instanceOf_of_P31 (O := upper) trivial

@[simp] theorem align_map (a : BabySteps.Item) : align.map a = link a := rfl

/-! ## Step 3: the asserted facts arrive on the other side -/

/-- `human ⊑ person` becomes `person ⊑ agent`. -/
theorem person_sub_agent : upper.SubclassOf person agent :=
  align.subclassOf BabySteps.human_sub_person

/-- Douglas Adams is a person on the other side too. -/
theorem douglas_inst_person : upper.InstanceOf douglas person :=
  align.instanceOf BabySteps.adams_inst_human

/-! ## Step 4: the *derived* facts arrive as well

The inheritance fact "Douglas Adams is a person" of `BabySteps` — which nobody
asserted there — is transported to "douglas is an agent", which nobody asserted
here either. -/

/-- Douglas Adams is an agent. -/
theorem douglas_inst_agent : upper.InstanceOf douglas agent :=
  align.instanceOf BabySteps.adams_inst_person

/-- And it is genuinely derived: no `instance of` statement of the upper ontology
says so. -/
theorem not_extInst_douglas_agent : ¬ upper.P31 douglas agent := by
  simp [upper, extInst]

/-! ## Step 5: classes, metaclasses and levels are transported -/

/-- `human` has an instance, so its image `person` is a class of the upper
ontology. -/
theorem person_isClass : upper.IsClass person :=
  align.isClass ⟨_, BabySteps.adams_inst_human⟩

/-- The metaclass stays a metaclass. -/
theorem kindOfOrganism_isMetaclass : upper.IsMetaclass kindOfOrganism :=
  align.isMetaclass BabySteps.organismName_isMetaclass

/-- Levels need not agree across an alignment, but the *step* between an instance
and its class always does. -/
theorem level_step_person :
    upper.level (link .organismName) = upper.level (link .human) + 1 :=
  align.level_step BabySteps.human_inst_organismName

/-! ## Step 6: the non-facts survive too

`instance of` is not transitive in `tiny`, and the alignment does not smuggle in
the missing fact: `douglas` is not an instance of the metaclass. -/

theorem douglas_not_inst_kindOfOrganism : ¬ upper.InstanceOf douglas kindOfOrganism := by
  intro h
  have := level_instanceOf h
  simp [upper, extLvl] at this

/-! ## Step 7: identity and composition

Alignments form a category: `tiny` is aligned with itself, and aligning twice is
an alignment. -/

/-- Prefixing with the identity alignment changes nothing. -/
theorem id_comp_align : ((Alignment.id tiny).comp align).map = link := rfl

/-- Aligning `tiny` with itself and then with `upper` is again our alignment. -/
theorem comp_id_align : (align.comp (Alignment.id upper)).map = link := rfl

/-! ## Step 8: what an alignment can never do

An alignment may merge two classes, but it can never identify an item with a
class it is an instance of: that would make something an instance of itself,
which the level discipline forbids. -/

/-- No alignment out of an ontology identifies an item with one of its classes. -/
theorem map_ne_of_P31 {I J : Type*} {O₁ : Ontology I} {O₂ : Ontology J}
    (F : Alignment O₁ O₂) {a c : I} (h : O₁.P31 a c) : F.map a ≠ F.map c := by
  intro heq
  refine not_instanceOf_self (O := O₂) (F.map a) ?_
  simpa [heq] using F.map_P31 h

/-- In particular Douglas Adams and the class `human` can never be linked to the
same item of any ontology. -/
theorem link_adams_ne_link_human {J : Type*} {O : Ontology J} (F : Alignment tiny O) :
    F.map .adams ≠ F.map .human :=
  map_ne_of_P31 F (O₁ := tiny) trivial

/-! ## Step 9: conservative versus lossy alignments

Our alignment is **conservative**: it creates no new subclass facts between
linked items. A different, lossy alignment — one that merges `human` and
`person` — is not. -/

/-- The alignment reflects the class hierarchy: a subclass fact between images
was already a subclass fact here. -/
theorem align_reflects {a b : BabySteps.Item} (h : upper.SubclassOf (link a) (link b)) :
    tiny.SubclassOf a b := by
  rcases reflTransGen_extSub h with heq | ⟨ha, hb⟩
  · rw [link_injective heq]
  · have ha' : a = .human := by cases a <;> simp_all [link]
    have hb' : b = .person := by cases b <;> simp_all [link]
    subst ha'; subst hb'
    exact BabySteps.human_sub_person

/-- Hence the class hierarchy of `tiny` is exactly what the upper ontology says
about the linked items. -/
theorem align_conservative {a b : BabySteps.Item} :
    upper.SubclassOf (link a) (link b) ↔ tiny.SubclassOf a b :=
  align.subclassOf_iff (fun h => align_reflects h)

/-- The lossy links: `human` and `person` are both sent to `person`. -/
def merge : BabySteps.Item → Ext
  | .adams => douglas
  | .human => person
  | .person => person
  | .organismName => kindOfOrganism

/-- They still form an alignment: everything asserted in `tiny` remains true of
the images. -/
def mergeAlign : Alignment tiny upper where
  map := merge
  map_P279 := by
    intro a b h
    cases a <;> cases b <;> simp_all [tiny, BabySteps.sub, merge]
    exact subclassOf_refl (O := upper) person
  map_P31 := by
    intro a c h
    cases a <;> cases c <;> simp_all [tiny, BabySteps.inst, merge] <;>
      exact instanceOf_of_P31 (O := upper) trivial

/-- But it is *not* conservative: after the merge, `person` looks like a subclass
of `human`, which it is not. -/
theorem mergeAlign_not_conservative :
    ¬ ∀ {a b : BabySteps.Item}, upper.SubclassOf (mergeAlign.map a) (mergeAlign.map b) →
      tiny.SubclassOf a b := by
  intro h
  exact BabySteps.person_not_sub_human (h (a := .person) (b := .human) (by rfl))

end BabyStepsAlignment
end Wikidata
