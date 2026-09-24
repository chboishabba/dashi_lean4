import RequestProject.Core

/-!
# Baby steps: the Wikidata ontology, one small step at a time

This file is a gentle, self-contained introduction to the abstract model of
`RequestProject.Core`. Nothing here is used by the rest of the development: the
point is to *build a Wikidata-style ontology from scratch by hand*, discharging
every one of its obligations explicitly, and then to read off the basic
ontological facts in the smallest possible steps.

The running example is the four-item fragment

```
Q42  (Douglas Adams)   --P31-->  Q5 (human)  --P279--> Q215627 (person)
Q5   (human)           --P31-->  Q55983715 ("organisms known by a particular
                                             common name", a metaclass)
```

Every step below is a one- or two-line theorem, and the steps are numbered so
that they can be read in order.
-/

namespace Wikidata
namespace BabySteps

/-! ## Step 0: four items

We do not need strings or identifiers to talk about an ontology: an ontology is
carried by *any* type of items. Ours has exactly four. -/

/-- The four items of our miniature Wikidata: Douglas Adams, human, person, and
the metaclass "organisms known by a particular common name". -/
inductive Item
  | adams
  | human
  | person
  | organismName
  deriving DecidableEq, Repr

open Item

/-! ## Step 1: the raw statements

A Wikidata ontology is nothing but a set of `P279` (*subclass of*) statements, a
set of `P31` (*instance of*) statements, and a metaclass level for each item. We
write the two relations down as plain predicates. -/

/-- The only direct *subclass of* statement: `human ⊑ person`. -/
def sub : Item → Item → Prop
  | human, person => True
  | _, _ => False

/-- The direct *instance of* statements: Douglas Adams is a human, and the class
`human` is an instance of the metaclass `organismName`. -/
def inst : Item → Item → Prop
  | adams, human => True
  | human, organismName => True
  | _, _ => False

/-- The metaclass level: Douglas Adams is an individual (level `0`), `human` and
`person` are classes of individuals (level `1`), and `organismName` is a class of
classes (level `2`). -/
def lvl : Item → ℕ
  | adams => 0
  | human => 1
  | person => 1
  | organismName => 2

instance decSub (a b : Item) : Decidable (sub a b) := by
  cases a <;> cases b <;> unfold sub <;> infer_instance

instance decInst (a b : Item) : Decidable (inst a b) := by
  cases a <;> cases b <;> unfold inst <;> infer_instance

/-! ## Step 2: the obligations

To turn the raw statements into an `Ontology` we must check four things. Each is
a finite case analysis, so each proof is a single `decide`-style step. -/

/-- An instance sits exactly one level below its class. -/
theorem lvl_inst {a c : Item} (h : inst a c) : lvl c = lvl a + 1 := by
  cases a <;> cases c <;> simp_all [inst, lvl]

/-- A class and its superclasses sit at the same level. -/
theorem lvl_sub {a b : Item} (h : sub a b) : lvl a = lvl b := by
  cases a <;> cases b <;> simp_all [sub, lvl]

/-- Only classes take part in *subclass of* statements. -/
theorem sub_isClass {a b : Item} (h : sub a b) : 0 < lvl a := by
  cases a <;> cases b <;> simp_all [sub, lvl]

/-- A chain of *subclass of* steps is either empty or the single step
`human ⊑ person`; there is nowhere else to go. -/
theorem reflTransGen_sub {a b : Item} (h : Relation.ReflTransGen sub a b) :
    a = b ∨ (a = human ∧ b = person) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
      rcases ih with rfl | ⟨rfl, rfl⟩
      · cases a <;> cases c <;> simp_all [sub]
      · cases c <;> simp_all [sub]

/-- Hence the class hierarchy has no genuine cycles. -/
theorem sub_antisymm {a b : Item} (hab : Relation.ReflTransGen sub a b)
    (hba : Relation.ReflTransGen sub b a) : a = b := by
  rcases reflTransGen_sub hab with rfl | ⟨rfl, rfl⟩
  · rfl
  · rcases reflTransGen_sub hba with h | ⟨h, _⟩ <;> exact absurd h (by decide)

/-! ## Step 3: the ontology

With the four obligations discharged, the fragment *is* an ontology in the sense
of `Wikidata.Ontology`. -/

/-- Our miniature Wikidata, as an abstract ontology. -/
def tiny : Ontology Item where
  P279 := sub
  P31 := inst
  level := lvl
  level_P31 := lvl_inst
  level_P279 := lvl_sub
  P279_isClass := sub_isClass
  P279_antisymm := sub_antisymm

/-! ## Step 4: reading off the asserted facts

The two relations of the abstract model, `SubclassOf` and `InstanceOf`, contain
at least what we asserted. -/

/-- `human ⊑ person` — the statement we wrote down. -/
theorem human_sub_person : tiny.SubclassOf human person :=
  Ontology.subclassOf_of_P279 (O := tiny) trivial

/-- Douglas Adams is an instance of `human` — the statement we wrote down. -/
theorem adams_inst_human : tiny.InstanceOf adams human :=
  Ontology.instanceOf_of_P31 (O := tiny) trivial

/-- `human` is an instance of the metaclass. -/
theorem human_inst_organismName : tiny.InstanceOf human organismName :=
  Ontology.instanceOf_of_P31 (O := tiny) trivial

/-! ## Step 5: the first derived fact — inheritance

Nobody asserted that Douglas Adams is a person; it follows, because *instance of*
composes with *subclass of*. -/

/-- Douglas Adams is a person. -/
theorem adams_inst_person : tiny.InstanceOf adams person :=
  Ontology.instanceOf_trans_subclassOf adams_inst_human human_sub_person

/-! ## Step 6: the first *non*-fact — `instance of` is not transitive

Douglas Adams is an instance of `human`, and `human` is an instance of
`organismName`, but Douglas Adams is *not* an instance of `organismName`: he is
not a class of organisms. In the model this is forced by the levels. -/

/-- Douglas Adams is not an instance of the metaclass. -/
theorem adams_not_inst_organismName : ¬ tiny.InstanceOf adams organismName := by
  intro h
  have := Ontology.level_instanceOf h
  simp [tiny, lvl] at this

/-- Spelled out: `instance of` really fails to be transitive in Wikidata. -/
theorem instanceOf_not_transitive :
    ¬ ∀ a b c : Item, tiny.InstanceOf a b → tiny.InstanceOf b c → tiny.InstanceOf a c :=
  fun h => adams_not_inst_organismName
    (h adams human organismName adams_inst_human human_inst_organismName)

/-! ## Step 7: who is what

`IsIndividual`, `IsClass` and `IsMetaclass` are read off from the levels. -/

/-- Douglas Adams is an individual. -/
theorem adams_isIndividual : tiny.IsIndividual adams := rfl

/-- `human` is a class. -/
theorem human_isClass : tiny.IsClass human := Nat.zero_lt_one

/-- `organismName` is a metaclass: it has an instance (`human`) which itself has
an instance (Douglas Adams). -/
theorem organismName_isMetaclass : tiny.IsMetaclass organismName :=
  ⟨human, human_inst_organismName, adams, adams_inst_human⟩

/-- Douglas Adams, being an individual, has no instances at all. -/
theorem adams_no_instances : ¬ tiny.HasInstance adams :=
  Ontology.not_hasInstance_of_isIndividual adams_isIndividual

/-- Douglas Adams, being an individual, has no subclasses either. -/
theorem adams_no_subclasses (b : Item) : ¬ tiny.P279 b adams :=
  Ontology.not_P279_of_isIndividual adams_isIndividual

/-! ## Step 8: the hierarchy is a partial order

Finally, the derived *subclass of* relation orders the items: `person` is not a
subclass of `human`, because that would make the two equal. -/

/-- The class hierarchy of `tiny`, as a partial order. -/
def tinyOrder : PartialOrder Item := Ontology.subclassPartialOrder tiny

/-- `person` is not a subclass of `human`: the one asserted step cannot be
reversed. -/
theorem person_not_sub_human : ¬ tiny.SubclassOf person human := by
  intro h
  have := Ontology.subclassOf_antisymm h human_sub_person
  exact absurd this (by decide)

/-- And no class of ours is a subclass of one of its own instances. -/
theorem organismName_not_sub_human : ¬ tiny.SubclassOf organismName human :=
  Ontology.not_subclassOf_of_instanceOf human_inst_organismName

end BabySteps
end Wikidata
