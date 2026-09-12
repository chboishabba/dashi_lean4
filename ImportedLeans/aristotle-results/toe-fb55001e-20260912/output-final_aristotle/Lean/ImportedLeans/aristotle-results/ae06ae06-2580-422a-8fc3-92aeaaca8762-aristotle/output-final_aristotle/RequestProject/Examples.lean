import RequestProject.SelfDescription

/-!
# Worked examples

A small, executable fragment of the Wikidata ontology, and the checks one can run
on it. All the facts below are decided by computation (`decide`), and the
statements about the abstract semantics are obtained from them through the
certification theorems of `RequestProject.Engine`.

The identifiers follow Wikidata (`Q42` Douglas Adams, `Q5` human, `Q215627`
person, `Q35120` entity, `Q55983715` "organisms known by a particular common
name", `Q19478619` metaclass, `Q11424` film); the fragment itself is of course
only a stylised excerpt.
-/

namespace Wikidata
namespace Examples

open KB

/-- Abbreviation for an ordinary Wikidata entity. -/
def Q (s : String) : Qid := .wd s

/-! ### A fragment of Wikidata -/

/-- Douglas Adams is a human, humans are persons, persons are entities; the class
`human` is itself an instance of the metaclass "organisms known by a particular
common name", which in turn is an instance of `metaclass`. `human` and `film` are
disjoint. -/
def wdCore : KB where
  name := "wd-core"
  items := [Q "Q42", Q "Q5", Q "Q215627", Q "Q35120", Q "Q55983715", Q "Q19478619", Q "Q11424"]
  levels := [(Q "Q42", 0), (Q "Q5", 1), (Q "Q215627", 1), (Q "Q35120", 1),
             (Q "Q55983715", 2), (Q "Q19478619", 3), (Q "Q11424", 1)]
  sub := [(Q "Q5", Q "Q215627"), (Q "Q215627", Q "Q35120")]
  inst := [(Q "Q42", Q "Q5"), (Q "Q5", Q "Q55983715"), (Q "Q55983715", Q "Q19478619")]
  disj := [(Q "Q5", Q "Q11424")]

/-- The fragment passes every ontology check. -/
theorem wdCore_valid : wdCore.valid = true := by decide

/-- Derived subclass: `human ⊑ entity`. -/
theorem human_subclassOf_entity : wdCore.isSubclassOf (Q "Q5") (Q "Q35120") = true := by decide

/-- Inheritance: Douglas Adams is an entity, although only `instance of human` is
asserted. -/
theorem adams_instanceOf_entity : wdCore.isInstanceOf (Q "Q42") (Q "Q35120") = true := by decide

/-- `instance of` is **not** transitive: Douglas Adams is an instance of `human`
and `human` is an instance of the metaclass `Q55983715`, but Douglas Adams is not
an instance of `Q55983715`. -/
theorem adams_not_instanceOf_metaclass :
    wdCore.isInstanceOf (Q "Q42") (Q "Q5") = true ∧
    wdCore.isInstanceOf (Q "Q5") (Q "Q55983715") = true ∧
    wdCore.isInstanceOf (Q "Q42") (Q "Q55983715") = false := by decide

/-- `Q55983715` really is a metaclass: it has an instance which itself has
instances. -/
theorem metaclass_is_metaclass : wdCore.isMetaclassB (Q "Q55983715") = true := by decide

/-- The classes Douglas Adams belongs to, computed. -/
example : wdCore.classesOf (Q "Q42") = [Q "Q5", Q "Q215627", Q "Q35120"] := by decide

/-! ### Transfer to the abstract model -/

/-- The abstract ontology determined by the fragment. -/
def wdOnt : Ontology Qid := wdCore.toOntology wdCore_valid

theorem adams_instanceOf_entity' : wdOnt.InstanceOf (Q "Q42") (Q "Q35120") :=
  (isInstanceOf_iff_instanceOf wdCore_valid _ _).1 adams_instanceOf_entity

theorem adams_not_instanceOf_metaclass' : ¬ wdOnt.InstanceOf (Q "Q42") (Q "Q55983715") := by
  intro h
  have := (isInstanceOf_iff_instanceOf wdCore_valid (Q "Q42") (Q "Q55983715")).2 h
  rw [adams_not_instanceOf_metaclass.2.2] at this
  exact Bool.false_ne_true this

/-- In a Wikidata-style ontology, `instance of` is not a transitive relation. -/
theorem instanceOf_not_transitive :
    ∃ (I : Type) (O : Ontology I) (a b c : I),
      O.InstanceOf a b ∧ O.InstanceOf b c ∧ ¬ O.InstanceOf a c := by
  refine ⟨Qid, wdOnt, Q "Q42", Q "Q5", Q "Q55983715", ?_, ?_, adams_not_instanceOf_metaclass'⟩
  · exact (isInstanceOf_iff_instanceOf wdCore_valid _ _).1 adams_not_instanceOf_metaclass.1
  · exact (isInstanceOf_iff_instanceOf wdCore_valid _ _).1 adams_not_instanceOf_metaclass.2.1

/-- Nothing in the fragment is an instance of itself — an instance of the general
theorem `Ontology.not_instanceOf_self`. -/
theorem no_self_instance (a : Qid) : ¬ wdOnt.InstanceOf a a :=
  Ontology.not_instanceOf_self a

/-! ### Ontologies that the validator rejects -/

/-- Wrong metaclass levels: an individual declared to be an instance of another
individual. -/
def badLevels : KB where
  items := [Q "A", Q "B"]
  levels := [(Q "A", 0), (Q "B", 0)]
  inst := [(Q "A", Q "B")]

theorem badLevels_invalid : badLevels.valid = false := by decide

/-- A cycle in the class hierarchy. -/
def cyclic : KB where
  items := [Q "A", Q "B"]
  levels := [(Q "A", 1), (Q "B", 1)]
  sub := [(Q "A", Q "B"), (Q "B", Q "A")]

theorem cyclic_invalid : cyclic.valid = false := by decide

/-- Two classes declared disjoint, yet sharing an inherited instance. -/
def disjointViolation : KB where
  items := [Q "x", Q "A", Q "B", Q "C"]
  levels := [(Q "x", 0), (Q "A", 1), (Q "B", 1), (Q "C", 1)]
  sub := [(Q "C", Q "A"), (Q "C", Q "B")]
  inst := [(Q "x", Q "C")]
  disj := [(Q "A", Q "B")]

theorem disjointViolation_invalid : disjointViolation.valid = false := by decide

/-! ### Reasoning about other ontologies -/

/-- A second, independent ontology: `Q11424` (film) with an instance. -/
def filmKB : KB where
  name := "films"
  items := [Q "Q25188", Q "Q11424"]
  levels := [(Q "Q25188", 0), (Q "Q11424", 1)]
  inst := [(Q "Q25188", Q "Q11424")]

theorem filmKB_valid : filmKB.valid = true := by decide

/-- Importing an ontology loses nothing: the merge entails both parts. -/
theorem merged_entails_both :
    (wdCore.merge filmKB).Entails wdCore = true ∧
    (wdCore.merge filmKB).Entails filmKB = true :=
  ⟨merge_entails_left (valid_wellFormed wdCore_valid) (valid_wellFormed filmKB_valid),
   merge_entails_right (valid_wellFormed wdCore_valid) (valid_wellFormed filmKB_valid)⟩

/-- Merging these two ontologies is consistent, and the result knows facts from
both, including that the film `Q25188` is not a human. -/
theorem merged_valid : (wdCore.merge filmKB).valid = true := by decide

theorem merged_knows :
    (wdCore.merge filmKB).isInstanceOf (Q "Q42") (Q "Q35120") = true ∧
    (wdCore.merge filmKB).isInstanceOf (Q "Q25188") (Q "Q11424") = true ∧
    (wdCore.merge filmKB).isInstanceOf (Q "Q25188") (Q "Q5") = false := by decide

/-- Validity is *not* automatic under import: here two individually valid
ontologies contradict each other, and the merge is rejected. `leftKB` says the
class `C` is a subclass of `A`, `rightKB` says `A` is a subclass of `C`. -/
def leftKB : KB where
  name := "left"
  items := [Q "A", Q "C"]
  levels := [(Q "A", 1), (Q "C", 1)]
  sub := [(Q "C", Q "A")]

/-- The companion of `leftKB` with the opposite subclass statement. -/
def rightKB : KB where
  name := "right"
  items := [Q "A", Q "C"]
  levels := [(Q "A", 1), (Q "C", 1)]
  sub := [(Q "A", Q "C")]

theorem incompatible_merge :
    leftKB.valid = true ∧ rightKB.valid = true ∧ (leftKB.merge rightKB).valid = false := by
  decide

/-! ### Ontologies describing themselves and each other -/

/-- The meta-description of the fragment is a valid ontology. -/
theorem wdCore_selfDescription_valid : (wdCore.selfDescription).valid = true :=
  selfDescription_valid wdCore

/-- ... and so is the meta-description of the meta-description. -/
theorem wdCore_selfDescription_selfDescription_valid :
    ((wdCore.selfDescription).selfDescription).valid = true :=
  selfDescription_valid _

/-- The meta-ontology contains an item denoting the ontology it describes. -/
theorem meta_knows_wdCore :
    (wdCore.selfDescription).isInstanceOf (Qid.ont "wd-core") (Qid.lvl 0) = true := by decide

/-- The meta-ontology classifies `human` as a level-1 class and the metaclass
`Q55983715` as a level-2 class. -/
theorem meta_classifies :
    (wdCore.selfDescription).isInstanceOf (Qid.about (Q "Q5")) (Qid.lvl 1) = true ∧
    (wdCore.selfDescription).isInstanceOf (Qid.about (Q "Q55983715")) (Qid.lvl 2) = true := by
  decide

/-- The tower of level classes: the class of individuals is an instance of the
class of level-1 classes. -/
theorem meta_tower :
    (wdCore.selfDescription).isInstanceOf (Qid.lvl 0) (Qid.lvl 1) = true := by decide

/-- A single ontology carrying descriptions of two different ontologies at once. -/
def metaBoth : KB := (wdCore.selfDescription).merge (filmKB.selfDescription)

theorem metaBoth_valid : metaBoth.valid = true := by decide

theorem metaBoth_knows_both :
    metaBoth.isInstanceOf (Qid.ont "wd-core") (Qid.lvl 0) = true ∧
    metaBoth.isInstanceOf (Qid.ont "films") (Qid.lvl 0) = true := by decide

end Examples
end Wikidata
