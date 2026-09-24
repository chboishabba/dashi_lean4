import RequestProject.PropertyConstraints
import RequestProject.Examples

/-!
# A fragment of the Wikidata upper ontology, with properties

This file ingests a larger fragment of the ontology described by
*Wikidata:WikiProject Ontology*: the upper level of the class hierarchy (entity,
object, concrete/abstract object, person, human, painting, geographic region,
administrative territorial entity), the metaclass tower above it (first-order
class, second-order class, and the "organisms known by a particular common name"
metaclass), individuals, and two property layers on top of the same items:

* `wdParts` — the meronomy and territorial containment layer: `part of` (P361) and
  `located in the administrative territorial entity` (P131), the latter a
  subproperty of the former, both declared transitive, with type and value-type
  constraints. It has no symmetry and no inverse declarations and its transitivity
  declarations are inherited upwards, so the engine decides its derived statements
  *exactly* (`wdParts_relatedB_iff_holds`).
* `wdSocial` — a layer using the features the first one avoids: the symmetric
  properties `spouse` (P26), `relative` (P1038) and `different from` (P1889), and
  the inverse pair `part of` (P361) / `has part(s)` (P527).

Everything below is decided by computation and then transported to the abstract
model of `RequestProject.Core` and `RequestProject.Properties` through the
certification theorems.

The last section formalises a well-known tension in the Wikidata ontology: the item
`class` (Q16889133) is meant to have both first-order and second-order classes among
its subclasses, and `no_variable_order_class` shows that no strictly stratified
ontology can do that. The stratified replacement is the tower of level classes of
`RequestProject.SelfDescription`.

As in `RequestProject.Examples`, the identifiers follow Wikidata but the fragment is
a stylised excerpt, not a dump; the theorems are statements about this fragment.
-/

namespace Wikidata
namespace Upper

open KB PKB

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a Wikidata property. -/
def P (s : String) : Pid := .wd s

/-! ### The items -/

/-- English labels for the identifiers used below. -/
def labels : List (Qid × String) :=
  [(Q "Q42", "Douglas Adams"), (Q "Q14623681", "Jane Belson"), (Q "Q12418", "Mona Lisa"),
   (Q "Q84", "London"), (Q "Q21", "England"), (Q "Q145", "United Kingdom"), (Q "Q46", "Europe"),
   (Q "Q35120", "entity"), (Q "Q488383", "object"), (Q "Q4406616", "concrete object"),
   (Q "Q7184903", "abstract object"), (Q "Q5", "human"), (Q "Q215627", "person"),
   (Q "Q3305213", "painting"), (Q "Q82794", "geographic region"),
   (Q "Q56061", "administrative territorial entity"),
   (Q "Q104086571", "first-order class"), (Q "Q55983715",
     "organisms known by a particular common name"), (Q "Q24017414", "second-order class")]

/-- The label of an identifier, or its raw form if none is recorded. -/
def labelOf (q : Qid) : String := (labels.lookup q).getD (toString (repr q))

/-- The item ontology: the upper classes, the metaclass tower, and some individuals. -/
def wdBase : KB where
  name := "wd-upper"
  items := [Q "Q42", Q "Q14623681", Q "Q12418", Q "Q84", Q "Q21", Q "Q145", Q "Q46",
            Q "Q35120", Q "Q488383", Q "Q4406616", Q "Q7184903", Q "Q5", Q "Q215627",
            Q "Q3305213", Q "Q82794", Q "Q56061",
            Q "Q104086571", Q "Q55983715", Q "Q24017414"]
  levels := [(Q "Q42", 0), (Q "Q14623681", 0), (Q "Q12418", 0), (Q "Q84", 0), (Q "Q21", 0),
             (Q "Q145", 0), (Q "Q46", 0),
             (Q "Q35120", 1), (Q "Q488383", 1), (Q "Q4406616", 1), (Q "Q7184903", 1),
             (Q "Q5", 1), (Q "Q215627", 1), (Q "Q3305213", 1), (Q "Q82794", 1), (Q "Q56061", 1),
             (Q "Q104086571", 2), (Q "Q55983715", 2), (Q "Q24017414", 3)]
  sub := [(Q "Q488383", Q "Q35120"), (Q "Q7184903", Q "Q35120"), (Q "Q4406616", Q "Q488383"),
          (Q "Q215627", Q "Q4406616"), (Q "Q5", Q "Q215627"), (Q "Q3305213", Q "Q4406616"),
          (Q "Q82794", Q "Q4406616"), (Q "Q56061", Q "Q82794")]
  inst := [(Q "Q42", Q "Q5"), (Q "Q14623681", Q "Q5"), (Q "Q12418", Q "Q3305213"),
           (Q "Q84", Q "Q56061"), (Q "Q21", Q "Q56061"), (Q "Q145", Q "Q56061"),
           (Q "Q46", Q "Q82794"),
           (Q "Q5", Q "Q104086571"), (Q "Q5", Q "Q55983715"), (Q "Q3305213", Q "Q104086571"),
           (Q "Q104086571", Q "Q24017414"), (Q "Q55983715", Q "Q24017414")]
  disj := [(Q "Q5", Q "Q3305213")]

set_option maxRecDepth 40000 in
/-- The item ontology passes every check of the validator. -/
theorem wdBase_valid : wdBase.valid = true := by decide

/-- The abstract ontology determined by the fragment. -/
def wdOnt : Ontology Qid := wdBase.toOntology wdBase_valid

set_option maxRecDepth 40000 in
/-- Inheritance through the upper hierarchy: Douglas Adams is an entity, the Mona
Lisa is an object, London is a concrete object. -/
theorem inherited_instances :
    wdBase.isInstanceOf (Q "Q42") (Q "Q35120") = true ∧
    wdBase.isInstanceOf (Q "Q12418") (Q "Q488383") = true ∧
    wdBase.isInstanceOf (Q "Q84") (Q "Q4406616") = true := by decide

set_option maxRecDepth 40000 in
/-- Douglas Adams is a human. -/
theorem adams_instanceOf_human : wdBase.isInstanceOf (Q "Q42") (Q "Q5") = true := by decide

set_option maxRecDepth 40000 in
/-- `human` and `painting` are first-order classes; `first-order class` is itself an
instance of `second-order class`. -/
theorem class_orders :
    wdBase.isInstanceOf (Q "Q5") (Q "Q104086571") = true ∧
    wdBase.isInstanceOf (Q "Q3305213") (Q "Q104086571") = true ∧
    wdBase.isInstanceOf (Q "Q104086571") (Q "Q24017414") = true := by decide

set_option maxRecDepth 40000 in
/-- `first-order class` and the metaclass "organisms known by a particular common
name" really are metaclasses: they have instances that themselves have instances. -/
theorem metaclasses :
    wdBase.isMetaclassB (Q "Q104086571") = true ∧
    wdBase.isMetaclassB (Q "Q55983715") = true := by decide

/-- Transported to the abstract model: `first-order class` is a metaclass, so its
instances are classes and it lives at level at least `2`. -/
theorem firstOrderClass_isMetaclass : wdOnt.IsMetaclass (Q "Q104086571") :=
  ⟨Q "Q5", (isInstanceOf_iff_instanceOf wdBase_valid _ _).1 class_orders.1,
    Q "Q42", (isInstanceOf_iff_instanceOf wdBase_valid _ _).1 adams_instanceOf_human⟩

theorem instances_of_firstOrderClass_are_classes {a : Qid}
    (h : wdOnt.InstanceOf a (Q "Q104086571")) : wdOnt.IsClass a :=
  Ontology.isClass_of_instanceOf_metaclass firstOrderClass_isMetaclass h

set_option maxRecDepth 40000 in
/-- The disjointness declaration is respected: no item is both a human and a
painting. -/
theorem human_painting_disjoint :
    wdBase.items.all (fun a =>
      !(wdBase.isInstanceOf a (Q "Q5") && wdBase.isInstanceOf a (Q "Q3305213"))) = true := by
  decide

/-! ### The meronomy layer: `part of` and territorial containment -/

/-- `located in the administrative territorial entity` (P131) is a subproperty of
`part of` (P361); both are transitive, and both carry type and value-type
constraints. -/
def wdParts : PKB where
  base := wdBase
  props := [P "P361", P "P131"]
  subProp := [(P "P131", P "P361")]
  stmts := [(P "P131", Q "Q84", Q "Q21"), (P "P131", Q "Q21", Q "Q145"),
            (P "P361", Q "Q145", Q "Q46")]
  transProps := [P "P361", P "P131"]
  typeC := [(P "P361", Q "Q35120"), (P "P131", Q "Q82794")]
  valueTypeC := [(P "P361", Q "Q35120"), (P "P131", Q "Q82794")]

set_option maxRecDepth 40000 in
/-- The layer passes the full validator, including the property constraints. -/
theorem wdParts_pvalid : wdParts.pvalid = true := by decide

set_option maxRecDepth 40000 in
theorem wdParts_transUpwardClosed : wdParts.transUpwardClosed = true := by decide

theorem wdParts_pWellFormed : wdParts.pWellFormed = true := pvalid_pWellFormed wdParts_pvalid

set_option maxRecDepth 40000 in
/-- Transitivity across the property hierarchy: London is part of Europe, although
the only statements are `London P131 England`, `England P131 United Kingdom` and
`United Kingdom P361 Europe`. -/
theorem london_part_of_europe : wdParts.relatedB (P "P361") (Q "Q84") (Q "Q46") = true := by
  decide

set_option maxRecDepth 40000 in
/-- Transitivity within P131: London is located in the United Kingdom. -/
theorem london_in_uk : wdParts.relatedB (P "P131") (Q "Q84") (Q "Q145") = true := by decide

set_option maxRecDepth 40000 in
/-- The subproperty relation is not reversed: London is *not* stated to be located in
the administrative territorial entity Europe, because the last step of the chain is a
`part of` statement only. -/
theorem london_not_in_europe : wdParts.relatedB (P "P131") (Q "Q84") (Q "Q46") = false := by
  decide

set_option maxRecDepth 40000 in
/-- The computed values of `part of` at London. -/
example : wdParts.valuesOf (P "P361") (Q "Q84") = [Q "Q21", Q "Q145", Q "Q46"] := by decide

/-- For this layer the engine decides derivability in the abstract model exactly. -/
theorem wdParts_relatedB_iff_holds (p : Pid) (s o : Qid) :
    wdParts.relatedB p s o = true ↔ wdParts.toLayer.Holds p s o :=
  relatedB_iff_holds wdParts_pWellFormed rfl rfl wdParts_transUpwardClosed p s o

/-- Hence, in the abstract property layer, London is part of Europe ... -/
theorem holds_london_part_of_europe :
    wdParts.toLayer.Holds (P "P361") (Q "Q84") (Q "Q46") :=
  (wdParts_relatedB_iff_holds _ _ _).1 london_part_of_europe

/-- ... and it is *not* derivable that London is located in the administrative
territorial entity Europe. -/
theorem not_holds_london_in_europe :
    ¬ wdParts.toLayer.Holds (P "P131") (Q "Q84") (Q "Q46") := by
  intro h
  have := (wdParts_relatedB_iff_holds _ _ _).2 h
  rw [london_not_in_europe] at this
  exact Bool.false_ne_true this

/-- The type constraints of the layer hold in the abstract model. -/
theorem wdParts_subjectTypeOk :
    PropertyLayer.Constraints.SubjectTypeOk (wdParts.base.toOntology (pvalid_base wdParts_pvalid))
      wdParts.toLayer wdParts.toConstraints :=
  subjectTypeOk_of_pvalid wdParts_pvalid rfl rfl wdParts_transUpwardClosed

/-- The value-type constraints of the layer hold in the abstract model. -/
theorem wdParts_valueTypeOk :
    PropertyLayer.Constraints.ValueTypeOk (wdParts.base.toOntology (pvalid_base wdParts_pvalid))
      wdParts.toLayer wdParts.toConstraints :=
  valueTypeOk_of_pvalid wdParts_pvalid rfl rfl wdParts_transUpwardClosed

/-- A consequence of the constraints: every subject of a derived `part of` statement
is an entity, even the ones obtained by transitivity through P131. -/
theorem subject_of_partOf_isEntity {s o : Qid}
    (h : wdParts.toLayer.Holds (P "P361") s o) :
    (wdParts.base.toOntology (pvalid_base wdParts_pvalid)).InstanceOf s (Q "Q35120") :=
  wdParts_subjectTypeOk (by simp [PKB.toConstraints, wdParts]) h

/-- A property knowledge base whose statements violate a type constraint is rejected:
here the Mona Lisa, a painting, is declared to be located in an administrative
territorial entity. -/
def badConstraint : PKB where
  base := wdBase
  props := [P "P131"]
  stmts := [(P "P131", Q "Q12418", Q "Q21")]
  typeC := [(P "P131", Q "Q82794")]

set_option maxRecDepth 40000 in
theorem badConstraint_invalid : badConstraint.pvalid = false := by decide

/-! ### `part of` is a strict order on the fragment -/

set_option maxRecDepth 40000 in
/-- The irreflexive constraint holds for `part of`: no item of the fragment is part
of itself. -/
theorem partOf_irreflexiveB : wdParts.irreflexiveB (P "P361") = true := by decide

/-- In the abstract model, no item is part of itself. -/
theorem partOf_irreflexive (s : Qid) : ¬ wdParts.toLayer.Holds (P "P361") s s :=
  irreflexive_of_irreflexiveB wdParts_pWellFormed rfl rfl wdParts_transUpwardClosed
    partOf_irreflexiveB s

set_option maxRecDepth 40000 in
theorem partOf_isTrans : wdParts.isTransB (P "P361") = true := by decide

/-- `part of` is asymmetric on the fragment. -/
theorem partOf_asymm {a b : Qid} (hab : wdParts.toLayer.Holds (P "P361") a b)
    (hba : wdParts.toLayer.Holds (P "P361") b a) : False :=
  PropertyLayer.asymm_of_irrefl_trans (by simpa [PKB.toLayer, PKB.isTransB] using partOf_isTrans)
    partOf_irreflexive hab hba

/-- `part of` is acyclic on the fragment: no chain of `part of` statements returns to
its starting point, so it is a strict partial order. -/
theorem partOf_acyclic (a : Qid) :
    ¬ Relation.TransGen (wdParts.toLayer.Holds (P "P361")) a a :=
  acyclic_of_irreflexiveB wdParts_pWellFormed rfl rfl wdParts_transUpwardClosed partOf_isTrans
    partOf_irreflexiveB a

set_option maxRecDepth 40000 in
/-- A transitive property is typically *not* single-valued: London is part of
England, of the United Kingdom and of Europe. -/
theorem partOf_not_singleValued : wdParts.singleValueB (P "P361") = false := by decide

/-! ### A single-valued, distinct-valued property -/

/-- `capital` (P36) relates a territorial entity to its capital. -/
def wdCapital : PKB where
  base := wdBase
  props := [P "P36"]
  stmts := [(P "P36", Q "Q145", Q "Q84")]
  typeC := [(P "P36", Q "Q82794")]
  valueTypeC := [(P "P36", Q "Q82794")]

set_option maxRecDepth 40000 in
theorem wdCapital_pvalid : wdCapital.pvalid = true := by decide

theorem wdCapital_pWellFormed : wdCapital.pWellFormed = true :=
  pvalid_pWellFormed wdCapital_pvalid

set_option maxRecDepth 40000 in
theorem wdCapital_transUpwardClosed : wdCapital.transUpwardClosed = true := by decide

set_option maxRecDepth 40000 in
theorem wdCapital_singleValueB : wdCapital.singleValueB (P "P36") = true := by decide

set_option maxRecDepth 40000 in
theorem wdCapital_distinctValuesB : wdCapital.distinctValuesB (P "P36") = true := by decide

/-- In the abstract model, `capital` has at most one value per subject ... -/
theorem capital_singleValued : wdCapital.toLayer.SingleValued (P "P36") :=
  singleValued_of_singleValueB wdCapital_pWellFormed rfl rfl wdCapital_transUpwardClosed
    wdCapital_singleValueB

/-- ... and at most one subject per value, so it is a partial injection. -/
theorem capital_distinctValued : wdCapital.toLayer.DistinctValued (P "P36") :=
  distinctValued_of_distinctValuesB wdCapital_pWellFormed rfl rfl wdCapital_transUpwardClosed
    wdCapital_distinctValuesB

/-! ### The social layer: symmetric properties and inverse pairs -/

/-- `spouse` (P26) is a symmetric subproperty of `relative` (P1038), `different from`
(P1889) is symmetric, and `part of` (P361) and `has part(s)` (P527) are inverse. -/
def wdSocial : PKB where
  base := wdBase
  props := [P "P1038", P "P26", P "P361", P "P527", P "P1889"]
  subProp := [(P "P26", P "P1038")]
  stmts := [(P "P26", Q "Q42", Q "Q14623681"), (P "P361", Q "Q84", Q "Q21"),
            (P "P1889", Q "Q42", Q "Q12418")]
  symProps := [P "P26", P "P1038", P "P1889"]
  inverses := [(P "P361", P "P527")]
  typeC := [(P "P26", Q "Q5")]
  valueTypeC := [(P "P26", Q "Q5")]

set_option maxRecDepth 40000 in
theorem wdSocial_pvalid : wdSocial.pvalid = true := by decide

theorem wdSocial_pWellFormed : wdSocial.pWellFormed = true := pvalid_pWellFormed wdSocial_pvalid

set_option maxRecDepth 40000 in
/-- Symmetry: the spouse statement holds in both directions. -/
theorem spouse_symmetric :
    wdSocial.relatedB (P "P26") (Q "Q42") (Q "Q14623681") = true ∧
    wdSocial.relatedB (P "P26") (Q "Q14623681") (Q "Q42") = true := by decide

set_option maxRecDepth 40000 in
/-- Subproperty inheritance, combined with symmetry: the two are relatives, in both
directions. -/
theorem relatives :
    wdSocial.relatedB (P "P1038") (Q "Q42") (Q "Q14623681") = true ∧
    wdSocial.relatedB (P "P1038") (Q "Q14623681") (Q "Q42") = true := by decide

set_option maxRecDepth 40000 in
/-- The inverse pair: from `London part of England` the engine derives
`England has part London`. -/
theorem england_has_part_london :
    wdSocial.relatedB (P "P527") (Q "Q21") (Q "Q84") = true := by decide

set_option maxRecDepth 40000 in
/-- Inverses are not confused with the property itself: `London has part England` is
not derived. -/
theorem london_not_has_part_england :
    wdSocial.relatedB (P "P527") (Q "Q84") (Q "Q21") = false := by decide

/-- Transported to the abstract model (by soundness of the engine). -/
theorem holds_england_has_part_london :
    wdSocial.toLayer.Holds (P "P527") (Q "Q21") (Q "Q84") :=
  holds_of_relatedB wdSocial_pWellFormed england_has_part_london

theorem holds_relatives :
    wdSocial.toLayer.Holds (P "P1038") (Q "Q14623681") (Q "Q42") :=
  holds_of_relatedB wdSocial_pWellFormed relatives.2

/-- In the abstract model the derived `has part(s)` statements are exactly the
reversed `part of` statements. -/
theorem holds_hasPart_iff_partOf (s o : Qid) :
    wdSocial.toLayer.Holds (P "P527") s o ↔ wdSocial.toLayer.Holds (P "P361") o s :=
  have hinv : wdSocial.toLayer.InverseOf (P "P361") (P "P527") := Or.inl (by simp [wdSocial])
  (PropertyLayer.holds_inverse_iff hinv o s).symm

/-! ### Why Wikidata's `class` cannot be strictly stratified

On Wikidata the item `class` (Q16889133) is a *variable-order* class: both
`first-order class` (whose instances are classes of individuals) and
`second-order class` (whose instances are classes of classes) are meant to be
subclasses of it. In a strictly stratified ontology this is impossible, because
`subclass of` preserves the metaclass level. -/

/-- Two classes with a common superclass sit at the same metaclass level. -/
theorem level_eq_of_common_superclass {I : Type*} {O : Ontology I} {a b c : I}
    (ha : O.SubclassOf a c) (hb : O.SubclassOf b c) : O.level a = O.level b := by
  rw [Ontology.level_subclassOf ha, Ontology.level_subclassOf hb]

/-- **No variable-order classes**: in any Wikidata-style ontology, a class `f` with
an individual instance and a class `s` with an instance that itself has instances
cannot have a common superclass. -/
theorem no_variable_order_class {I : Type*} {O : Ontology I} {c f s a b x : I}
    (hf : O.SubclassOf f c) (hs : O.SubclassOf s c)
    (haf : O.InstanceOf a f) (hind : O.IsIndividual a)
    (hbs : O.InstanceOf b s) (hxb : O.InstanceOf x b) : False := by
  have h1 := Ontology.level_instanceOf haf
  have h2 := Ontology.level_instanceOf hbs
  have h3 := Ontology.level_instanceOf hxb
  have h4 := level_eq_of_common_superclass hf hs
  simp only [Ontology.IsIndividual] at hind
  omega

/-- The executable counterpart: a knowledge base declaring `first-order class` and
`second-order class` to be subclasses of one item `class` is rejected by the
validator, whatever level `class` is given (here `Q16889133` is tried at level `2`;
the level table forces `subclass of` to preserve levels). -/
def classTowerBad : KB where
  name := "variable-order class"
  items := [Q "Q16889133", Q "Q104086571", Q "Q24017414"]
  levels := [(Q "Q16889133", 2), (Q "Q104086571", 2), (Q "Q24017414", 3)]
  sub := [(Q "Q104086571", Q "Q16889133"), (Q "Q24017414", Q "Q16889133")]

set_option maxRecDepth 40000 in
theorem classTowerBad_invalid : classTowerBad.valid = false := by decide

/-- The stratified replacement used in this development is the tower of level
classes: `lvl n` is the class of all items of metaclass level `n`, and `lvl n` is an
instance of `lvl (n+1)`. It is generated automatically for any knowledge base and is
always valid. -/
theorem levelTower_valid : (wdBase.selfDescription).valid = true :=
  selfDescription_valid wdBase

set_option maxRecDepth 40000 in
/-- In that tower, `first-order class` is classified as a level-2 item and
`second-order class` as a level-3 item — the distinction the single item `class`
cannot make. -/
theorem levelTower_classifies :
    (wdBase.selfDescription).isInstanceOf (Qid.about (Q "Q104086571")) (Qid.lvl 2) = true ∧
    (wdBase.selfDescription).isInstanceOf (Qid.about (Q "Q24017414")) (Qid.lvl 3) = true := by
  decide

end Upper
end Wikidata
