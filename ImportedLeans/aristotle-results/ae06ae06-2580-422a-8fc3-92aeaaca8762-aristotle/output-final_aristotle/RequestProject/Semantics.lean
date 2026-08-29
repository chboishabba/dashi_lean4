import RequestProject.Examples
import RequestProject.Alignment
import RequestProject.Properties

/-!
# Extensional semantics of the ontology layer

The Wikidata ontology layer (`Wikidata:WikiProject Ontology`) is described in terms of
*extensions*: `subclass of` (P279) is read as "every instance of the subclass is an
instance of the superclass", and `instance of` (P31) as "this item belongs to the
extension of that class".  So far this development has treated the two relations
*proof-theoretically*, as inductively derived facts (`Wikidata.Ontology.SubclassOf` and
`Wikidata.Ontology.InstanceOf`).  This file adds the missing *model-theoretic* side and
shows that the two agree.

* `Wikidata.Ontology.Model O D` is an extensional interpretation of an ontology in a
  domain `D`: a point `pt a` for every item and an extension `ext c ⊆ D` for every item,
  such that asserted `instance of` statements put the point into the extension and
  asserted `subclass of` statements make the extension grow.
* **Soundness**: in *every* model, the derived relations hold extensionally
  (`Wikidata.Ontology.Model.ext_subset_of_subclassOf`,
  `Wikidata.Ontology.Model.pt_mem_ext_of_instanceOf`).  Reasoning with the derivation
  rules of `RequestProject.Core` therefore never asserts more than the intended reading.
* **Completeness**: nothing else holds in every model.  Semantic consequence is
  *exactly* derivability (`Wikidata.Ontology.semSubclassOf_iff`,
  `Wikidata.Ontology.semInstanceOf_iff`), via a canonical model built from the ontology
  itself.
* **Consistency**: disjointness declarations can always be satisfied — every ontology
  with disjointness has a model in which the declared disjoint classes really have
  disjoint extensions (`Wikidata.Ontology.WithDisjointness.instanceModel`), and in that
  model a class has a nonempty extension exactly when it has an instance.
* Models pull back along an `equivalent class` alignment
  (`Wikidata.Ontology.Model.comap`), so a model of an external ontology is a model of
  everything aligned into it.

The final section evaluates the semantics on the worked Wikidata fragment of
`RequestProject.Examples`.
-/

namespace Wikidata

namespace Ontology

universe u v w

variable {I : Type u} {J : Type v}

/-- An **extensional model** of an ontology `O` in the domain `D`: every item `a` is
interpreted both as a point `pt a` of the domain (the item seen as an object) and as a
set `ext a` (the item seen as a class, its *extension*), so that the asserted statements
of the ontology are true under the intended reading. -/
structure Model (O : Ontology I) (D : Type w) where
  /-- The item read as an object of the domain. -/
  pt : I → D
  /-- The item read as a class: its extension. -/
  ext : I → Set D
  /-- An asserted `instance of` (P31) statement puts the instance in the extension. -/
  pt_mem_ext_of_P31 : ∀ {a c}, O.P31 a c → pt a ∈ ext c
  /-- An asserted `subclass of` (P279) statement is an inclusion of extensions. -/
  ext_subset_of_P279 : ∀ {a b}, O.P279 a b → ext a ⊆ ext b

namespace Model

variable {O : Ontology I} {D : Type w} (M : Model O D)

/-! ### Soundness -/

/-- Soundness for `subclass of`: the *derived* class hierarchy is an inclusion of
extensions in every model. -/
theorem ext_subset_of_subclassOf {a b : I} (h : O.SubclassOf a b) : M.ext a ⊆ M.ext b := by
  induction h with
  | refl => exact fun _ hx => hx
  | tail _ hbc ih => exact fun _ hx => M.ext_subset_of_P279 hbc (ih hx)

/-- Soundness for `instance of`: every *derived* instance really lies in the extension
of the class, in every model. -/
theorem pt_mem_ext_of_instanceOf {a c : I} (h : O.InstanceOf a c) : M.pt a ∈ M.ext c := by
  obtain ⟨d, hd, hdc⟩ := h
  exact M.ext_subset_of_subclassOf hdc (M.pt_mem_ext_of_P31 hd)

/-- Soundness of the inheritance rule, read extensionally. -/
theorem pt_mem_ext_of_instanceOf_subclassOf {a c d : I} (hac : O.InstanceOf a c)
    (hcd : O.SubclassOf c d) : M.pt a ∈ M.ext d :=
  M.pt_mem_ext_of_instanceOf (instanceOf_trans_subclassOf hac hcd)

/-- A class with an instance has a nonempty extension in every model. -/
theorem ext_nonempty_of_hasInstance {c : I} (h : O.HasInstance c) : (M.ext c).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨M.pt a, M.pt_mem_ext_of_instanceOf ha⟩

end Model

/-! ### The canonical model and completeness -/

/-- The extension of `c` in the canonical model: the instances of `c` in the left copy
of the domain, and the subclasses of `c` in the right copy.  The right copy is what
makes the model *complete* for `subclass of`: a class is always a member of its own
extension there, even when it has no instances. -/
def canonicalExt (O : Ontology I) (c : I) : Set (I ⊕ I) :=
  {x | Sum.elim (fun a => O.InstanceOf a c) (fun a => O.SubclassOf a c) x}

@[simp] theorem inl_mem_canonicalExt {O : Ontology I} {a c : I} :
    Sum.inl a ∈ O.canonicalExt c ↔ O.InstanceOf a c := Iff.rfl

@[simp] theorem inr_mem_canonicalExt {O : Ontology I} {a c : I} :
    Sum.inr a ∈ O.canonicalExt c ↔ O.SubclassOf a c := Iff.rfl

/-- The **canonical model** of an ontology: the ontology interpreted in itself. -/
def canonicalModel (O : Ontology I) : Model O (I ⊕ I) where
  pt := Sum.inl
  ext := O.canonicalExt
  pt_mem_ext_of_P31 h := instanceOf_of_P31 h
  ext_subset_of_P279 h := by
    rintro (x | x) hx
    · exact instanceOf_trans_subclassOf hx (subclassOf_of_P279 h)
    · exact subclassOf_trans hx (subclassOf_of_P279 h)

@[simp] theorem canonicalModel_pt (O : Ontology I) (a : I) :
    (canonicalModel O).pt a = Sum.inl a := rfl

@[simp] theorem canonicalModel_ext (O : Ontology I) (c : I) :
    (canonicalModel O).ext c = O.canonicalExt c := rfl

/-- **Semantic subclass**: `a` is a subclass of `b` in every model of `O`. -/
def SemSubclassOf (O : Ontology I) (a b : I) : Prop :=
  ∀ (D : Type u) (M : Model O D), M.ext a ⊆ M.ext b

/-- **Semantic instance**: the point of `a` lies in the extension of `c` in every model
of `O`. -/
def SemInstanceOf (O : Ontology I) (a c : I) : Prop :=
  ∀ (D : Type u) (M : Model O D), M.pt a ∈ M.ext c

/-- **Soundness and completeness for `subclass of`**: an inclusion of extensions holds
in every model exactly when it is derivable from the P279 statements. -/
theorem semSubclassOf_iff {O : Ontology I} {a b : I} :
    O.SemSubclassOf a b ↔ O.SubclassOf a b := by
  constructor
  · intro h
    have := h (I ⊕ I) (canonicalModel O) (a := Sum.inr a) (by simpa using subclassOf_refl a)
    simpa using this
  · intro h _ M
    exact M.ext_subset_of_subclassOf h

/-- **Soundness and completeness for `instance of`**: membership in an extension holds
in every model exactly when it is derivable from the P31 and P279 statements. -/
theorem semInstanceOf_iff {O : Ontology I} {a c : I} :
    O.SemInstanceOf a c ↔ O.InstanceOf a c := by
  constructor
  · intro h
    have := h (I ⊕ I) (canonicalModel O)
    simpa using this
  · intro h _ M
    exact M.pt_mem_ext_of_instanceOf h

/-- Every ontology has a model: the ontology layer is consistent. -/
theorem exists_model (O : Ontology I) : Nonempty (Model O (I ⊕ I)) :=
  ⟨canonicalModel O⟩

/-! ### Disjointness -/

namespace WithDisjointness

variable {Dj : WithDisjointness I}

/-- A model of an ontology *with disjointness*: on top of a model of the underlying
ontology, classes declared disjoint are required to have disjoint extensions. -/
structure DModel (Dj : WithDisjointness I) (D : Type w) extends Model Dj.toOntology D where
  /-- Declared disjoint classes have disjoint extensions. -/
  ext_disjoint : ∀ {c d}, Dj.DisjointWith c d → Disjoint (ext c) (ext d)

/-- In a model of a disjointness declaration, the disjointness is inherited by
subclasses, exactly as in the abstract layer. -/
theorem DModel.ext_disjoint_of_subclassOf {D : Type w} (M : DModel Dj D) {c d c' d' : I}
    (h : Dj.DisjointWith c d) (hc : Dj.toOntology.SubclassOf c' c)
    (hd : Dj.toOntology.SubclassOf d' d) : Disjoint (M.ext c') (M.ext d') :=
  (M.ext_disjoint h).mono (M.toModel.ext_subset_of_subclassOf hc)
    (M.toModel.ext_subset_of_subclassOf hd)

/-- The **instance model** of an ontology with disjointness: the domain is the type of
items, each item denotes itself, and the extension of a class is the set of its derived
instances.  Disjointness declarations are satisfied, so declaring classes disjoint never
makes an ontology unsatisfiable. -/
def instanceModel (Dj : WithDisjointness I) : DModel Dj I where
  pt := id
  ext c := {a | Dj.toOntology.InstanceOf a c}
  pt_mem_ext_of_P31 h := instanceOf_of_P31 h
  ext_subset_of_P279 h := fun _ hx => instanceOf_trans_subclassOf hx (subclassOf_of_P279 h)
  ext_disjoint h := Set.disjoint_left.mpr fun _ hc hd => (Dj.disjointWith_spec h hc hd).elim

@[simp] theorem instanceModel_ext (Dj : WithDisjointness I) (c : I) :
    (instanceModel Dj).ext c = {a | Dj.toOntology.InstanceOf a c} := rfl

/-- Every ontology with disjointness declarations has a model: the disjointness layer is
consistent. -/
theorem exists_dmodel (Dj : WithDisjointness I) : Nonempty (DModel Dj I) :=
  ⟨instanceModel Dj⟩

/-- In the instance model, a class has a nonempty extension exactly when it has an
instance: the model does not invent members. -/
theorem instanceModel_ext_nonempty_iff (Dj : WithDisjointness I) (c : I) :
    ((instanceModel Dj).ext c).Nonempty ↔ Dj.toOntology.HasInstance c := Iff.rfl

/-- In the instance model, the extension of a class is contained in that of a superclass
exactly when the superclass inherits all its instances. -/
theorem instanceModel_ext_subset_iff (Dj : WithDisjointness I) (c d : I) :
    (instanceModel Dj).ext c ⊆ (instanceModel Dj).ext d ↔
      ∀ a, Dj.toOntology.InstanceOf a c → Dj.toOntology.InstanceOf a d := Iff.rfl

end WithDisjointness

/-! ### Models transport along alignments -/

namespace Model

/-- A model of the target of an `equivalent class` alignment is a model of its source:
interpretations pull back along alignments. -/
def comap {O₁ : Ontology I} {O₂ : Ontology J} (F : Alignment O₁ O₂) {D : Type w}
    (M : Model O₂ D) : Model O₁ D where
  pt a := M.pt (F.map a)
  ext c := M.ext (F.map c)
  pt_mem_ext_of_P31 h := M.pt_mem_ext_of_instanceOf (F.map_P31 h)
  ext_subset_of_P279 h := M.ext_subset_of_subclassOf (F.map_P279 h)

@[simp] theorem comap_pt {O₁ : Ontology I} {O₂ : Ontology J} (F : Alignment O₁ O₂)
    {D : Type w} (M : Model O₂ D) (a : I) : (M.comap F).pt a = M.pt (F.map a) := rfl

@[simp] theorem comap_ext {O₁ : Ontology I} {O₂ : Ontology J} (F : Alignment O₁ O₂)
    {D : Type w} (M : Model O₂ D) (c : I) : (M.comap F).ext c = M.ext (F.map c) := rfl

/-- The identity alignment pulls a model back to itself. -/
theorem comap_id {O : Ontology I} {D : Type w} (M : Model O D) :
    M.comap (Alignment.id O) = M := rfl

end Model

end Ontology

/-! ### Semantics of the property layer

The same soundness/completeness picture holds one level up, for the statement relation
of the property layer: a *model* interprets every property as a relation on items that
respects the asserted statements and the `subproperty of`, transitivity, symmetry and
inverse declarations. -/

namespace PropertyLayer

variable {I P : Type*} {L : PropertyLayer I P}

/-- A model of a property layer: an interpretation of the properties as relations that
validates the asserted statements and all the declarations. -/
structure Model (L : PropertyLayer I P) where
  /-- The interpretation of each property as a relation on items. -/
  rel : P → I → I → Prop
  /-- Asserted statements hold. -/
  rel_stmt : ∀ {p s o}, L.Stmt p s o → rel p s o
  /-- Statements are inherited by superproperties. -/
  rel_sub : ∀ {p q s o}, L.SubProp p q → rel p s o → rel q s o
  /-- A property declared transitive is interpreted by a transitive relation. -/
  rel_trans : ∀ {p a b c}, L.IsTransitive p → rel p a b → rel p b c → rel p a c
  /-- A property declared symmetric is interpreted by a symmetric relation. -/
  rel_symm : ∀ {p s o}, L.IsSymmetric p → rel p s o → rel p o s
  /-- Inverse properties are interpreted by converse relations. -/
  rel_inv : ∀ {p q s o}, L.InverseOf p q → rel p s o → rel q o s

/-- A model of a property layer is exactly a relation closed under the derivation
rules. -/
theorem Model.isClosed (M : Model L) : IsClosed (L := L) M.rel where
  stmt := M.rel_stmt
  sub := M.rel_sub
  trans := M.rel_trans
  symm := M.rel_symm
  inv := M.rel_inv

/-- The derived statement relation is itself a model: the canonical one. -/
def canonicalModel (L : PropertyLayer I P) : Model L where
  rel := L.Holds
  rel_stmt := Holds.stmt
  rel_sub := Holds.sub
  rel_trans := Holds.trans
  rel_symm := Holds.symm
  rel_inv := Holds.inv

/-- A statement is a **semantic consequence** of a property layer when it holds in every
model of it. -/
def SemHolds (L : PropertyLayer I P) (p : P) (s o : I) : Prop := ∀ M : Model L, M.rel p s o

/-- **Soundness and completeness for the property layer**: a statement holds in every
model exactly when it is derivable. -/
theorem semHolds_iff {p : P} {s o : I} : L.SemHolds p s o ↔ L.Holds p s o :=
  ⟨fun h => h (canonicalModel L), fun h M => holds_minimal M.isClosed h⟩

end PropertyLayer

/-! ### The semantics on the worked fragment

The Wikidata fragment of `RequestProject.Examples` (Douglas Adams, human, person,
entity, …) is interpreted in its own instance model. -/

namespace Examples

open Ontology

/-- The fragment carries a model in which the declared disjointness holds. -/
def wdModel : WithDisjointness.DModel (wdCore.toWithDisjointness wdCore_valid) Qid :=
  WithDisjointness.instanceModel _

/-- Douglas Adams belongs to the extension of `entity` (Q35120) in the model — the
inherited fact `Q42 P31 Q5 P279* Q35120` read extensionally. -/
theorem adams_mem_ext_entity : wdModel.pt (Q "Q42") ∈ wdModel.ext (Q "Q35120") :=
  wdModel.toModel.pt_mem_ext_of_instanceOf adams_instanceOf_entity'

/-- The extension of `human` (Q5) is contained in that of `entity` (Q35120) in every
model of the fragment, since the inclusion is derivable. -/
theorem ext_human_subset_entity {D : Type} (M : Model wdOnt D) :
    M.ext (Q "Q5") ⊆ M.ext (Q "Q35120") := by
  refine M.ext_subset_of_subclassOf ?_
  exact (KB.isSubclassOf_iff_subclassOf wdCore_valid _ _).mp human_subclassOf_entity

/-- Douglas Adams is *not* in the extension of the metaclass Q55983715 in the canonical
model: the semantics does not over-generate. -/
theorem adams_not_mem_ext_metaclass :
    ¬ (canonicalModel wdOnt).pt (Q "Q42") ∈ (canonicalModel wdOnt).ext (Q "Q55983715") := by
  simpa using adams_not_instanceOf_metaclass'

end Examples

end Wikidata
