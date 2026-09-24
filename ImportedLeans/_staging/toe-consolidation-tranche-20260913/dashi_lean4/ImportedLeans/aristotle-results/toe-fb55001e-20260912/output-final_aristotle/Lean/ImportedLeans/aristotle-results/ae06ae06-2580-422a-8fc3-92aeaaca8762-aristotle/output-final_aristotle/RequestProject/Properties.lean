import RequestProject.Core

/-!
# The property layer of Wikidata

Beyond `instance of` (P31) and `subclass of` (P279), which are the subject of
`RequestProject.Core`, the Wikidata ontology is organised by *properties*: items
are related to one another by statements `⟨subject, property, value⟩`, and the
properties themselves carry ontological information:

* `subproperty of` (P1647) organises properties into a hierarchy — a statement made
  with a property is also a statement made with each of its superproperties;
* some properties are declared *transitive* (e.g. `part of`, P361; the property
  constraint item is Q18647515), some *symmetric* (Q18647518, e.g. `different
  from`, P1889), and properties come in *inverse* pairs (P1696, e.g. `part of`
  P361 and `has part(s)` P527);
* properties carry *constraints*: the **type constraint** (Q21503250) says the
  subject of a statement must be an instance of a given class, the **value-type
  constraint** (Q21510865) says the same of the value.

This file models that layer abstractly. A `Wikidata.PropertyLayer I P` records the
*asserted* data (statements, subproperty declarations, transitivity, symmetry and
inverse declarations) over a type `I` of items and a type `P` of properties, and
`PropertyLayer.Holds` is the *derived* statement relation: the least relation
containing the asserted statements and closed under the four rules above.

The main results are:

* `PropertyLayer.holds_of_subPropertyOf` — statements are inherited upwards along
  the property hierarchy;
* `PropertyLayer.holds_minimal` — `Holds` is the least closure, so the derived
  relation adds nothing that is not forced;
* `PropertyLayer.holds_inverse_iff`, `PropertyLayer.holds_symm_iff`,
  `PropertyLayer.holds_transGen` — the behaviour of inverse, symmetric and
  transitive properties;
* the constraint results `Constraints.subjectType_of_subPropertyOf`,
  `Constraints.instanceOf_superclass_of_typeC`, and
  `Constraints.not_holds_self_of_disjoint`: a property whose subject and value
  types are disjoint classes never relates an item to itself.
-/

namespace Wikidata

/-- The asserted property layer over items `I` and properties `P`. -/
structure PropertyLayer (I P : Type*) where
  /-- Asserted statements: `Stmt p s o` means "`s` has value `o` for property `p`". -/
  Stmt : P → I → I → Prop
  /-- Asserted `subproperty of` (P1647) declarations. -/
  SubProp : P → P → Prop
  /-- Properties declared transitive (Q18647515). -/
  IsTransitive : P → Prop
  /-- Properties declared symmetric (Q18647518). -/
  IsSymmetric : P → Prop
  /-- Asserted `inverse property` (P1696) declarations. -/
  InverseOf : P → P → Prop
  /-- Being inverse is a symmetric relation between properties. -/
  inverseOf_symm : ∀ {p q}, InverseOf p q → InverseOf q p

namespace PropertyLayer

variable {I P : Type*} (L : PropertyLayer I P)

/-- Derived `subproperty of`: the reflexive–transitive closure of the asserted
P1647 statements. -/
def SubPropertyOf (p q : P) : Prop := Relation.ReflTransGen L.SubProp p q

/-- The derived statement relation: the least relation containing the asserted
statements and closed under the subproperty, transitivity, symmetry and inverse
rules. -/
inductive Holds : P → I → I → Prop
  /-- An asserted statement holds. -/
  | stmt {p s o} : L.Stmt p s o → Holds p s o
  /-- A statement holds for every superproperty of its property. -/
  | sub {p q s o} : L.SubProp p q → Holds p s o → Holds q s o
  /-- A transitive property composes with itself. -/
  | trans {p a b c} : L.IsTransitive p → Holds p a b → Holds p b c → Holds p a c
  /-- A symmetric property holds in both directions. -/
  | symm {p s o} : L.IsSymmetric p → Holds p s o → Holds p o s
  /-- An inverse property holds in the opposite direction. -/
  | inv {p q s o} : L.InverseOf p q → Holds p s o → Holds q o s

variable {L}

/-! ### The property hierarchy -/

@[refl] theorem subPropertyOf_refl (p : P) : L.SubPropertyOf p p := Relation.ReflTransGen.refl

theorem subPropertyOf_of_subProp {p q : P} (h : L.SubProp p q) : L.SubPropertyOf p q :=
  Relation.ReflTransGen.single h

theorem subPropertyOf_trans {p q r : P} (h : L.SubPropertyOf p q) (h' : L.SubPropertyOf q r) :
    L.SubPropertyOf p r := Relation.ReflTransGen.trans h h'

/-- Statements are inherited upwards along the property hierarchy. -/
theorem holds_of_subPropertyOf {p q : P} {s o : I} (hpq : L.SubPropertyOf p q)
    (h : L.Holds p s o) : L.Holds q s o := by
  induction hpq with
  | refl => exact h
  | tail _ hbc ih => exact Holds.sub hbc ih

/-! ### `Holds` is the least closure -/

/-- What it means for a relation to be closed under the rules generating `Holds`. -/
structure IsClosed (R : P → I → I → Prop) : Prop where
  /-- Asserted statements are in `R`. -/
  stmt : ∀ {p s o}, L.Stmt p s o → R p s o
  /-- `R` is inherited upwards along the property hierarchy. -/
  sub : ∀ {p q s o}, L.SubProp p q → R p s o → R q s o
  /-- `R` composes transitive properties. -/
  trans : ∀ {p a b c}, L.IsTransitive p → R p a b → R p b c → R p a c
  /-- `R` is symmetric at symmetric properties. -/
  symm : ∀ {p s o}, L.IsSymmetric p → R p s o → R p o s
  /-- `R` respects inverse properties. -/
  inv : ∀ {p q s o}, L.InverseOf p q → R p s o → R q o s

/-- `Holds` is itself closed under the rules. -/
theorem isClosed_holds : IsClosed (L := L) L.Holds where
  stmt := Holds.stmt
  sub := Holds.sub
  trans := Holds.trans
  symm := Holds.symm
  inv := Holds.inv

/-- **Minimality**: the derived statement relation is contained in every relation
closed under the rules, so the property layer derives nothing that is not forced. -/
theorem holds_minimal {R : P → I → I → Prop} (hR : IsClosed (L := L) R) {p : P} {s o : I}
    (h : L.Holds p s o) : R p s o := by
  induction h with
  | stmt h => exact hR.stmt h
  | sub h _ ih => exact hR.sub h ih
  | trans h _ _ ih1 ih2 => exact hR.trans h ih1 ih2
  | symm h _ ih => exact hR.symm h ih
  | inv h _ ih => exact hR.inv h ih

/-! ### Inverse, symmetric and transitive properties -/

/-- Inverse properties describe the same statements read backwards. -/
theorem holds_inverse_iff {p q : P} (h : L.InverseOf p q) (s o : I) :
    L.Holds p s o ↔ L.Holds q o s :=
  ⟨fun hp => Holds.inv h hp, fun hq => Holds.inv (L.inverseOf_symm h) hq⟩

/-- A symmetric property holds in both directions. -/
theorem holds_symm_iff {p : P} (h : L.IsSymmetric p) (s o : I) :
    L.Holds p s o ↔ L.Holds p o s :=
  ⟨fun hp => Holds.symm h hp, fun hp => Holds.symm h hp⟩

/-- A property that is its own inverse is symmetric in the derived semantics. -/
theorem holds_selfInverse_iff {p : P} (h : L.InverseOf p p) (s o : I) :
    L.Holds p s o ↔ L.Holds p o s := holds_inverse_iff h s o

/-- For a transitive property, the derived statements are already transitively
closed. -/
theorem holds_transGen {p : P} (hp : L.IsTransitive p) {s o : I}
    (h : Relation.TransGen (L.Holds p) s o) : L.Holds p s o := by
  induction h with
  | single h => exact h
  | tail _ hbc ih => exact Holds.trans hp ih hbc

/-- For a transitive property, chains of asserted statements are derived. -/
theorem holds_of_transGen_stmt {p : P} (hp : L.IsTransitive p) {s o : I}
    (h : Relation.TransGen (L.Stmt p) s o) : L.Holds p s o :=
  holds_transGen hp (h.mono fun _ _ => Holds.stmt)

/-- The inverse of a transitive property is transitive on derived statements. -/
theorem holds_trans_of_inverse {p q : P} (hp : L.IsTransitive p) (hpq : L.InverseOf p q)
    {a b c : I} (hab : L.Holds q a b) (hbc : L.Holds q b c) : L.Holds q a c :=
  (holds_inverse_iff hpq c a).1
    (Holds.trans hp ((holds_inverse_iff hpq c b).2 hbc) ((holds_inverse_iff hpq b a).2 hab))

/-! ### Property constraints -/

/-- Property constraints: the type constraint (Q21503250) restricts the subject of a
statement, the value-type constraint (Q21510865) restricts its value. -/
structure Constraints (I P : Type*) where
  /-- `TypeC p c`: the subject of a `p`-statement must be an instance of `c`. -/
  TypeC : P → I → Prop
  /-- `ValueTypeC p c`: the value of a `p`-statement must be an instance of `c`. -/
  ValueTypeC : P → I → Prop

namespace Constraints

variable {I P : Type*} {L : PropertyLayer I P} {C : Constraints I P} {O : Ontology I}

/-- The type constraints of `C` are satisfied by the derived statements of `L` in the
ontology `O`. -/
def SubjectTypeOk (O : Ontology I) (L : PropertyLayer I P) (C : Constraints I P) : Prop :=
  ∀ {p c s o}, C.TypeC p c → L.Holds p s o → O.InstanceOf s c

/-- The value-type constraints of `C` are satisfied by the derived statements of `L`
in the ontology `O`. -/
def ValueTypeOk (O : Ontology I) (L : PropertyLayer I P) (C : Constraints I P) : Prop :=
  ∀ {p c s o}, C.ValueTypeC p c → L.Holds p s o → O.InstanceOf o c

/-- Type constraints propagate down the property hierarchy: a statement made with a
subproperty of `p` satisfies the type constraint of `p`. -/
theorem subjectType_of_subPropertyOf (h : SubjectTypeOk O L C) {p q : P} {c s o : I}
    (hc : C.TypeC p c) (hqp : L.SubPropertyOf q p) (hq : L.Holds q s o) :
    O.InstanceOf s c :=
  h hc (holds_of_subPropertyOf hqp hq)

/-- Value-type constraints propagate down the property hierarchy. -/
theorem valueType_of_subPropertyOf (h : ValueTypeOk O L C) {p q : P} {c s o : I}
    (hc : C.ValueTypeC p c) (hqp : L.SubPropertyOf q p) (hq : L.Holds q s o) :
    O.InstanceOf o c :=
  h hc (holds_of_subPropertyOf hqp hq)

/-- A type constraint is inherited by the superclasses of the constraining class. -/
theorem instanceOf_superclass_of_typeC (h : SubjectTypeOk O L C) {p : P} {c d s o : I}
    (hc : C.TypeC p c) (hcd : O.SubclassOf c d) (hp : L.Holds p s o) :
    O.InstanceOf s d :=
  Ontology.instanceOf_trans_subclassOf (h hc hp) hcd

/-- The subject type constraint of a property is a value-type constraint for its
inverse. -/
theorem valueType_of_inverse (h : SubjectTypeOk O L C) {p q : P} {c s o : I}
    (hc : C.TypeC p c) (hpq : L.InverseOf p q) (hq : L.Holds q s o) :
    O.InstanceOf o c :=
  h hc ((holds_inverse_iff (L.inverseOf_symm hpq) s o).1 hq)

/-- For a symmetric property the subject constraint applies to the value as well. -/
theorem subjectType_of_symmetric (h : SubjectTypeOk O L C) {p : P} {c s o : I}
    (hc : C.TypeC p c) (hp : L.IsSymmetric p) (hq : L.Holds p s o) :
    O.InstanceOf o c :=
  h hc ((holds_symm_iff hp s o).1 hq)

/-- A property whose subject type and value type are declared disjoint never relates
an item to itself. -/
theorem not_holds_self_of_disjoint {D : Ontology.WithDisjointness I}
    (h1 : SubjectTypeOk D.toOntology L C) (h2 : ValueTypeOk D.toOntology L C)
    {p : P} {c d s : I} (hc : C.TypeC p c) (hd : C.ValueTypeC p d)
    (hdisj : D.DisjointWith c d) : ¬ L.Holds p s s :=
  fun hp => D.disjointWith_spec hdisj (h1 hc hp) (h2 hd hp)

/-- A transitive property whose subject type and value type are declared disjoint has
no two-step chains either. -/
theorem not_holds_cycle_of_disjoint {D : Ontology.WithDisjointness I}
    (h1 : SubjectTypeOk D.toOntology L C) (h2 : ValueTypeOk D.toOntology L C)
    {p : P} {c d s t : I} (hc : C.TypeC p c) (hd : C.ValueTypeC p d)
    (hdisj : D.DisjointWith c d) (htr : L.IsTransitive p)
    (hst : L.Holds p s t) (hts : L.Holds p t s) : False :=
  not_holds_self_of_disjoint h1 h2 hc hd hdisj (Holds.trans htr hst hts)

end Constraints

end PropertyLayer

end Wikidata
