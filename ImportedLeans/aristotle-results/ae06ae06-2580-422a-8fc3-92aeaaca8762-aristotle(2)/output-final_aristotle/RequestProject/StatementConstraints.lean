import RequestProject.PropertyConstraints

/-!
# Statement-level property constraints

`RequestProject.Properties` covers the type (Q21503250) and value-type (Q21510865)
constraints and `RequestProject.PropertyConstraints` the single-value (Q19474404),
distinct-values (Q21502410) and irreflexive (Q21510863) ones.  The Wikidata property
constraint vocabulary also contains constraints that relate *different statements about
the same item*:

* **item-requires-statement** (Q21503247): an item using the property `p` must also use
  the property `q`;
* **value-requires-statement** (Q21510864): the *value* of a `p`-statement must itself
  carry a `q`-statement;
* **conflicts-with** (Q21502838): an item may not use `p` and `q` at the same time;
* **one-of** (Q21510859) and **none-of** (Q52558054): the value of `p` must (or must
  not) come from a fixed list;
* **inverse** (Q21510855): every `p`-statement must be mirrored by a `q`-statement.

and, on the ontology side, the *soft* constraint **properties for this type** (P1963):
the instances of a class are expected to carry certain properties.

This file adds all of these:

* abstract definitions on `Wikidata.PropertyLayer`, phrased with the derived statement
  relation `Holds`, and their propagation laws — every constraint of a property is a
  constraint of each of its subproperties, `conflicts-with` is symmetric, a property
  that conflicts with itself (or that both requires and conflicts with the same
  property) is empty, `one-of` together with `none-of` on the same list forces the
  property to be empty, a `one-of` list of instances of a class implies the value-type
  constraint of that class, and the inverse constraint at a single property is exactly
  symmetry of the derived statements;
* `Wikidata.PropertiesForType` (P1963) and the fact that the expectation is inherited by
  subclasses, together with its interaction with the type constraint;
* certified executable checkers on `Wikidata.PKB` (`itemRequiresB`, `valueRequiresB`,
  `conflictsWithB`, `oneOfB`, `noneOfB`, `inverseConstraintB`), each proved to imply the
  corresponding abstract constraint for the layers on which the engine is complete;
* a worked fragment on which the checkers are evaluated, including a constraint that is
  correctly *rejected*.
-/

namespace Wikidata

namespace PropertyLayer

variable {I P : Type*} {L : PropertyLayer I P}

/-! ### The abstract constraints -/

/-- The **item-requires-statement constraint** (Q21503247): the subject of a
`p`-statement also has a `q`-statement. -/
def RequiresStatement (L : PropertyLayer I P) (p q : P) : Prop :=
  ∀ {s o : I}, L.Holds p s o → ∃ o', L.Holds q s o'

/-- The **value-requires-statement constraint** (Q21510864): the value of a
`p`-statement has a `q`-statement of its own. -/
def ValueRequiresStatement (L : PropertyLayer I P) (p q : P) : Prop :=
  ∀ {s o : I}, L.Holds p s o → ∃ o', L.Holds q o o'

/-- The **conflicts-with constraint** (Q21502838): no item has both a `p`-statement and
a `q`-statement. -/
def ConflictsWith (L : PropertyLayer I P) (p q : P) : Prop :=
  ∀ {s o o' : I}, L.Holds p s o → L.Holds q s o' → False

/-- The **one-of constraint** (Q21510859): the values of `p` all lie in `S`. -/
def OneOf (L : PropertyLayer I P) (p : P) (S : Set I) : Prop :=
  ∀ {s o : I}, L.Holds p s o → o ∈ S

/-- The **none-of constraint** (Q52558054): no value of `p` lies in `S`. -/
def NoneOf (L : PropertyLayer I P) (p : P) (S : Set I) : Prop :=
  ∀ {s o : I}, L.Holds p s o → o ∉ S

/-- The **inverse constraint** (Q21510855): every `p`-statement is mirrored by a
`q`-statement in the opposite direction. -/
def InverseConstraint (L : PropertyLayer I P) (p q : P) : Prop :=
  ∀ {s o : I}, L.Holds p s o → L.Holds q o s

/-- A property has no statements at all. -/
def IsEmptyProperty (L : PropertyLayer I P) (p : P) : Prop := ∀ s o : I, ¬ L.Holds p s o

/-! ### Propagation along the property hierarchy -/

/-- A required statement of `p` is required by every subproperty of `p`. -/
theorem RequiresStatement.of_subPropertyOf {p q p' : P} (h : L.RequiresStatement p q)
    (hp : L.SubPropertyOf p' p) : L.RequiresStatement p' q :=
  fun hs => h (holds_of_subPropertyOf hp hs)

/-- Requiring a statement with `q` also requires one with every superproperty of `q`. -/
theorem RequiresStatement.mono {p q q' : P} (h : L.RequiresStatement p q)
    (hq : L.SubPropertyOf q q') : L.RequiresStatement p q' := by
  intro s o hs
  obtain ⟨o', ho'⟩ := h hs
  exact ⟨o', holds_of_subPropertyOf hq ho'⟩

/-- Every property requires itself. -/
theorem RequiresStatement.refl (p : P) : L.RequiresStatement p p := fun hs => ⟨_, hs⟩

/-- The item-requires-statement constraint is transitive. -/
theorem RequiresStatement.trans {p q r : P} (h : L.RequiresStatement p q)
    (h' : L.RequiresStatement q r) : L.RequiresStatement p r := by
  intro s o hs
  obtain ⟨o', ho'⟩ := h hs
  exact h' ho'

/-- A value-requires-statement constraint of `p` is one of every subproperty of `p`. -/
theorem ValueRequiresStatement.of_subPropertyOf {p q p' : P}
    (h : L.ValueRequiresStatement p q) (hp : L.SubPropertyOf p' p) :
    L.ValueRequiresStatement p' q :=
  fun hs => h (holds_of_subPropertyOf hp hs)

/-- For a symmetric property, requiring a statement of the subject requires one of the
value as well. -/
theorem ValueRequiresStatement.of_symmetric {p q : P} (hsym : L.IsSymmetric p)
    (h : L.RequiresStatement p q) : L.ValueRequiresStatement p q :=
  fun hs => h (Holds.symm hsym hs)

/-- The subject requirement of a property is a value requirement of its inverse. -/
theorem ValueRequiresStatement.of_inverse {p p' q : P} (hinv : L.InverseOf p p')
    (h : L.RequiresStatement p q) : L.ValueRequiresStatement p' q := by
  intro s o hs
  exact h ((holds_inverse_iff hinv o s).2 hs)

/-- The conflicts-with constraint is symmetric. -/
theorem ConflictsWith.symm {p q : P} (h : L.ConflictsWith p q) : L.ConflictsWith q p :=
  fun h1 h2 => h h2 h1

/-- A conflict between `p` and `q` is a conflict between all their subproperties. -/
theorem ConflictsWith.of_subPropertyOf {p q p' q' : P} (h : L.ConflictsWith p q)
    (hp : L.SubPropertyOf p' p) (hq : L.SubPropertyOf q' q) : L.ConflictsWith p' q' :=
  fun h1 h2 => h (holds_of_subPropertyOf hp h1) (holds_of_subPropertyOf hq h2)

/-- A property that conflicts with itself has no statements. -/
theorem ConflictsWith.isEmptyProperty_self {p : P} (h : L.ConflictsWith p p) :
    L.IsEmptyProperty p := fun _ _ hs => h hs hs

/-- A property that both requires and conflicts with the same property has no
statements: the two constraints together are unsatisfiable. -/
theorem IsEmptyProperty.of_requires_conflicts {p q : P} (hreq : L.RequiresStatement p q)
    (hcon : L.ConflictsWith p q) : L.IsEmptyProperty p := by
  intro s o hs
  obtain ⟨o', ho'⟩ := hreq hs
  exact hcon hs ho'

/-- A one-of constraint of `p` is one of every subproperty of `p`. -/
theorem OneOf.of_subPropertyOf {p p' : P} {S : Set I} (h : L.OneOf p S)
    (hp : L.SubPropertyOf p' p) : L.OneOf p' S :=
  fun hs => h (holds_of_subPropertyOf hp hs)

/-- A one-of constraint may always be relaxed to a larger list. -/
theorem OneOf.mono {p : P} {S T : Set I} (h : L.OneOf p S) (hST : S ⊆ T) : L.OneOf p T :=
  fun hs => hST (h hs)

/-- A none-of constraint of `p` is one of every subproperty of `p`. -/
theorem NoneOf.of_subPropertyOf {p p' : P} {S : Set I} (h : L.NoneOf p S)
    (hp : L.SubPropertyOf p' p) : L.NoneOf p' S :=
  fun hs => h (holds_of_subPropertyOf hp hs)

/-- A none-of constraint may always be tightened to a smaller list. -/
theorem NoneOf.anti {p : P} {S T : Set I} (h : L.NoneOf p S) (hTS : T ⊆ S) : L.NoneOf p T :=
  fun hs hmem => h hs (hTS hmem)

/-- One-of and none-of constraints on overlapping lists force the property to be
empty. -/
theorem IsEmptyProperty.of_oneOf_noneOf {p : P} {S T : Set I} (h : L.OneOf p S)
    (h' : L.NoneOf p T) (hST : S ⊆ T) : L.IsEmptyProperty p :=
  fun _ _ hs => h' hs (hST (h hs))

/-- A one-of list whose members are all instances of a class implies the value-type
constraint (Q21510865) for that class. -/
theorem instanceOf_of_oneOf {O : Ontology I} {p : P} {S : Set I} {c : I} (h : L.OneOf p S)
    (hS : ∀ x ∈ S, O.InstanceOf x c) {s o : I} (hs : L.Holds p s o) : O.InstanceOf o c :=
  hS o (h hs)

/-- The inverse constraint at a single property says exactly that the derived
statements are symmetric. -/
theorem inverseConstraint_self_iff {p : P} :
    L.InverseConstraint p p ↔ ∀ s o : I, L.Holds p s o → L.Holds p o s :=
  ⟨fun h _ _ hs => h hs, fun h _ _ hs => h _ _ hs⟩

/-- A declared `inverse property` (P1696) pair satisfies the inverse constraint. -/
theorem InverseConstraint.of_inverseOf {p q : P} (h : L.InverseOf p q) :
    L.InverseConstraint p q := fun hs => Holds.inv h hs

/-- A symmetric property satisfies the inverse constraint with itself. -/
theorem InverseConstraint.of_symmetric {p : P} (h : L.IsSymmetric p) :
    L.InverseConstraint p p := fun hs => Holds.symm h hs

/-- Two mutually inverse constraints turn the statements of one property into exactly
the reversed statements of the other. -/
theorem holds_comm_of_inverseConstraint {p q : P} (h : L.InverseConstraint p q)
    (h' : L.InverseConstraint q p) (s o : I) : L.Holds p s o ↔ L.Holds q o s :=
  ⟨fun hs => h hs, fun hs => h' hs⟩

/-- The inverse constraint turns a value requirement into a subject requirement. -/
theorem RequiresStatement.of_inverseConstraint {p q r : P} (h : L.InverseConstraint p q)
    (hv : L.RequiresStatement q r) : L.ValueRequiresStatement p r :=
  fun hs => hv (h hs)

end PropertyLayer

/-! ### `properties for this type` (P1963) -/

/-- The soft constraint **properties for this type** (P1963): every instance of the
class `c` is expected to carry a statement with the property `p`. -/
def PropertiesForType {I P : Type*} (O : Ontology I) (L : PropertyLayer I P) (c : I)
    (p : P) : Prop :=
  ∀ {a : I}, O.InstanceOf a c → ∃ o, L.Holds p a o

namespace PropertiesForType

variable {I P : Type*} {O : Ontology I} {L : PropertyLayer I P} {c d : I} {p q : P}

/-- The expectation is inherited by subclasses: if the instances of `c` carry `p`, so
do the instances of any subclass of `c`. -/
theorem of_subclassOf (h : PropertiesForType O L c p) (hd : O.SubclassOf d c) :
    PropertiesForType O L d p :=
  fun ha => h (Ontology.instanceOf_trans_subclassOf ha hd)

/-- The expectation passes to superproperties. -/
theorem mono (h : PropertiesForType O L c p) (hp : L.SubPropertyOf p q) :
    PropertiesForType O L c q := by
  intro a ha
  obtain ⟨o, ho⟩ := h ha
  exact ⟨o, PropertyLayer.holds_of_subPropertyOf hp ho⟩

/-- Combined with a type constraint (Q21503250): if the subjects of `q` must be
instances of `c`, and the instances of `c` are expected to carry `p`, then every
subject of a `q`-statement carries a `p`-statement. -/
theorem requiresStatement_of_typeC {C : PropertyLayer.Constraints I P}
    (htype : PropertyLayer.Constraints.SubjectTypeOk O L C) (hc : C.TypeC q c)
    (h : PropertiesForType O L c p) : L.RequiresStatement q p :=
  fun hs => h (htype hc hs)

/-- A class whose instances are expected to carry a property that has no statements has
no instances. -/
theorem not_hasInstance_of_isEmptyProperty (h : PropertiesForType O L c p)
    (hp : L.IsEmptyProperty p) : ¬ O.HasInstance c := by
  rintro ⟨a, ha⟩
  obtain ⟨o, ho⟩ := h ha
  exact hp a o ho

end PropertiesForType

/-! ### The executable checkers -/

namespace PKB

variable (pkb : PKB)

/-- Does the item `s` have any value for the property `p`? -/
def hasValueB (p : Pid) (s : Qid) : Bool := !(pkb.valuesOf p s).isEmpty

/-- The item-requires-statement constraint (Q21503247), executably. -/
def itemRequiresB (p q : Pid) : Bool :=
  pkb.base.items.all (fun s => !pkb.hasValueB p s || pkb.hasValueB q s)

/-- The value-requires-statement constraint (Q21510864), executably. -/
def valueRequiresB (p q : Pid) : Bool :=
  pkb.base.items.all (fun s => (pkb.valuesOf p s).all (fun o => pkb.hasValueB q o))

/-- The conflicts-with constraint (Q21502838), executably. -/
def conflictsWithB (p q : Pid) : Bool :=
  pkb.base.items.all (fun s => !(pkb.hasValueB p s && pkb.hasValueB q s))

/-- The one-of constraint (Q21510859), executably. -/
def oneOfB (p : Pid) (vals : List Qid) : Bool :=
  pkb.base.items.all (fun s => (pkb.valuesOf p s).all (fun o => o ∈ vals))

/-- The none-of constraint (Q52558054), executably. -/
def noneOfB (p : Pid) (vals : List Qid) : Bool :=
  pkb.base.items.all (fun s => (pkb.valuesOf p s).all (fun o => !(o ∈ vals)))

/-- The inverse constraint (Q21510855), executably. -/
def inverseConstraintB (p q : Pid) : Bool :=
  pkb.base.items.all (fun s => (pkb.valuesOf p s).all (fun o => pkb.relatedB q o s))

variable {pkb}

theorem hasValueB_iff {p : Pid} {s : Qid} :
    pkb.hasValueB p s = true ↔ ∃ o, o ∈ pkb.base.items ∧ pkb.relatedB p s o = true := by
  constructor
  · intro h
    have hne : pkb.valuesOf p s ≠ [] := by simpa [hasValueB, List.isEmpty_iff] using h
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨o, mem_valuesOf.1 ho⟩
  · rintro ⟨o, ho, hr⟩
    have hm : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨ho, hr⟩
    simpa [hasValueB, List.isEmpty_iff] using List.ne_nil_of_mem hm

/-- **Certified item-requires-statement**: a pair of properties passing the check
satisfies the abstract constraint. -/
theorem requiresStatement_of_itemRequiresB (h : pkb.pWellFormed = true)
    (hsym : pkb.symProps = []) (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true)
    {p q : Pid} (hb : pkb.itemRequiresB p q = true) :
    pkb.toLayer.RequiresStatement p q := by
  intro s o hs
  have hr : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup hs
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr
  have homem : o ∈ pkb.base.items := (mem_items_of_supportsB h hsupv).2
  have hp : pkb.hasValueB p s = true := hasValueB_iff.2 ⟨o, homem, hr⟩
  have := List.all_eq_true.1 hb s hsmem
  rw [hp] at this
  simp only [Bool.not_true, Bool.false_or] at this
  obtain ⟨o', -, hr'⟩ := hasValueB_iff.1 this
  exact ⟨o', holds_of_relatedB h hr'⟩

/-- **Certified value-requires-statement**. -/
theorem valueRequiresStatement_of_valueRequiresB (h : pkb.pWellFormed = true)
    (hsym : pkb.symProps = []) (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true)
    {p q : Pid} (hb : pkb.valueRequiresB p q = true) :
    pkb.toLayer.ValueRequiresStatement p q := by
  intro s o hs
  have hr : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup hs
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr
  have homem : o ∈ pkb.base.items := (mem_items_of_supportsB h hsupv).2
  have hmem : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨homem, hr⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 hb s hsmem) o hmem
  obtain ⟨o', -, hr'⟩ := hasValueB_iff.1 this
  exact ⟨o', holds_of_relatedB h hr'⟩

/-- **Certified conflicts-with**. -/
theorem conflictsWith_of_conflictsWithB (h : pkb.pWellFormed = true)
    (hsym : pkb.symProps = []) (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true)
    {p q : Pid} (hb : pkb.conflictsWithB p q = true) : pkb.toLayer.ConflictsWith p q := by
  intro s o o' h1 h2
  have hr1 : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup h1
  have hr2 : pkb.relatedB q s o' = true := relatedB_of_holds h hsym hinv hup h2
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr1
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v1, hsupv1⟩ := exists_supportsB_value h hsym hinv hr1
  obtain ⟨v2, hsupv2⟩ := exists_supportsB_value h hsym hinv hr2
  have hp : pkb.hasValueB p s = true :=
    hasValueB_iff.2 ⟨o, (mem_items_of_supportsB h hsupv1).2, hr1⟩
  have hq : pkb.hasValueB q s = true :=
    hasValueB_iff.2 ⟨o', (mem_items_of_supportsB h hsupv2).2, hr2⟩
  have := List.all_eq_true.1 hb s hsmem
  rw [hp, hq] at this
  simp at this

/-- **Certified one-of**. -/
theorem oneOf_of_oneOfB (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid}
    {vals : List Qid} (hb : pkb.oneOfB p vals = true) :
    pkb.toLayer.OneOf p {x | x ∈ vals} := by
  intro s o hs
  have hr : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup hs
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr
  have hmem : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨(mem_items_of_supportsB h hsupv).2, hr⟩
  simpa using List.all_eq_true.1 (List.all_eq_true.1 hb s hsmem) o hmem

/-- **Certified none-of**. -/
theorem noneOf_of_noneOfB (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid}
    {vals : List Qid} (hb : pkb.noneOfB p vals = true) :
    pkb.toLayer.NoneOf p {x | x ∈ vals} := by
  intro s o hs
  have hr : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup hs
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr
  have hmem : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨(mem_items_of_supportsB h hsupv).2, hr⟩
  simpa using List.all_eq_true.1 (List.all_eq_true.1 hb s hsmem) o hmem

/-- **Certified inverse constraint**. -/
theorem inverseConstraint_of_inverseConstraintB (h : pkb.pWellFormed = true)
    (hsym : pkb.symProps = []) (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true)
    {p q : Pid} (hb : pkb.inverseConstraintB p q = true) :
    pkb.toLayer.InverseConstraint p q := by
  intro s o hs
  have hr : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup hs
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr
  have hsmem : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr
  have hmem : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨(mem_items_of_supportsB h hsupv).2, hr⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 hb s hsmem) o hmem
  exact holds_of_relatedB h this

end PKB

/-! ### A worked fragment

Douglas Adams (Q42) is born in Cambridge (Q350), a city (Q515) in the United Kingdom
(Q145), of which he is a citizen; the properties are `place of birth` (P19), `country of
citizenship` (P27) and `country` (P17). -/

namespace StatementConstraintExample

open KB PKB PropertyLayer

/-- Abbreviation for an item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a property. -/
def P (s : String) : Pid := .wd s

/-- The item layer of the fragment. -/
def bioBase : KB where
  name := "bio"
  items := [Q "Q42", Q "Q350", Q "Q145", Q "Q5", Q "Q515", Q "Q6256"]
  levels := [(Q "Q42", 0), (Q "Q350", 0), (Q "Q145", 0), (Q "Q5", 1), (Q "Q515", 1),
             (Q "Q6256", 1)]
  inst := [(Q "Q42", Q "Q5"), (Q "Q350", Q "Q515"), (Q "Q145", Q "Q6256")]

theorem bioBase_valid : bioBase.valid = true := by decide

/-- The property layer: place of birth, country of citizenship and country. -/
def bio : PKB where
  base := bioBase
  props := [P "P19", P "P27", P "P17"]
  stmts := [(P "P19", Q "Q42", Q "Q350"), (P "P27", Q "Q42", Q "Q145"),
            (P "P17", Q "Q350", Q "Q145")]
  typeC := [(P "P19", Q "Q5"), (P "P27", Q "Q5"), (P "P17", Q "Q515")]
  valueTypeC := [(P "P19", Q "Q515"), (P "P27", Q "Q6256"), (P "P17", Q "Q6256")]

set_option maxRecDepth 40000 in
theorem bio_pvalid : bio.pvalid = true := by decide

theorem bio_pWellFormed : bio.pWellFormed = true := pvalid_pWellFormed bio_pvalid

set_option maxRecDepth 40000 in
theorem bio_transUpwardClosed : bio.transUpwardClosed = true := by decide

set_option maxRecDepth 40000 in
/-- Everyone with a `place of birth` also has a `country of citizenship`
(item-requires-statement, Q21503247). -/
theorem bio_itemRequires : bio.itemRequiresB (P "P19") (P "P27") = true := by decide

set_option maxRecDepth 40000 in
/-- Every `place of birth` value has a `country` of its own (value-requires-statement,
Q21510864). -/
theorem bio_valueRequires : bio.valueRequiresB (P "P19") (P "P17") = true := by decide

set_option maxRecDepth 40000 in
/-- The values of `country of citizenship` come from the declared list (one-of,
Q21510859). -/
theorem bio_oneOf : bio.oneOfB (P "P27") [Q "Q145"] = true := by decide

set_option maxRecDepth 40000 in
/-- No `country of citizenship` value is a city (none-of, Q52558054). -/
theorem bio_noneOf : bio.noneOfB (P "P27") [Q "Q350"] = true := by decide

set_option maxRecDepth 40000 in
/-- A constraint that the fragment violates is rejected: `place of birth` does not
conflict with `country of citizenship` here, since Douglas Adams has both. -/
theorem bio_conflicts_rejected : bio.conflictsWithB (P "P19") (P "P27") = false := by decide

set_option maxRecDepth 40000 in
/-- Two properties that no item uses together do pass the conflicts-with check. -/
theorem bio_conflicts_ok : bio.conflictsWithB (P "P19") (P "P17") = true := by decide

/-! The checks are transported to the abstract model. -/

/-- Abstractly: every subject of a `place of birth` statement has a `country of
citizenship` statement. -/
theorem bio_requiresStatement :
    bio.toLayer.RequiresStatement (P "P19") (P "P27") :=
  requiresStatement_of_itemRequiresB bio_pWellFormed rfl rfl bio_transUpwardClosed
    bio_itemRequires

/-- Abstractly: the value of a `place of birth` statement has a `country`. -/
theorem bio_valueRequiresStatement :
    bio.toLayer.ValueRequiresStatement (P "P19") (P "P17") :=
  valueRequiresStatement_of_valueRequiresB bio_pWellFormed rfl rfl bio_transUpwardClosed
    bio_valueRequires

/-- Abstractly: `place of birth` and `country` are never used by the same item. -/
theorem bio_conflictsWith : bio.toLayer.ConflictsWith (P "P19") (P "P17") :=
  conflictsWith_of_conflictsWithB bio_pWellFormed rfl rfl bio_transUpwardClosed
    bio_conflicts_ok

/-- Abstractly: the values of `country of citizenship` are among the listed items. -/
theorem bio_oneOfAbstract : bio.toLayer.OneOf (P "P27") {x | x ∈ [Q "Q145"]} :=
  oneOf_of_oneOfB bio_pWellFormed rfl rfl bio_transUpwardClosed bio_oneOf

end StatementConstraintExample

end Wikidata
