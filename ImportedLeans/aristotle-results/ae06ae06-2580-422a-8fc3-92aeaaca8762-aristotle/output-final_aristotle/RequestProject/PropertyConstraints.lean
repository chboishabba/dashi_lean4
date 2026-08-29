import RequestProject.PropertyEngine

/-!
# Further Wikidata property constraints

Besides the type and value-type constraints of `RequestProject.Properties`, the
Wikidata property constraint vocabulary contains, among others,

* the **single-value constraint** (Q19474404): a property has at most one value per
  subject;
* the **distinct-values constraint** (Q21502410): a value determines its subject;
* the **irreflexive constraint** (Q21510863): no item is related to itself.

This file adds these three, abstractly and executably, and draws the ontological
consequence that matters for the class of properties Wikidata declares transitive
(`part of` P361, `located in the administrative territorial entity` P131, ...): an
irreflexive transitive property is asymmetric and acyclic, hence a strict partial
order on the items it relates.

The executable checks `PKB.irreflexiveB`, `PKB.singleValueB` and
`PKB.distinctValuesB` are certified: for a property layer whose derived statements
the engine computes exactly (no symmetry, no inverses, transitivity inherited
upwards), passing the check implies the corresponding abstract property of
`PropertyLayer.Holds`.
-/

namespace Wikidata

namespace PropertyLayer

variable {I P : Type*} {L : PropertyLayer I P}

/-! ### Irreflexive transitive properties are strict orders -/

/-- An irreflexive transitive property is asymmetric. -/
theorem asymm_of_irrefl_trans {p : P} (htr : L.IsTransitive p)
    (hirr : ∀ s, ¬ L.Holds p s s) {a b : I} (hab : L.Holds p a b) (hba : L.Holds p b a) :
    False := hirr a (Holds.trans htr hab hba)

/-- An irreflexive transitive property has no cycles of any length. -/
theorem acyclic_of_irrefl_trans {p : P} (htr : L.IsTransitive p)
    (hirr : ∀ s, ¬ L.Holds p s s) (a : I) : ¬ Relation.TransGen (L.Holds p) a a := by
  intro h
  exact hirr a (holds_transGen htr h)

/-- An irreflexive transitive property is a strict order on the items. -/
theorem isStrictOrder_of_irrefl_trans {p : P} (htr : L.IsTransitive p)
    (hirr : ∀ s, ¬ L.Holds p s s) : IsStrictOrder I (L.Holds p) where
  irrefl := hirr
  trans _ _ _ hab hbc := Holds.trans htr hab hbc

/-! ### Single-value and distinct-values constraints -/

/-- The single-value constraint (Q19474404) for the property `p`. -/
def SingleValued (L : PropertyLayer I P) (p : P) : Prop :=
  ∀ {s o o' : I}, L.Holds p s o → L.Holds p s o' → o = o'

/-- The distinct-values constraint (Q21502410) for the property `p`. -/
def DistinctValued (L : PropertyLayer I P) (p : P) : Prop :=
  ∀ {s s' o : I}, L.Holds p s o → L.Holds p s' o → s = s'

/-- A single-valued transitive property relates each item to at most one item, so it
cannot have a chain of length two out of any item. -/
theorem eq_of_singleValued_trans {p : P} (hsv : L.SingleValued p) (htr : L.IsTransitive p)
    {a b c : I} (hab : L.Holds p a b) (hbc : L.Holds p b c) : b = c :=
  hsv hab (Holds.trans htr hab hbc)

/-- A single-valued irreflexive transitive property has no chains of length two. -/
theorem not_holds_two_step_of_singleValued {p : P} (hsv : L.SingleValued p)
    (htr : L.IsTransitive p) (hirr : ∀ s, ¬ L.Holds p s s) {a b c : I}
    (hab : L.Holds p a b) (hbc : L.Holds p b c) : False := by
  have : b = c := eq_of_singleValued_trans hsv htr hab hbc
  subst this
  exact hirr b hbc

/-- A property that is both single-valued and distinct-valued is a partial injection:
it relates `a` to `b` and `a'` to `b'` with `a = a'` exactly when `b = b'`. -/
theorem eq_iff_of_singleValued_distinctValued {p : P} (hsv : L.SingleValued p)
    (hdv : L.DistinctValued p) {a a' b b' : I} (h : L.Holds p a b) (h' : L.Holds p a' b') :
    a = a' ↔ b = b' :=
  ⟨fun haa => by subst haa; exact hsv h h', fun hbb => by subst hbb; exact hdv h h'⟩

end PropertyLayer

namespace PKB

variable (pkb : PKB)

/-! ### The executable checks -/

/-- The irreflexive constraint (Q21510863): no item is related to itself by `p`. -/
def irreflexiveB (p : Pid) : Bool := pkb.base.items.all (fun s => !pkb.relatedB p s s)

/-- The single-value constraint (Q19474404): every subject has at most one value. -/
def singleValueB (p : Pid) : Bool :=
  pkb.base.items.all (fun s =>
    (pkb.valuesOf p s).all (fun o => (pkb.valuesOf p s).all (fun o' => o == o')))

/-- The distinct-values constraint (Q21502410): every value has at most one subject. -/
def distinctValuesB (p : Pid) : Bool :=
  pkb.base.items.all (fun o =>
    (pkb.subjectsOf p o).all (fun s => (pkb.subjectsOf p o).all (fun s' => s == s')))

variable {pkb}

theorem mem_valuesOf {p : Pid} {s o : Qid} :
    o ∈ pkb.valuesOf p s ↔ o ∈ pkb.base.items ∧ pkb.relatedB p s o = true := by
  simp [valuesOf, List.mem_filter]

theorem mem_subjectsOf {p : Pid} {s o : Qid} :
    s ∈ pkb.subjectsOf p o ↔ s ∈ pkb.base.items ∧ pkb.relatedB p s o = true := by
  simp [subjectsOf, List.mem_filter]

/-- **Certified irreflexivity**: a property passing the irreflexive check relates no
item to itself in the abstract model. -/
theorem irreflexive_of_irreflexiveB (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid}
    (hb : pkb.irreflexiveB p = true) (s : Qid) : ¬ pkb.toLayer.Holds p s s := by
  intro hholds
  have hrel : pkb.relatedB p s s = true := relatedB_of_holds h hsym hinv hup hholds
  obtain ⟨o', hsup⟩ := exists_supportsB_subject hsym hinv hrel
  have hs : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  have := List.all_eq_true.1 hb s hs
  simp [hrel] at this

/-- **Certified single-valuedness**. -/
theorem singleValued_of_singleValueB (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid}
    (hb : pkb.singleValueB p = true) : pkb.toLayer.SingleValued p := by
  intro s o o' h1 h2
  have hr1 : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup h1
  have hr2 : pkb.relatedB p s o' = true := relatedB_of_holds h hsym hinv hup h2
  obtain ⟨u, hsup⟩ := exists_supportsB_subject hsym hinv hr1
  have hs : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup).1
  obtain ⟨v1, hsup1⟩ := exists_supportsB_value h hsym hinv hr1
  obtain ⟨v2, hsup2⟩ := exists_supportsB_value h hsym hinv hr2
  have ho : o ∈ pkb.base.items := (mem_items_of_supportsB h hsup1).2
  have ho' : o' ∈ pkb.base.items := (mem_items_of_supportsB h hsup2).2
  have hmem : o ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨ho, hr1⟩
  have hmem' : o' ∈ pkb.valuesOf p s := mem_valuesOf.2 ⟨ho', hr2⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 hb s hs) o hmem
  simpa using List.all_eq_true.1 this o' hmem'

/-- **Certified distinctness of values**. -/
theorem distinctValued_of_distinctValuesB (h : pkb.pWellFormed = true)
    (hsym : pkb.symProps = []) (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true)
    {p : Pid} (hb : pkb.distinctValuesB p = true) : pkb.toLayer.DistinctValued p := by
  intro s s' o h1 h2
  have hr1 : pkb.relatedB p s o = true := relatedB_of_holds h hsym hinv hup h1
  have hr2 : pkb.relatedB p s' o = true := relatedB_of_holds h hsym hinv hup h2
  obtain ⟨u1, hsup1⟩ := exists_supportsB_subject hsym hinv hr1
  obtain ⟨u2, hsup2⟩ := exists_supportsB_subject hsym hinv hr2
  obtain ⟨v, hsupv⟩ := exists_supportsB_value h hsym hinv hr1
  have hs : s ∈ pkb.base.items := (mem_items_of_supportsB h hsup1).1
  have hs' : s' ∈ pkb.base.items := (mem_items_of_supportsB h hsup2).1
  have ho : o ∈ pkb.base.items := (mem_items_of_supportsB h hsupv).2
  have hmem : s ∈ pkb.subjectsOf p o := mem_subjectsOf.2 ⟨hs, hr1⟩
  have hmem' : s' ∈ pkb.subjectsOf p o := mem_subjectsOf.2 ⟨hs', hr2⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 hb o ho) s hmem
  simpa using List.all_eq_true.1 this s' hmem'

/-- A transitive property passing the irreflexivity check is acyclic in the abstract
model: no chain of statements returns to its starting point. -/
theorem acyclic_of_irreflexiveB (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid}
    (htr : pkb.isTransB p = true) (hb : pkb.irreflexiveB p = true) (a : Qid) :
    ¬ Relation.TransGen (pkb.toLayer.Holds p) a a :=
  PropertyLayer.acyclic_of_irrefl_trans (by simpa [toLayer, isTransB] using htr)
    (irreflexive_of_irreflexiveB h hsym hinv hup hb) a

end PKB

end Wikidata
