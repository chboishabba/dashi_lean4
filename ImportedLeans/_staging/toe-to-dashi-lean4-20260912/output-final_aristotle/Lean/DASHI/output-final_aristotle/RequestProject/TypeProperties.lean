import RequestProject.StatementConstraints

/-!
# `properties for this type` (P1963): what a class expects of its instances

Wikidata classes carry, besides their place in the `subclass of` hierarchy, a
*modelling profile*: the property `properties for this type` (P1963) lists the
properties that instances of a class are expected to have — `date of birth`
(P569) for a human, `country` (P17) for a geographic feature, and so on.  Unlike
a property constraint, P1963 is not a restriction on the statements that may be
made; it is a *completeness* requirement on the items.

This file adds that layer on top of the executable property layer
`Wikidata.PKB`:

* `Profile.expectedOfClass c` — the properties expected of instances of `c`,
  collected from `c` **and all of its superclasses**;
* `Profile.expectedOf a` — the properties expected of an item, collected from all
  the classes it is an instance of;
* `Profile.missingOf a` — the expected properties for which the item carries no
  statement, and the completeness checks `Profile.completeFor`, `Profile.completeB`.

The results are:

* the computations are certified — `mem_expectedOf_iff` and `completeFor_iff`
  describe exactly what they decide, and `expectedOf_eq_abstract` phrases the
  expectations of an item in terms of the *abstract* derived `instance of` of
  `RequestProject.Core`;
* expectations are **inherited downwards**: a subclass expects everything its
  superclasses expect (`expectedOfClass_subset_of_isSubclassOf`), and an instance
  of a class is held to the profile of every superclass of it
  (`mem_expectedOf_of_isInstanceOf`);
* a complete knowledge base therefore satisfies the *inherited* obligations, not
  merely the directly declared ones (`hasPropertyB_of_completeB`);
* adding statements can only help (`completeFor_withStmts`), whereas adding an
  `instance of` statement can destroy completeness — both are exhibited on a
  worked fragment;
* the layer is tied back to the abstract soft constraint
  `Wikidata.PropertiesForType` of `RequestProject.StatementConstraints`: a base
  passing the completeness check satisfies every P1963 declaration it makes, in
  the abstract sense (`propertiesForType_of_completeB`).
-/

namespace Wikidata

/-- A property knowledge base together with its `properties for this type`
(P1963) declarations: `(c, p)` records that instances of the class `c` are
expected to carry a statement with the property `p`. -/
structure Profile where
  /-- The underlying property layer. -/
  base : PKB
  /-- `properties for this type` (P1963) declarations, as `(class, property)` pairs. -/
  p1963 : List (Qid × Pid) := []
deriving Repr, DecidableEq, Inhabited

namespace Profile

variable (pf : Profile)

/-- The underlying item ontology. -/
def kb : KB := pf.base.base

/-- The properties declared for a class by a P1963 statement *on that class*. -/
def declaredFor (c : Qid) : List Pid := (pf.p1963.filter (fun r => r.1 == c)).map Prod.snd

/-- The properties expected of instances of a class: those declared for the class
itself and those declared for any of its superclasses. -/
def expectedOfClass (c : Qid) : List Pid :=
  (pf.p1963.filter (fun r => pf.kb.isSubclassOf c r.1)).map Prod.snd

/-- The properties expected of an item: those declared for any class it is an
instance of (derived `instance of`, so superclasses are already included). -/
def expectedOf (a : Qid) : List Pid :=
  (pf.p1963.filter (fun r => pf.kb.isInstanceOf a r.1)).map Prod.snd

/-- Decides whether an item carries a statement with the given property, or with
one of its subproperties. -/
def hasPropertyB (a : Qid) (p : Pid) : Bool :=
  pf.base.stmts.any (fun t => t.2.1 == a && pf.base.isSubPropertyOf t.1 p)

/-- The expected properties an item does not carry. -/
def missingOf (a : Qid) : List Pid := (pf.expectedOf a).filter (fun p => !pf.hasPropertyB a p)

/-- An item is *complete* when it carries every property expected of it. -/
def completeFor (a : Qid) : Bool := (pf.missingOf a).isEmpty

/-- The whole knowledge base is complete when each of its items is. -/
def completeB : Bool := pf.kb.items.all (fun a => pf.completeFor a)

/-- Well-formedness of the profile layer: P1963 statements mention declared items
and declared properties. -/
def profileWellFormed : Bool :=
  pf.p1963.all (fun r => r.1 ∈ pf.kb.items && r.2 ∈ pf.base.props)

/-- The profile obtained by asserting further statements. -/
def withStmts (ts : List (Pid × Qid × Qid)) : Profile :=
  { pf with base := { pf.base with stmts := pf.base.stmts ++ ts } }

/-- The profile obtained by asserting further `instance of` (P31) statements. -/
def withInst (ts : List (Qid × Qid)) : Profile :=
  { pf with base := { pf.base with base := { pf.base.base with inst := pf.base.base.inst ++ ts } } }

variable {pf}

/-! ### What the computations decide -/

theorem mem_declaredFor {c : Qid} {p : Pid} : p ∈ pf.declaredFor c ↔ (c, p) ∈ pf.p1963 := by
  simp [declaredFor, List.mem_filter, List.mem_map]

theorem mem_expectedOfClass_iff {c : Qid} {p : Pid} :
    p ∈ pf.expectedOfClass c ↔ ∃ d, (d, p) ∈ pf.p1963 ∧ pf.kb.isSubclassOf c d = true := by
  simp only [expectedOfClass, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨d, q⟩, ⟨hmem, hsub⟩, rfl⟩; exact ⟨d, hmem, hsub⟩
  · rintro ⟨d, hmem, hsub⟩; exact ⟨(d, p), ⟨hmem, hsub⟩, rfl⟩

theorem mem_expectedOf_iff {a : Qid} {p : Pid} :
    p ∈ pf.expectedOf a ↔ ∃ c, (c, p) ∈ pf.p1963 ∧ pf.kb.isInstanceOf a c = true := by
  simp only [expectedOf, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨c, q⟩, ⟨hmem, hinst⟩, rfl⟩; exact ⟨c, hmem, hinst⟩
  · rintro ⟨c, hmem, hinst⟩; exact ⟨(c, p), ⟨hmem, hinst⟩, rfl⟩

theorem hasPropertyB_iff {a : Qid} {p : Pid} :
    pf.hasPropertyB a p = true ↔
      ∃ q o, (q, a, o) ∈ pf.base.stmts ∧ pf.base.isSubPropertyOf q p = true := by
  simp only [hasPropertyB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨q, s, o⟩, hmem, rfl, hsub⟩; exact ⟨q, o, hmem, hsub⟩
  · rintro ⟨q, o, hmem, hsub⟩; exact ⟨(q, a, o), hmem, rfl, hsub⟩

/-- An item is complete exactly when it carries every property expected of it. -/
theorem completeFor_iff {a : Qid} :
    pf.completeFor a = true ↔ ∀ p ∈ pf.expectedOf a, pf.hasPropertyB a p = true := by
  simp [completeFor, missingOf, List.isEmpty_iff, List.filter_eq_nil_iff]

theorem completeB_iff :
    pf.completeB = true ↔ ∀ a ∈ pf.kb.items, ∀ p ∈ pf.expectedOf a, pf.hasPropertyB a p = true := by
  simp only [completeB, List.all_eq_true]
  exact ⟨fun h a ha => completeFor_iff.1 (h a ha), fun h a ha => completeFor_iff.2 (h a ha)⟩

/-! ### Inheritance of expectations -/

/-- **Expectations are inherited downwards**: a subclass is expected to carry
everything its superclasses expect. -/
theorem expectedOfClass_subset_of_isSubclassOf (hwf : pf.kb.wellFormed = true) {c d : Qid}
    (hcd : pf.kb.isSubclassOf c d = true) : pf.expectedOfClass d ⊆ pf.expectedOfClass c := by
  intro p hp
  obtain ⟨e, hmem, hde⟩ := mem_expectedOfClass_iff.1 hp
  exact mem_expectedOfClass_iff.2 ⟨e, hmem, KB.isSubclassOf_trans hwf hcd hde⟩

/-- Everything declared for a class is expected of it. -/
theorem declaredFor_subset_expectedOfClass (c : Qid) :
    pf.declaredFor c ⊆ pf.expectedOfClass c := by
  intro p hp
  exact mem_expectedOfClass_iff.2 ⟨c, mem_declaredFor.1 hp, KB.isSubclassOf_refl _ c⟩

/-- **An instance is held to the profile of every class it belongs to**, including
the classes it belongs to only through the `subclass of` hierarchy. -/
theorem mem_expectedOf_of_isInstanceOf (hwf : pf.kb.wellFormed = true) {a c : Qid} {p : Pid}
    (hac : pf.kb.isInstanceOf a c = true) (hp : p ∈ pf.expectedOfClass c) :
    p ∈ pf.expectedOf a := by
  obtain ⟨d, hmem, hcd⟩ := mem_expectedOfClass_iff.1 hp
  exact mem_expectedOf_iff.2 ⟨d, hmem, KB.isInstanceOf_trans_subclass hwf hac hcd⟩

/-- The expectations of an item, phrased in the abstract semantics of
`RequestProject.Core`: they are exactly the properties declared for some class the
item is an instance of, in the derived (inheritance-closed) sense. -/
theorem expectedOf_eq_abstract (hv : pf.kb.valid = true) {a : Qid} {p : Pid} :
    p ∈ pf.expectedOf a ↔ ∃ c, (c, p) ∈ pf.p1963 ∧ (pf.kb.toOntology hv).InstanceOf a c := by
  rw [mem_expectedOf_iff]
  exact exists_congr fun c =>
    and_congr_right fun _ => KB.isInstanceOf_iff_instanceOf hv a c

/-- In a complete knowledge base every item really does carry the properties its
classes — and their superclasses — ask for. -/
theorem hasPropertyB_of_completeB (hwf : pf.kb.wellFormed = true) (hc : pf.completeB = true)
    {a c : Qid} {p : Pid} (ha : a ∈ pf.kb.items) (hac : pf.kb.isInstanceOf a c = true)
    (hp : p ∈ pf.expectedOfClass c) : pf.hasPropertyB a p = true :=
  completeB_iff.1 hc a ha p (mem_expectedOf_of_isInstanceOf hwf hac hp)

/-! ### The bridge to the abstract soft constraint -/

theorem hasPropertyB_iff_exists_supportsB {a : Qid} {p : Pid} :
    pf.hasPropertyB a p = true ↔ ∃ o, pf.base.supportsB p a o = true := by
  rw [hasPropertyB_iff]
  constructor
  · rintro ⟨q, o, hmem, hsub⟩; exact ⟨o, PKB.supportsB_iff.2 ⟨q, hmem, hsub⟩⟩
  · rintro ⟨o, ho⟩
    obtain ⟨q, hmem, hsub⟩ := PKB.supportsB_iff.1 ho
    exact ⟨q, o, hmem, hsub⟩

/-- **A complete knowledge base satisfies its `properties for this type`
declarations** in the abstract sense of `Wikidata.PropertiesForType`: every
instance — direct or inherited — of a class carrying a P1963 declaration really
has a value for the declared property. -/
theorem propertiesForType_of_completeB (hv : pf.kb.valid = true)
    (hpwf : pf.base.pWellFormed = true) (hc : pf.completeB = true) {c : Qid} {p : Pid}
    (hmem : (c, p) ∈ pf.p1963) :
    PropertiesForType (pf.kb.toOntology hv) pf.base.toLayer c p := by
  intro a ha
  obtain ⟨d, hd, -⟩ := id ha
  have hwf := KB.valid_wellFormed hv
  have hitem : a ∈ pf.kb.items := (KB.wf_inst hwf hd).1
  have hinst : pf.kb.isInstanceOf a c = true := (KB.isInstanceOf_iff_instanceOf hv a c).2 ha
  have hexp : p ∈ pf.expectedOf a := mem_expectedOf_iff.2 ⟨c, hmem, hinst⟩
  obtain ⟨o, ho⟩ := hasPropertyB_iff_exists_supportsB.1 (completeB_iff.1 hc a hitem p hexp)
  exact ⟨o, PKB.holds_of_supportsB hpwf ho⟩

/-! ### Stability -/

@[simp] theorem withStmts_kb (ts : List (Pid × Qid × Qid)) : (pf.withStmts ts).kb = pf.kb := rfl

@[simp] theorem withStmts_expectedOf (ts : List (Pid × Qid × Qid)) (a : Qid) :
    (pf.withStmts ts).expectedOf a = pf.expectedOf a := rfl

@[simp] theorem withStmts_isSubPropertyOf (ts : List (Pid × Qid × Qid)) (p q : Pid) :
    (pf.withStmts ts).base.isSubPropertyOf p q = pf.base.isSubPropertyOf p q := rfl

theorem hasPropertyB_withStmts (ts : List (Pid × Qid × Qid)) {a : Qid} {p : Pid}
    (h : pf.hasPropertyB a p = true) : (pf.withStmts ts).hasPropertyB a p = true := by
  obtain ⟨q, o, hmem, hsub⟩ := hasPropertyB_iff.1 h
  exact hasPropertyB_iff.2 ⟨q, o, by simp [withStmts, hmem], hsub⟩

/-- **Asserting more statements never destroys completeness**: the obligations of an
item depend only on its classes, and the statements that discharge them are only
ever added to. -/
theorem completeFor_withStmts (ts : List (Pid × Qid × Qid)) {a : Qid}
    (h : pf.completeFor a = true) : (pf.withStmts ts).completeFor a = true := by
  refine completeFor_iff.2 fun p hp => ?_
  rw [withStmts_expectedOf] at hp
  exact hasPropertyB_withStmts ts (completeFor_iff.1 h p hp)

@[simp] theorem withInst_isSubclassOf (ts : List (Qid × Qid)) (a b : Qid) :
    (pf.withInst ts).kb.isSubclassOf a b = pf.kb.isSubclassOf a b := rfl

/-- Asserting more `instance of` statements only *adds* obligations. -/
theorem expectedOf_subset_withInst (ts : List (Qid × Qid)) (a : Qid) :
    pf.expectedOf a ⊆ (pf.withInst ts).expectedOf a := by
  intro p hp
  obtain ⟨c, hmem, hinst⟩ := mem_expectedOf_iff.1 hp
  refine mem_expectedOf_iff.2 ⟨c, hmem, ?_⟩
  simp only [KB.isInstanceOf, List.any_eq_true] at hinst ⊢
  obtain ⟨d, hd, hdc⟩ := hinst
  refine ⟨d, KB.mem_directClassesL.2 ?_, by simpa using hdc⟩
  have : pf.kb.Inst a d := KB.mem_directClassesL.1 hd
  simpa [withInst, kb, KB.Inst] using Or.inl this

end Profile

/-! ## A worked fragment

`person` (Q215627) declares `date of birth` (P569) as a property for its type and
`human` (Q5), a subclass of it, declares `country of citizenship` (P27).  Douglas
Adams (Q42) is an instance of `human`, so he is expected to carry *both*. -/

namespace TypeProfileExample

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a Wikidata property. -/
def P (s : String) : Pid := .wd s

/-- The item layer: Douglas Adams, the United Kingdom and a date, below the
classes `human`, `person` and `entity`. -/
def base : KB where
  name := "wd-profile"
  items := [Q "Q42", Q "Q145", Q "V1952", Q "Q5", Q "Q215627", Q "Q35120"]
  levels := [(Q "Q42", 0), (Q "Q145", 0), (Q "V1952", 0),
             (Q "Q5", 1), (Q "Q215627", 1), (Q "Q35120", 1)]
  sub := [(Q "Q5", Q "Q215627"), (Q "Q215627", Q "Q35120")]
  inst := [(Q "Q42", Q "Q5")]

set_option maxRecDepth 40000 in
theorem base_valid : base.valid = true := by decide

/-- The property layer: `date of birth` (P569) and `country of citizenship` (P27),
with a single asserted statement — Douglas Adams' date of birth. -/
def layer : PKB where
  base := base
  props := [P "P569", P "P27"]
  stmts := [(P "P569", Q "Q42", Q "V1952")]

/-- The modelling profile: persons are expected to have a date of birth, humans a
country of citizenship. -/
def profile : Profile where
  base := layer
  p1963 := [(Q "Q215627", P "P569"), (Q "Q5", P "P27")]

set_option maxRecDepth 40000 in
theorem profile_wellFormed : profile.profileWellFormed = true := by decide

set_option maxRecDepth 40000 in
/-- The declaration on `person` reaches an instance of the subclass `human`:
Douglas Adams is expected to have a date of birth. -/
theorem adams_expects_p569 : P "P569" ∈ profile.expectedOf (Q "Q42") := by decide

set_option maxRecDepth 40000 in
/-- ... and, from `human`, a country of citizenship, which he does not have. -/
theorem adams_missing_p27 : profile.missingOf (Q "Q42") = [P "P27"] := by decide

set_option maxRecDepth 40000 in
theorem adams_incomplete : profile.completeFor (Q "Q42") = false := by decide

set_option maxRecDepth 40000 in
/-- The class `human` is a *subclass* of `person`, not an instance of it, so the
profile of `person` puts no obligation on the class itself — only on its
instances. -/
theorem human_expects_nothing : profile.expectedOf (Q "Q5") = [] := by decide

set_option maxRecDepth 40000 in
/-- Nevertheless `human`, as a class, inherits the *expectations* of `person`. -/
theorem human_class_expects_p569 : P "P569" ∈ profile.expectedOfClass (Q "Q5") := by decide

set_option maxRecDepth 40000 in
/-- Asserting the missing statement completes the item — and the whole base. -/
theorem completed :
    (profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).completeB = true := by decide

set_option maxRecDepth 40000 in
/-- Adding an `instance of` statement, by contrast, *adds* obligations: declaring
the United Kingdom to be a human makes the completed base incomplete again. -/
theorem incomplete_again :
    ((profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).withInst
      [(Q "Q145", Q "Q5")]).completeB = false := by decide

set_option maxRecDepth 40000 in
theorem completed_pWellFormed :
    (profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).base.pWellFormed = true := by decide

/-- On the completed fragment the P1963 declaration on `human` holds in the
abstract sense: *every* instance of `human` has a country of citizenship. -/
theorem completed_satisfies_p27 :
    PropertiesForType
      ((profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).kb.toOntology base_valid)
      (profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).base.toLayer (Q "Q5") (P "P27") :=
  Profile.propertiesForType_of_completeB (pf := profile.withStmts [(P "P27", Q "Q42", Q "Q145")])
    base_valid completed_pWellFormed completed (by decide)

end TypeProfileExample

end Wikidata
