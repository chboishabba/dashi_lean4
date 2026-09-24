import RequestProject.Engine
import RequestProject.Properties

/-!
# An executable property layer

`Wikidata.PKB` ("property knowledge base") extends a `Wikidata.KB` with the
*property* part of the Wikidata ontology: a list of properties (PIDs), their
`subproperty of` (P1647) hierarchy, the statements made with them, the
declarations that a property is transitive or symmetric, the `inverse property`
(P1696) pairs, and the type (Q21503250) and value-type (Q21510865) constraints.

Everything is computable:

* `PKB.isSubPropertyOf` decides the property hierarchy (certified against
  `Relation.ReflTransGen` in `PKB.isSubPropertyOf_iff`);
* `PKB.supportsB p s o` decides whether the statement `⟨s, p, o⟩` follows from an
  asserted statement made with a subproperty of `p`;
* `PKB.relatedB p s o` additionally applies symmetry, inverses and — for a
  property declared transitive — transitive closure;
* `PKB.pvalid` validates the whole thing, including the property constraints.

The Boolean computations are certified against the abstract model of
`RequestProject.Properties`: `PKB.holds_of_relatedB` is soundness (everything
computed is derivable) and `PKB.relatedB_of_holds` is completeness for property
layers without symmetry or inverse declarations whose transitivity declarations
are inherited upwards.
-/

namespace Wikidata

/-- A Wikidata property identifier, e.g. `Pid.wd "P361"` for *part of*. -/
inductive Pid where
  /-- The Wikidata property with the given identifier. -/
  | wd (id : String)
deriving DecidableEq, Repr, Inhabited

/-- A finite, executable Wikidata property layer on top of a knowledge base. -/
structure PKB where
  /-- The underlying item ontology. -/
  base : KB
  /-- The properties of the ontology. -/
  props : List Pid := []
  /-- Direct `subproperty of` (P1647) statements. -/
  subProp : List (Pid × Pid) := []
  /-- Statements `⟨subject, property, value⟩`, written `(p, s, o)`. -/
  stmts : List (Pid × Qid × Qid) := []
  /-- Properties declared transitive. -/
  transProps : List Pid := []
  /-- Properties declared symmetric. -/
  symProps : List Pid := []
  /-- `inverse property` (P1696) pairs. -/
  inverses : List (Pid × Pid) := []
  /-- Type constraints: `(p, c)` requires subjects of `p` to be instances of `c`. -/
  typeC : List (Pid × Qid) := []
  /-- Value-type constraints: `(p, c)` requires values of `p` to be instances of `c`. -/
  valueTypeC : List (Pid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace PKB

variable (pkb : PKB)

/-! ### The property hierarchy -/

/-- The properties, as a `Finset`. -/
def allP : Finset Pid := pkb.props.toFinset

/-- The direct superproperties of a property. -/
def superPropsL (p : Pid) : List Pid := (pkb.subProp.filter (fun r => r.1 == p)).map Prod.snd

/-- The direct superproperties of a property, as a `Finset`. -/
def superProps (p : Pid) : Finset Pid := (pkb.superPropsL p).toFinset

/-- All superproperties of a property, computed by saturating the P1647 graph. -/
def superProperties (p : Pid) : Finset Pid := Reach.reach pkb.superProps pkb.allP p

/-- Decides derived `subproperty of`. -/
def isSubPropertyOf (p q : Pid) : Bool := q ∈ pkb.superProperties p

/-- Decides whether two properties are declared inverse to one another. -/
def inverseOfB (p q : Pid) : Bool :=
  pkb.inverses.any (fun r => (r.1 == p && r.2 == q) || (r.1 == q && r.2 == p))

/-- Decides whether a property is declared transitive. -/
def isTransB (p : Pid) : Bool := p ∈ pkb.transProps

/-- Decides whether a property is declared symmetric. -/
def isSymB (p : Pid) : Bool := p ∈ pkb.symProps

/-! ### Statements -/

/-- Decides whether `⟨s, p, o⟩` is supported by an asserted statement made with a
subproperty of `p`. -/
def supportsB (p : Pid) (s o : Qid) : Bool :=
  pkb.stmts.any (fun t => pkb.isSubPropertyOf t.1 p && t.2.1 == s && t.2.2 == o)

/-- The one-step pairs for a property: the statements of its subproperties, plus the
reversed ones coming from a symmetry declaration or from an inverse property. -/
def basePairsL (p : Pid) : List (Qid × Qid) :=
  ((pkb.stmts.filter (fun t => pkb.isSubPropertyOf t.1 p)).map (fun t => (t.2.1, t.2.2))) ++
  ((pkb.stmts.filter (fun t => pkb.isSymB p && pkb.isSubPropertyOf t.1 p)).map
    (fun t => (t.2.2, t.2.1))) ++
  ((pkb.stmts.filter
      (fun t => pkb.props.any (fun r => pkb.isSubPropertyOf t.1 r && pkb.inverseOfB r p))).map
    (fun t => (t.2.2, t.2.1)))

/-- The values reachable from `s` in one step of the property `p`. -/
def stepPairs (p : Pid) (s : Qid) : Finset Qid :=
  (((pkb.basePairsL p).filter (fun r => r.1 == s)).map Prod.snd).toFinset

/-- Decides a one-step `p`-statement (subproperties, symmetry and inverses applied). -/
def oneStepB (p : Pid) (s o : Qid) : Bool := o ∈ pkb.stepPairs p s

/-- Decides a chain of `p`-statements, used for properties declared transitive. -/
def chainB (p : Pid) (s o : Qid) : Bool :=
  decide (∃ m ∈ pkb.stepPairs p s, o ∈ Reach.reach (pkb.stepPairs p) pkb.base.allF m)

/-- The full computable statement query: one step for an ordinary property, the
transitive closure for a property declared transitive. -/
def relatedB (p : Pid) (s o : Qid) : Bool :=
  if pkb.isTransB p then pkb.chainB p s o else pkb.oneStepB p s o

/-- All values of the property `p` at the subject `s`, among the items. -/
def valuesOf (p : Pid) (s : Qid) : List Qid :=
  pkb.base.items.filter (fun o => pkb.relatedB p s o)

/-- All subjects with the value `o` for the property `p`, among the items. -/
def subjectsOf (p : Pid) (o : Qid) : List Qid :=
  pkb.base.items.filter (fun s => pkb.relatedB p s o)

/-! ### The validator -/

/-- All property statements mention declared properties and declared items. -/
def pWellFormed : Bool :=
  pkb.subProp.all (fun r => r.1 ∈ pkb.props && r.2 ∈ pkb.props) &&
  pkb.stmts.all
    (fun t => t.1 ∈ pkb.props && t.2.1 ∈ pkb.base.items && t.2.2 ∈ pkb.base.items) &&
  pkb.transProps.all (fun p => p ∈ pkb.props) &&
  pkb.symProps.all (fun p => p ∈ pkb.props) &&
  pkb.inverses.all (fun r => r.1 ∈ pkb.props && r.2 ∈ pkb.props) &&
  pkb.typeC.all (fun r => r.1 ∈ pkb.props && r.2 ∈ pkb.base.items) &&
  pkb.valueTypeC.all (fun r => r.1 ∈ pkb.props && r.2 ∈ pkb.base.items)

/-- Every type constraint is respected by the statements. -/
def typeConstraintsOk : Bool :=
  pkb.typeC.all (fun r => pkb.stmts.all
    (fun t => !pkb.isSubPropertyOf t.1 r.1 || pkb.base.isInstanceOf t.2.1 r.2))

/-- Every value-type constraint is respected by the statements. -/
def valueTypeConstraintsOk : Bool :=
  pkb.valueTypeC.all (fun r => pkb.stmts.all
    (fun t => !pkb.isSubPropertyOf t.1 r.1 || pkb.base.isInstanceOf t.2.2 r.2))

/-- The full validity check: the item ontology, the property layer, and the
constraints. -/
def pvalid : Bool :=
  pkb.base.valid && pkb.pWellFormed && pkb.typeConstraintsOk && pkb.valueTypeConstraintsOk

/-- Transitivity declarations are inherited by superproperties. -/
def transUpwardClosed : Bool :=
  pkb.subProp.all (fun r => !pkb.isTransB r.1 || pkb.isTransB r.2)

/-! ### Semantics -/

/-- The abstract property layer determined by a property knowledge base. -/
def toLayer : PropertyLayer Qid Pid where
  Stmt p s o := (p, s, o) ∈ pkb.stmts
  SubProp p q := (p, q) ∈ pkb.subProp
  IsTransitive p := p ∈ pkb.transProps
  IsSymmetric p := p ∈ pkb.symProps
  InverseOf p q := (p, q) ∈ pkb.inverses ∨ (q, p) ∈ pkb.inverses
  inverseOf_symm h := h.symm

/-- The abstract constraints determined by a property knowledge base. -/
def toConstraints : PropertyLayer.Constraints Qid Pid where
  TypeC p c := (p, c) ∈ pkb.typeC
  ValueTypeC p c := (p, c) ∈ pkb.valueTypeC

@[simp] theorem toLayer_Stmt (p : Pid) (s o : Qid) :
    pkb.toLayer.Stmt p s o ↔ (p, s, o) ∈ pkb.stmts := Iff.rfl

@[simp] theorem toLayer_SubProp (p q : Pid) :
    pkb.toLayer.SubProp p q ↔ (p, q) ∈ pkb.subProp := Iff.rfl

variable {pkb}

/-! ### Certification of the property hierarchy -/

theorem mem_superProps {p q : Pid} : q ∈ pkb.superProps p ↔ pkb.toLayer.SubProp p q := by
  simp [superProps, superPropsL, toLayer, List.mem_filter, List.mem_map]

theorem succ_eq_subProp (pkb : PKB) :
    (fun u v => v ∈ pkb.superProps u) = pkb.toLayer.SubProp := by
  funext u v; exact propext mem_superProps

theorem pwf_subProp (h : pkb.pWellFormed = true) {p q : Pid} (hpq : pkb.toLayer.SubProp p q) :
    p ∈ pkb.props ∧ q ∈ pkb.props := by
  simp only [pWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := h.1.1.1.1.1.1 (p, q) hpq
  simpa using this

theorem pwf_stmt (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hst : (p, s, o) ∈ pkb.stmts) :
    p ∈ pkb.props ∧ s ∈ pkb.base.items ∧ o ∈ pkb.base.items := by
  simp only [pWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := h.1.1.1.1.1.2 (p, s, o) hst
  simpa [and_assoc] using this

theorem superProps_subset_allP (h : pkb.pWellFormed = true) (p : Pid) :
    pkb.superProps p ⊆ pkb.allP := by
  intro q hq
  simpa [allP] using (pwf_subProp h (mem_superProps.1 hq)).2

theorem superProps_eq_empty_of_not_mem (h : pkb.pWellFormed = true) {p : Pid}
    (hp : p ∉ pkb.allP) : pkb.superProps p = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun q hq => ?_
  exact hp (by simpa [allP] using (pwf_subProp h (mem_superProps.1 hq)).1)

/-- **Certified property-hierarchy computation**: the Boolean check
`isSubPropertyOf` decides the reflexive–transitive closure of the asserted
`subproperty of` statements. -/
theorem isSubPropertyOf_iff (h : pkb.pWellFormed = true) (p q : Pid) :
    pkb.isSubPropertyOf p q = true ↔ pkb.toLayer.SubPropertyOf p q := by
  have hR := Reach.mem_reach_iff_of_closed pkb.superProps (superProps_subset_allP h)
    (fun y hy => superProps_eq_empty_of_not_mem h hy) p q
  rw [succ_eq_subProp] at hR
  simpa [isSubPropertyOf, superProperties, PropertyLayer.SubPropertyOf] using hR

theorem isSubPropertyOf_refl (pkb : PKB) (p : Pid) : pkb.isSubPropertyOf p p = true := by
  simpa [isSubPropertyOf, superProperties] using Reach.mem_reach_self pkb.superProps pkb.allP p

/-! ### The shape of the computed statement relations -/

theorem supportsB_iff {p : Pid} {s o : Qid} :
    pkb.supportsB p s o = true ↔
      ∃ q, (q, s, o) ∈ pkb.stmts ∧ pkb.isSubPropertyOf q p = true := by
  simp only [supportsB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨q, a, b⟩, hmem, ⟨hsub, rfl⟩, rfl⟩
    exact ⟨q, hmem, hsub⟩
  · rintro ⟨q, hmem, hsub⟩
    exact ⟨(q, s, o), hmem, ⟨hsub, rfl⟩, rfl⟩

theorem mem_basePairsL_iff {p : Pid} {s o : Qid} :
    (s, o) ∈ pkb.basePairsL p ↔
      pkb.supportsB p s o = true ∨
      (pkb.isSymB p = true ∧ pkb.supportsB p o s = true) ∨
      (∃ q r, r ∈ pkb.props ∧ (q, o, s) ∈ pkb.stmts ∧ pkb.isSubPropertyOf q r = true ∧
        pkb.inverseOfB r p = true) := by
  simp only [basePairsL, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Prod.mk.injEq, List.any_eq_true]
  constructor
  · rintro ((⟨⟨q, a, b⟩, ⟨hmem, hsub⟩, rfl, rfl⟩ |
      ⟨⟨q, a, b⟩, ⟨hmem, hsym, hsub⟩, rfl, rfl⟩) |
      ⟨⟨q, a, b⟩, ⟨hmem, r, hr, hqr, hrp⟩, rfl, rfl⟩)
    · exact Or.inl (supportsB_iff.2 ⟨q, hmem, hsub⟩)
    · exact Or.inr (Or.inl ⟨hsym, supportsB_iff.2 ⟨q, hmem, hsub⟩⟩)
    · exact Or.inr (Or.inr ⟨q, r, hr, hmem, hqr, hrp⟩)
  · rintro (h | ⟨hsym, h⟩ | ⟨q, r, hr, hmem, hqr, hrp⟩)
    · obtain ⟨q, hmem, hsub⟩ := supportsB_iff.1 h
      exact Or.inl (Or.inl ⟨(q, s, o), ⟨hmem, hsub⟩, rfl, rfl⟩)
    · obtain ⟨q, hmem, hsub⟩ := supportsB_iff.1 h
      exact Or.inl (Or.inr ⟨(q, o, s), ⟨hmem, hsym, hsub⟩, rfl, rfl⟩)
    · exact Or.inr ⟨(q, o, s), ⟨hmem, r, hr, hqr, hrp⟩, rfl, rfl⟩

theorem mem_stepPairs_iff {p : Pid} {s o : Qid} :
    o ∈ pkb.stepPairs p s ↔ (s, o) ∈ pkb.basePairsL p := by
  simp only [stepPairs, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hmem, rfl⟩, rfl⟩; exact hmem
  · intro hmem; exact ⟨(s, o), ⟨hmem, rfl⟩, rfl⟩

theorem mem_items_of_supportsB (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : pkb.supportsB p s o = true) : s ∈ pkb.base.items ∧ o ∈ pkb.base.items := by
  obtain ⟨q, hmem, -⟩ := supportsB_iff.1 hs
  exact (pwf_stmt h hmem).2

theorem mem_items_of_mem_basePairsL (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : (s, o) ∈ pkb.basePairsL p) : s ∈ pkb.base.items ∧ o ∈ pkb.base.items := by
  rcases mem_basePairsL_iff.1 hs with h1 | ⟨-, h1⟩ | ⟨q, -, -, hmem, -, -⟩
  · exact mem_items_of_supportsB h h1
  · exact (mem_items_of_supportsB h h1).symm
  · exact ((pwf_stmt h hmem).2).symm

theorem stepPairs_subset_items (h : pkb.pWellFormed = true) (p : Pid) (s : Qid) :
    pkb.stepPairs p s ⊆ pkb.base.allF := by
  intro o ho
  simpa [KB.allF] using (mem_items_of_mem_basePairsL h (mem_stepPairs_iff.1 ho)).2

theorem stepPairs_eq_empty_of_not_mem (h : pkb.pWellFormed = true) {p : Pid} {s : Qid}
    (hs : s ∉ pkb.base.allF) : pkb.stepPairs p s = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun o ho => ?_
  exact hs (by simpa [KB.allF] using (mem_items_of_mem_basePairsL h (mem_stepPairs_iff.1 ho)).1)

/-- Reachability along one-step `p`-pairs is decided by the saturation procedure. -/
theorem mem_reach_stepPairs_iff (h : pkb.pWellFormed = true) (p : Pid) (s o : Qid) :
    o ∈ Reach.reach (pkb.stepPairs p) pkb.base.allF s ↔
      Relation.ReflTransGen (fun u v => v ∈ pkb.stepPairs p u) s o :=
  Reach.mem_reach_iff_of_closed _ (stepPairs_subset_items h p)
    (fun _ hy => stepPairs_eq_empty_of_not_mem h hy) s o

/-! ### Soundness of the statement queries -/

theorem holds_of_supportsB (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : pkb.supportsB p s o = true) : pkb.toLayer.Holds p s o := by
  obtain ⟨q, hmem, hsub⟩ := supportsB_iff.1 hs
  exact PropertyLayer.holds_of_subPropertyOf ((isSubPropertyOf_iff h q p).1 hsub)
    (PropertyLayer.Holds.stmt hmem)

theorem holds_of_mem_basePairsL (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : (s, o) ∈ pkb.basePairsL p) : pkb.toLayer.Holds p s o := by
  rcases mem_basePairsL_iff.1 hs with h1 | ⟨hsym, h1⟩ | ⟨q, r, -, hmem, hqr, hrp⟩
  · exact holds_of_supportsB h h1
  · refine PropertyLayer.Holds.symm (by simpa [toLayer, isSymB] using hsym) ?_
    exact holds_of_supportsB h h1
  · have hr : pkb.toLayer.Holds r o s :=
      PropertyLayer.holds_of_subPropertyOf ((isSubPropertyOf_iff h q r).1 hqr)
        (PropertyLayer.Holds.stmt hmem)
    have hinvrp : pkb.toLayer.InverseOf r p := by
      simp only [inverseOfB, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hrp
      obtain ⟨⟨x, y⟩, hmem', hxy⟩ := hrp
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hmem'
      · exact Or.inr hmem'
    exact PropertyLayer.Holds.inv hinvrp hr

theorem holds_of_mem_stepPairs (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : o ∈ pkb.stepPairs p s) : pkb.toLayer.Holds p s o :=
  holds_of_mem_basePairsL h (mem_stepPairs_iff.1 hs)

theorem holds_of_oneStepB (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : pkb.oneStepB p s o = true) : pkb.toLayer.Holds p s o :=
  holds_of_mem_stepPairs h (by simpa [oneStepB] using hs)

theorem holds_of_chainB (h : pkb.pWellFormed = true) {p : Pid} (hp : pkb.isTransB p = true)
    {s o : Qid} (hs : pkb.chainB p s o = true) : pkb.toLayer.Holds p s o := by
  have htr : pkb.toLayer.IsTransitive p := by simpa [toLayer, isTransB] using hp
  simp only [chainB, decide_eq_true_eq] at hs
  obtain ⟨m, hm, hmo⟩ := hs
  have hreach : Relation.ReflTransGen (fun u v => v ∈ pkb.stepPairs p u) m o :=
    (mem_reach_stepPairs_iff h p m o).1 hmo
  have key : ∀ {x y : Qid}, Relation.ReflTransGen (fun u v => v ∈ pkb.stepPairs p u) x y →
      pkb.toLayer.Holds p s x → pkb.toLayer.Holds p s y := by
    intro x y hxy
    induction hxy with
    | refl => exact fun hh => hh
    | tail _ hbc ih => exact fun hsx =>
        PropertyLayer.Holds.trans htr (ih hsx) (holds_of_mem_stepPairs h hbc)
  exact key hreach (holds_of_mem_stepPairs h hm)

/-- **Soundness**: every statement computed by the engine is derivable in the
abstract property layer. -/
theorem holds_of_relatedB (h : pkb.pWellFormed = true) {p : Pid} {s o : Qid}
    (hs : pkb.relatedB p s o = true) : pkb.toLayer.Holds p s o := by
  by_cases hp : pkb.isTransB p = true
  · rw [relatedB, if_pos hp] at hs; exact holds_of_chainB h hp hs
  · rw [relatedB, if_neg hp] at hs; exact holds_of_oneStepB h hs

/-! ### Completeness

For a property layer without symmetry and inverse declarations, in which
transitivity is inherited upwards along the property hierarchy, the engine
computes *exactly* the derivable statements. -/

theorem supportsB_of_mem_basePairsL (hsym : pkb.symProps = []) (hinv : pkb.inverses = [])
    {p : Pid} {s o : Qid} (hs : (s, o) ∈ pkb.basePairsL p) : pkb.supportsB p s o = true := by
  rcases mem_basePairsL_iff.1 hs with h1 | ⟨hsymp, h2⟩ | ⟨q, r, hr, hmem, hqr, hrp⟩
  · exact h1
  · simp [isSymB, hsym] at hsymp
  · simp [inverseOfB, hinv] at hrp

theorem basePairsL_mono (h : pkb.pWellFormed = true) {p q : Pid}
    (hpq : pkb.toLayer.SubPropertyOf p q) (hsym : pkb.symProps = []) (hinv : pkb.inverses = [])
    {s o : Qid} (hs : (s, o) ∈ pkb.basePairsL p) : (s, o) ∈ pkb.basePairsL q := by
  obtain ⟨r, hmem, hsub⟩ := supportsB_iff.1 (supportsB_of_mem_basePairsL hsym hinv hs)
  refine mem_basePairsL_iff.2 (Or.inl (supportsB_iff.2 ⟨r, hmem, ?_⟩))
  exact (isSubPropertyOf_iff h r q).2
    (PropertyLayer.subPropertyOf_trans ((isSubPropertyOf_iff h r p).1 hsub) hpq)

theorem relatedB_of_mem_basePairsL {p : Pid} {s o : Qid} (hs : (s, o) ∈ pkb.basePairsL p) :
    pkb.relatedB p s o = true := by
  by_cases hp : pkb.isTransB p = true
  · rw [relatedB, if_pos hp]
    exact decide_eq_true ⟨o, mem_stepPairs_iff.2 hs, Reach.mem_reach_self _ _ _⟩
  · rw [relatedB, if_neg hp]
    simpa [oneStepB] using mem_stepPairs_iff.2 hs

theorem mem_basePairsL_of_relatedB_of_not_trans {p : Pid} (hp : pkb.isTransB p = false)
    {s o : Qid} (hs : pkb.relatedB p s o = true) : (s, o) ∈ pkb.basePairsL p := by
  rw [relatedB, if_neg (by simp [hp])] at hs
  exact mem_stepPairs_iff.1 (by simpa [oneStepB] using hs)

theorem chainB_trans (h : pkb.pWellFormed = true) {p : Pid} {a b c : Qid}
    (hab : pkb.chainB p a b = true) (hbc : pkb.chainB p b c = true) :
    pkb.chainB p a c = true := by
  simp only [chainB, decide_eq_true_eq] at hab hbc ⊢
  obtain ⟨m, hm, hmb⟩ := hab
  obtain ⟨n, hn, hnc⟩ := hbc
  refine ⟨m, hm, (mem_reach_stepPairs_iff h p m c).2 ?_⟩
  exact ((mem_reach_stepPairs_iff h p m b).1 hmb).trans
    (Relation.ReflTransGen.head hn ((mem_reach_stepPairs_iff h p n c).1 hnc))

/-- **Completeness**: for a layer with no symmetry and no inverse declarations, in
which transitivity declarations are inherited upwards, every derivable statement is
computed by the engine. -/
theorem relatedB_of_holds (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) {p : Pid} {s o : Qid}
    (hs : pkb.toLayer.Holds p s o) : pkb.relatedB p s o = true := by
  induction hs with
  | @stmt p s o hst =>
      refine relatedB_of_mem_basePairsL (mem_basePairsL_iff.2 (Or.inl ?_))
      exact supportsB_iff.2 ⟨p, hst, isSubPropertyOf_refl pkb p⟩
  | @sub p q s o hpq _ ih =>
      have hmono : ∀ {x y : Qid}, y ∈ pkb.stepPairs p x → y ∈ pkb.stepPairs q x := by
        intro x y hxy
        exact mem_stepPairs_iff.2 (basePairsL_mono h
          (PropertyLayer.subPropertyOf_of_subProp hpq) hsym hinv (mem_stepPairs_iff.1 hxy))
      by_cases hp : pkb.isTransB p = true
      · have hq : pkb.isTransB q = true := by
          simp only [transUpwardClosed, List.all_eq_true, Bool.or_eq_true,
            Bool.not_eq_true'] at hup
          rcases hup (p, q) hpq with hfalse | hok
          · rw [hp] at hfalse; exact absurd hfalse (by simp)
          · exact hok
        rw [relatedB, if_pos hp] at ih
        rw [relatedB, if_pos hq]
        simp only [chainB, decide_eq_true_eq] at ih ⊢
        obtain ⟨m, hm, hmo⟩ := ih
        refine ⟨m, hmono hm, (mem_reach_stepPairs_iff h q m o).2 ?_⟩
        exact ((mem_reach_stepPairs_iff h p m o).1 hmo).mono fun _ _ hxy => hmono hxy
      · simp only [Bool.not_eq_true] at hp
        exact relatedB_of_mem_basePairsL (basePairsL_mono h
          (PropertyLayer.subPropertyOf_of_subProp hpq) hsym hinv
          (mem_basePairsL_of_relatedB_of_not_trans hp ih))
  | @trans p a b c htr _ _ ih1 ih2 =>
      have hp : pkb.isTransB p = true := by simpa [isTransB] using htr
      rw [relatedB, if_pos hp] at ih1 ih2 ⊢
      exact chainB_trans h ih1 ih2
  | @symm p s o hsymm _ _ => simp [toLayer, hsym] at hsymm
  | @inv p q s o hinvpq _ _ => rcases hinvpq with hmem | hmem <;> simp [hinv] at hmem

/-- The engine decides derivability exactly, under the hypotheses of
`PKB.relatedB_of_holds`. -/
theorem relatedB_iff_holds (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) (p : Pid) (s o : Qid) :
    pkb.relatedB p s o = true ↔ pkb.toLayer.Holds p s o :=
  ⟨holds_of_relatedB h, relatedB_of_holds h hsym hinv hup⟩

/-! ### Constraints -/

theorem pvalid_base (h : pkb.pvalid = true) : pkb.base.valid = true := by
  simp only [pvalid, Bool.and_eq_true] at h; tauto

theorem pvalid_pWellFormed (h : pkb.pvalid = true) : pkb.pWellFormed = true := by
  simp only [pvalid, Bool.and_eq_true] at h; tauto

theorem pvalid_typeConstraintsOk (h : pkb.pvalid = true) : pkb.typeConstraintsOk = true := by
  simp only [pvalid, Bool.and_eq_true] at h; tauto

theorem pvalid_valueTypeConstraintsOk (h : pkb.pvalid = true) :
    pkb.valueTypeConstraintsOk = true := by
  simp only [pvalid, Bool.and_eq_true] at h; tauto

/-- A validated knowledge base satisfies its type constraints on every statement the
engine supports. -/
theorem instanceOf_of_typeC (h : pkb.typeConstraintsOk = true) {p : Pid} {c : Qid}
    (hc : (p, c) ∈ pkb.typeC) {s o : Qid} (hs : pkb.supportsB p s o = true) :
    pkb.base.isInstanceOf s c = true := by
  obtain ⟨q, hmem, hsub⟩ := supportsB_iff.1 hs
  simp only [typeConstraintsOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h (p, c) hc (q, s, o) hmem with hfalse | hok
  · rw [hsub] at hfalse; exact absurd hfalse (by simp)
  · exact hok

/-- ... and its value-type constraints. -/
theorem instanceOf_of_valueTypeC (h : pkb.valueTypeConstraintsOk = true) {p : Pid} {c : Qid}
    (hc : (p, c) ∈ pkb.valueTypeC) {s o : Qid} (hs : pkb.supportsB p s o = true) :
    pkb.base.isInstanceOf o c = true := by
  obtain ⟨q, hmem, hsub⟩ := supportsB_iff.1 hs
  simp only [valueTypeConstraintsOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h (p, c) hc (q, s, o) hmem with hfalse | hok
  · rw [hsub] at hfalse; exact absurd hfalse (by simp)
  · exact hok

/-! ### Constraints in the abstract model

For a layer with no symmetry and no inverse declarations, a validated property
knowledge base satisfies the abstract constraint predicates of
`RequestProject.Properties`, so all the constraint theorems proved there apply to
it. -/

theorem exists_supportsB_subject (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) {p : Pid} {s o : Qid} (hr : pkb.relatedB p s o = true) :
    ∃ o', pkb.supportsB p s o' = true := by
  by_cases hp : pkb.isTransB p = true
  · rw [relatedB, if_pos hp] at hr
    simp only [chainB, decide_eq_true_eq] at hr
    obtain ⟨m, hm, -⟩ := hr
    exact ⟨m, supportsB_of_mem_basePairsL hsym hinv (mem_stepPairs_iff.1 hm)⟩
  · simp only [Bool.not_eq_true] at hp
    exact ⟨o, supportsB_of_mem_basePairsL hsym hinv
      (mem_basePairsL_of_relatedB_of_not_trans hp hr)⟩

theorem exists_supportsB_value (h : pkb.pWellFormed = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) {p : Pid} {s o : Qid} (hr : pkb.relatedB p s o = true) :
    ∃ s', pkb.supportsB p s' o = true := by
  by_cases hp : pkb.isTransB p = true
  · rw [relatedB, if_pos hp] at hr
    simp only [chainB, decide_eq_true_eq] at hr
    obtain ⟨m, hm, hmo⟩ := hr
    have key : ∀ {x y : Qid}, Relation.ReflTransGen (fun u v => v ∈ pkb.stepPairs p u) x y →
        (∃ s', pkb.supportsB p s' x = true) → ∃ s', pkb.supportsB p s' y = true := by
      intro x y hxy
      induction hxy with
      | refl => exact fun hh => hh
      | tail _ hbc _ => exact fun _ =>
          ⟨_, supportsB_of_mem_basePairsL hsym hinv (mem_stepPairs_iff.1 hbc)⟩
    exact key ((mem_reach_stepPairs_iff h p m o).1 hmo)
      ⟨s, supportsB_of_mem_basePairsL hsym hinv (mem_stepPairs_iff.1 hm)⟩
  · simp only [Bool.not_eq_true] at hp
    exact ⟨s, supportsB_of_mem_basePairsL hsym hinv
      (mem_basePairsL_of_relatedB_of_not_trans hp hr)⟩

/-- A validated property knowledge base satisfies its type constraints in the
abstract model. -/
theorem subjectTypeOk_of_pvalid (hv : pkb.pvalid = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) :
    PropertyLayer.Constraints.SubjectTypeOk (pkb.base.toOntology (pvalid_base hv))
      pkb.toLayer pkb.toConstraints := by
  intro p c s o hc hholds
  have hwf := pvalid_pWellFormed hv
  obtain ⟨o', hsup⟩ :=
    exists_supportsB_subject hsym hinv (relatedB_of_holds hwf hsym hinv hup hholds)
  exact (KB.isInstanceOf_iff_instanceOf (pvalid_base hv) s c).1
    (instanceOf_of_typeC (pvalid_typeConstraintsOk hv) hc hsup)

/-- A validated property knowledge base satisfies its value-type constraints in the
abstract model. -/
theorem valueTypeOk_of_pvalid (hv : pkb.pvalid = true) (hsym : pkb.symProps = [])
    (hinv : pkb.inverses = []) (hup : pkb.transUpwardClosed = true) :
    PropertyLayer.Constraints.ValueTypeOk (pkb.base.toOntology (pvalid_base hv))
      pkb.toLayer pkb.toConstraints := by
  intro p c s o hc hholds
  have hwf := pvalid_pWellFormed hv
  obtain ⟨s', hsup⟩ :=
    exists_supportsB_value hwf hsym hinv (relatedB_of_holds hwf hsym hinv hup hholds)
  exact (KB.isInstanceOf_iff_instanceOf (pvalid_base hv) o c).1
    (instanceOf_of_valueTypeC (pvalid_valueTypeConstraintsOk hv) hc hsup)

end PKB

end Wikidata
