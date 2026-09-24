import RequestProject.Wikidata.Reachability

/-!
# A small executable model of the Wikidata data model

Items (`Qid`), properties (`Pid`), ranked statements and knowledge bases, with

* the *truthy* projection (preferred statements, or normal statements when no
  preferred statement exists, never deprecated statements);
* the executable subclass (`P279`) and instance (`P31`) engines;
* exactness theorems relating each executable checker to its declarative
  relation (`isSubclassOf_iff`, `isInstanceOf_iff`).

The truthy projection is a *query* semantics on the data model.  It is
deliberately kept separate from the evidence semantics in
`RequestProject.Epistemic.*`: see `truthy_isNot_epistemic_truth` there.
-/

namespace Wikidata

/-- A Wikidata item identifier, e.g. `Q42`. -/
structure Qid where
  num : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A Wikidata property identifier, e.g. `P31`. -/
structure Pid where
  num : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Statement rank. -/
inductive Rank
  | deprecated
  | normal
  | preferred
  deriving DecidableEq, Repr, Inhabited

/-- An item-valued statement. -/
structure Statement where
  subject : Qid
  property : Pid
  value : Qid
  rank : Rank := Rank.normal
  deriving DecidableEq, Repr, Inhabited

/-- A knowledge base: a list of known entities together with a list of statements. -/
structure KB where
  entities : List Qid
  statements : List Statement
  deriving Repr, Inhabited

/-- `P31`, "instance of". -/
def P31 : Pid := ⟨31⟩
/-- `P279`, "subclass of". -/
def P279 : Pid := ⟨279⟩
/-- `P2737`, "union of". -/
def P2737 : Pid := ⟨2737⟩
/-- `P2738`, "disjoint union of". -/
def P2738 : Pid := ⟨2738⟩

/-! ## Ranks and the truthy projection -/

/-- All statements of `kb` with the given subject and property. -/
def statementsFor (kb : KB) (s : Qid) (p : Pid) : List Statement :=
  kb.statements.filter (fun st => st.subject = s ∧ st.property = p)

/-- Does the subject/property pair carry a preferred statement? -/
def hasPreferred (kb : KB) (s : Qid) (p : Pid) : Bool :=
  (statementsFor kb s p).any (fun st => st.rank = Rank.preferred)

/-- The truthy projection: a statement is truthy when it is preferred, or normal
in the absence of any preferred statement for the same subject and property.
Deprecated statements are never truthy. -/
def IsTruthy (kb : KB) (st : Statement) : Bool :=
  (st.rank = Rank.preferred) ||
    ((st.rank = Rank.normal) && !hasPreferred kb st.subject st.property)

@[simp] theorem isTruthy_deprecated (kb : KB) (st : Statement) (h : st.rank = Rank.deprecated) :
    IsTruthy kb st = false := by
  simp [IsTruthy, h]

theorem isTruthy_preferred (kb : KB) (st : Statement) (h : st.rank = Rank.preferred) :
    IsTruthy kb st = true := by
  simp [IsTruthy, h]

/-- If some preferred statement exists for a subject/property pair, no normal
statement of that pair is truthy. -/
theorem not_truthy_normal_of_hasPreferred (kb : KB) (st : Statement)
    (hst : st.rank = Rank.normal) (h : hasPreferred kb st.subject st.property = true) :
    IsTruthy kb st = false := by
  simp [IsTruthy, hst, h]

/-- With no preferred statement present, every normal statement is truthy. -/
theorem isTruthy_normal_of_not_hasPreferred (kb : KB) (st : Statement)
    (hst : st.rank = Rank.normal) (h : hasPreferred kb st.subject st.property = false) :
    IsTruthy kb st = true := by
  simp [IsTruthy, hst, h]

/-! ## The subclass engine -/

/-- The truthy `P279` edges of the knowledge base. -/
def subclassEdges (kb : KB) : List (Qid × Qid) :=
  (kb.statements.filter (fun st => st.property = P279 ∧ IsTruthy kb st = true)).map
    (fun st => (st.subject, st.value))

/-- Direct superclasses of a class. -/
def superclasses (kb : KB) (a : Qid) : List Qid :=
  (subclassEdges kb).filterMap (fun e => if e.1 = a then some e.2 else none)

theorem mem_superclasses_iff (kb : KB) (a b : Qid) :
    b ∈ superclasses kb a ↔ (a, b) ∈ subclassEdges kb := by
  constructor
  · intro h
    simp only [superclasses, List.mem_filterMap] at h
    obtain ⟨e, he, heq⟩ := h
    by_cases h1 : e.1 = a
    · simp only [h1] at heq
      have : e = (a, b) := by
        cases e with
        | mk x y => simp_all
      exact this ▸ he
    · simp [h1] at heq
  · intro h
    simp only [superclasses, List.mem_filterMap]
    exact ⟨(a, b), h, by simp⟩

/-- The declarative direct-subclass relation. -/
def DirectSubclass (kb : KB) (a b : Qid) : Prop := (a, b) ∈ subclassEdges kb

instance (kb : KB) (a b : Qid) : Decidable (DirectSubclass kb a b) :=
  inferInstanceAs (Decidable ((a, b) ∈ subclassEdges kb))

/-- The declarative subclass relation: the reflexive transitive closure of the
truthy `P279` edges. -/
def SubclassOf (kb : KB) (a b : Qid) : Prop :=
  Relation.ReflTransGen (DirectSubclass kb) a b

/-- The executable subclass checker. -/
def isSubclassOf (kb : KB) (a b : Qid) : Bool :=
  Wikidata.Reach.reachIn (superclasses kb) (subclassEdges kb).length a b

theorem step_iff_directSubclass (kb : KB) (a b : Qid) :
    Wikidata.Reach.Step (superclasses kb) a b ↔ DirectSubclass kb a b :=
  mem_superclasses_iff kb a b

/-- **Exactness of the subclass engine.** -/
theorem isSubclassOf_iff (kb : KB) (a b : Qid) :
    isSubclassOf kb a b = true ↔ SubclassOf kb a b := by
  have hstep : Wikidata.Reach.Step (superclasses kb) = DirectSubclass kb := by
    funext x y
    exact propext (step_iff_directSubclass kb x y)
  have hlen : ((subclassEdges kb).map Prod.snd).length = (subclassEdges kb).length := by
    simp
  have := Wikidata.Reach.reachIn_iff (succ := superclasses kb)
    (objs := (subclassEdges kb).map Prod.snd)
    (by
      intro x y hy
      rw [mem_superclasses_iff] at hy
      exact List.mem_map.2 ⟨(x, y), hy, rfl⟩) a b
  rw [hlen] at this
  rw [isSubclassOf, this, hstep]
  rfl

theorem subclassOf_refl (kb : KB) (a : Qid) : SubclassOf kb a a :=
  Relation.ReflTransGen.refl

theorem subclassOf_trans {kb : KB} {a b c : Qid} (h₁ : SubclassOf kb a b)
    (h₂ : SubclassOf kb b c) : SubclassOf kb a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem subclassOf_of_direct {kb : KB} {a b : Qid} (h : DirectSubclass kb a b) :
    SubclassOf kb a b :=
  Relation.ReflTransGen.single h

instance (kb : KB) (a b : Qid) : Decidable (SubclassOf kb a b) :=
  decidable_of_iff _ (isSubclassOf_iff kb a b)

/-! ## The instance engine -/

/-- The truthy `P31` edges of the knowledge base. -/
def instanceEdges (kb : KB) : List (Qid × Qid) :=
  (kb.statements.filter (fun st => st.property = P31 ∧ IsTruthy kb st = true)).map
    (fun st => (st.subject, st.value))

/-- The declarative instance relation: an asserted type together with subclass
closure. -/
def InstanceOf (kb : KB) (x c : Qid) : Prop :=
  ∃ c₀, (x, c₀) ∈ instanceEdges kb ∧ SubclassOf kb c₀ c

/-- The executable instance checker. -/
def isInstanceOf (kb : KB) (x c : Qid) : Bool :=
  (instanceEdges kb).any (fun e => e.1 = x ∧ isSubclassOf kb e.2 c)

/-- **Exactness of the instance engine.** -/
theorem isInstanceOf_iff (kb : KB) (x c : Qid) :
    isInstanceOf kb x c = true ↔ InstanceOf kb x c := by
  simp only [isInstanceOf, List.any_eq_true, decide_eq_true_eq, InstanceOf]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    refine ⟨e.2, ?_, (isSubclassOf_iff kb e.2 c).1 (by simpa using h2)⟩
    have : e = (x, e.2) := by
      cases e with
      | mk a b => simp_all
    exact this ▸ he
  · rintro ⟨c₀, hc₀, hsub⟩
    exact ⟨(x, c₀), hc₀, by simp, by simpa using (isSubclassOf_iff kb c₀ c).2 hsub⟩

instance (kb : KB) (x c : Qid) : Decidable (InstanceOf kb x c) :=
  decidable_of_iff _ (isInstanceOf_iff kb x c)

theorem instanceOf_of_subclassOf {kb : KB} {x c d : Qid} (h : InstanceOf kb x c)
    (hcd : SubclassOf kb c d) : InstanceOf kb x d := by
  obtain ⟨c₀, hc₀, hsub⟩ := h
  exact ⟨c₀, hc₀, subclassOf_trans hsub hcd⟩

end Wikidata
