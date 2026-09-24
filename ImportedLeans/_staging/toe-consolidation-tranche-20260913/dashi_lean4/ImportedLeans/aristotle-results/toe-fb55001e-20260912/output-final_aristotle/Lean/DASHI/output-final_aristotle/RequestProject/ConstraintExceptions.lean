import RequestProject.StatementConstraints

/-!
# Constraint exceptions, status and scope

Every Wikidata property constraint carries administrative qualifiers that say
*how seriously* it is meant and *where* it applies:

* **exception to constraint** (P2303): a list of items that are explicitly
  exempted — the constraint is not expected to hold of them;
* **constraint status** (P2316): *mandatory* (Q21502408) or, by default, a mere
  *suggestion* (Q62026391); only a mandatory constraint counts as an error;
* **constraint scope** (P4680): whether the constraint applies to the main value
  of a statement, to its qualifiers, or to its references.

The constraint files of this development check constraints as if they were
absolute.  This file adds the three qualifiers, abstractly on
`Wikidata.PropertyLayer` and executably on lists of statements.

* `Wikidata.PropertyLayer.Satisfies` / `SatisfiesUpTo` — a statement-level
  requirement, without and with exceptions.  Proved: with no exceptions the two
  agree; adding exceptions only weakens; exceptions weaken *exactly* at the
  listed items (`satisfiesUpTo_iff_satisfies_or_exception`); requirements are
  inherited by subproperties and combine conjunctively.
* `Wikidata.PropertyLayer.Violators` — the items that really break the
  requirement.  Main theorem `satisfiesUpTo_iff_violators_subset`: a constraint
  with exceptions holds precisely when every violator is listed, so `Violators`
  is the *smallest* admissible exception list and any exception outside it is
  redundant (`satisfiesUpTo_inter_violators`).
* `Wikidata.ConstraintDecl` — a declared constraint with its exceptions and its
  status, and the resulting errors and warnings.  Proved: a satisfied constraint
  raises nothing; a suggestion is never an error; demoting a mandatory constraint
  to a suggestion removes its error, and errors are exactly the unlisted
  violators of a mandatory constraint.
* `Wikidata.Scope` and `Wikidata.PropertyLayer.SatisfiesScoped` — checking a
  requirement only in the declared scopes.  Proved: the check over a union of
  scopes is the conjunction of the checks, enlarging the scope strengthens the
  constraint, and the default main-value scope says nothing about qualifiers.
* `Wikidata.exceptionalViolations` — the executable checker over a finite list of
  statements: it returns the violating statements that are not excepted, is empty
  exactly when the requirement holds of the listed statements, and, for a layer
  whose derived statements are all listed, implies the abstract constraint.

The worked fragment is the `sex or gender` (P21) one-of constraint with an
exception item: it passes with the exception declared, fails without it, and the
same violation is an error when the constraint is mandatory and only a warning
when it is a suggestion.
-/

namespace Wikidata

namespace PropertyLayer

variable {I P : Type*} {L : PropertyLayer I P}

/-! ### Requirements with exceptions -/

/-- A statement-level requirement on a property: every derived `p`-statement
satisfies `ok`. -/
def Satisfies (L : PropertyLayer I P) (p : P) (ok : I → I → Prop) : Prop :=
  ∀ {s o : I}, L.Holds p s o → ok s o

/-- The same requirement with an **exception to constraint** (P2303) list `E`:
statements whose subject is exempted are not checked. -/
def SatisfiesUpTo (L : PropertyLayer I P) (p : P) (ok : I → I → Prop) (E : Set I) : Prop :=
  ∀ {s o : I}, L.Holds p s o → s ∉ E → ok s o

/-- With no exceptions, the two notions agree. -/
theorem satisfiesUpTo_empty_iff {p : P} {ok : I → I → Prop} :
    L.SatisfiesUpTo p ok ∅ ↔ L.Satisfies p ok := by
  constructor
  · intro h s o hs; exact h hs (by simp)
  · intro h s o hs _; exact h hs

/-- An absolute requirement holds up to any exception list. -/
theorem satisfiesUpTo_of_satisfies {p : P} {ok : I → I → Prop} (h : L.Satisfies p ok)
    (E : Set I) : L.SatisfiesUpTo p ok E := fun hs _ => h hs

/-- Declaring more exceptions only weakens a constraint. -/
theorem satisfiesUpTo_mono {p : P} {ok : I → I → Prop} {E E' : Set I} (hE : E ⊆ E')
    (h : L.SatisfiesUpTo p ok E) : L.SatisfiesUpTo p ok E' :=
  fun hs hne => h hs (fun hmem => hne (hE hmem))

/-- Exempting everything makes a constraint vacuous. -/
theorem satisfiesUpTo_univ {p : P} {ok : I → I → Prop} :
    L.SatisfiesUpTo p ok Set.univ := fun _ hne => absurd (Set.mem_univ _) hne

/-- Exceptions weaken a requirement exactly at the listed items: the constraint
with exceptions is the plain constraint whose condition is relaxed to "either the
subject is an exception, or the requirement holds". -/
theorem satisfiesUpTo_iff_satisfies_or_exception {p : P} {ok : I → I → Prop} {E : Set I} :
    L.SatisfiesUpTo p ok E ↔ L.Satisfies p (fun s o => s ∈ E ∨ ok s o) := by
  constructor
  · intro h s o hs
    by_cases hmem : s ∈ E
    · exact Or.inl hmem
    · exact Or.inr (h hs hmem)
  · intro h s o hs hne
    exact (h hs).resolve_left hne

/-- A requirement of a property is a requirement of each of its subproperties,
with the same exceptions. -/
theorem SatisfiesUpTo.of_subPropertyOf {p p' : P} {ok : I → I → Prop} {E : Set I}
    (h : L.SatisfiesUpTo p ok E) (hp : L.SubPropertyOf p' p) : L.SatisfiesUpTo p' ok E :=
  fun hs hne => h (holds_of_subPropertyOf hp hs) hne

/-- Two requirements on the same property combine, the exceptions being pooled. -/
theorem SatisfiesUpTo.and {p : P} {ok ok' : I → I → Prop} {E E' : Set I}
    (h : L.SatisfiesUpTo p ok E) (h' : L.SatisfiesUpTo p ok' E') :
    L.SatisfiesUpTo p (fun s o => ok s o ∧ ok' s o) (E ∪ E') :=
  fun hs hne =>
    ⟨h hs (fun hm => hne (Or.inl hm)), h' hs (fun hm => hne (Or.inr hm))⟩

/-- A weaker requirement is implied by a stronger one. -/
theorem SatisfiesUpTo.imp {p : P} {ok ok' : I → I → Prop} {E : Set I}
    (h : L.SatisfiesUpTo p ok E) (himp : ∀ s o, ok s o → ok' s o) :
    L.SatisfiesUpTo p ok' E := fun hs hne => himp _ _ (h hs hne)

/-! ### Violators: the smallest admissible exception list -/

/-- The items that really break a requirement: those with a `p`-statement
violating `ok`. -/
def Violators (L : PropertyLayer I P) (p : P) (ok : I → I → Prop) : Set I :=
  {s | ∃ o, L.Holds p s o ∧ ¬ ok s o}

/-- A constraint with exceptions holds exactly when every violator is listed as
an exception. -/
theorem satisfiesUpTo_iff_violators_subset {p : P} {ok : I → I → Prop} {E : Set I} :
    L.SatisfiesUpTo p ok E ↔ L.Violators p ok ⊆ E := by
  constructor
  · rintro h s ⟨o, ho, hno⟩
    by_contra hmem
    exact hno (h ho hmem)
  · intro h s o hs hne
    by_contra hno
    exact hne (h ⟨o, hs, hno⟩)

/-- Consequently the violators are themselves an admissible exception list, and
the smallest one. -/
theorem satisfiesUpTo_violators {p : P} {ok : I → I → Prop} :
    L.SatisfiesUpTo p ok (L.Violators p ok) :=
  satisfiesUpTo_iff_violators_subset.2 (subset_refl _)

/-- An exception that is not a violator is redundant: only the exceptions that do
break the requirement matter. -/
theorem satisfiesUpTo_inter_violators {p : P} {ok : I → I → Prop} {E : Set I} :
    L.SatisfiesUpTo p ok E ↔ L.SatisfiesUpTo p ok (E ∩ L.Violators p ok) := by
  rw [satisfiesUpTo_iff_violators_subset, satisfiesUpTo_iff_violators_subset]
  constructor
  · exact fun h s hs => ⟨h hs, hs⟩
  · exact fun h s hs => (h hs).1

/-- No violators is the same as the absolute constraint. -/
theorem violators_eq_empty_iff {p : P} {ok : I → I → Prop} :
    L.Violators p ok = ∅ ↔ L.Satisfies p ok := by
  rw [← satisfiesUpTo_empty_iff, satisfiesUpTo_iff_violators_subset,
    Set.subset_empty_iff]

end PropertyLayer

/-! ### Constraint status -/

/-- The **constraint status** (P2316): a constraint is either *mandatory*
(Q21502408) or a *suggestion* (Q62026391, the default). -/
inductive ConstraintStatus
  /-- Q21502408: violations are errors. -/
  | mandatory
  /-- Q62026391: violations are only warnings. -/
  | suggestion
deriving DecidableEq, Repr, Inhabited

/-- A declared property constraint: the property, the requirement it imposes, its
`exception to constraint` (P2303) list and its `constraint status` (P2316). -/
structure ConstraintDecl (I P : Type*) where
  /-- The constrained property. -/
  prop : P
  /-- The requirement on `⟨subject, value⟩` pairs. -/
  ok : I → I → Prop
  /-- The exempted items. -/
  exceptions : Set I := ∅
  /-- Mandatory, or a mere suggestion. -/
  status : ConstraintStatus := .suggestion

namespace ConstraintDecl

variable {I P : Type*} {L : PropertyLayer I P} (C : ConstraintDecl I P)

/-- The constraint holds in a layer when the requirement holds up to its
exceptions. -/
def Holds (C : ConstraintDecl I P) (L : PropertyLayer I P) : Prop :=
  L.SatisfiesUpTo C.prop C.ok C.exceptions

/-- A violated mandatory constraint is an *error*. -/
def IsError (C : ConstraintDecl I P) (L : PropertyLayer I P) : Prop :=
  C.status = .mandatory ∧ ¬ C.Holds L

/-- A violated suggestion is only a *warning*. -/
def IsWarning (C : ConstraintDecl I P) (L : PropertyLayer I P) : Prop :=
  C.status = .suggestion ∧ ¬ C.Holds L

/-- A constraint that holds raises neither an error nor a warning. -/
theorem not_error_of_holds (h : C.Holds L) : ¬ C.IsError L := fun he => he.2 h

theorem not_warning_of_holds (h : C.Holds L) : ¬ C.IsWarning L := fun hw => hw.2 h

/-- Errors and warnings are mutually exclusive. -/
theorem not_error_and_warning : ¬ (C.IsError L ∧ C.IsWarning L) := by
  rintro ⟨⟨h, -⟩, ⟨h', -⟩⟩
  rw [h] at h'
  exact absurd h' (by decide)

/-- A suggestion is never an error. -/
theorem suggestion_not_error (h : C.status = .suggestion) : ¬ C.IsError L := by
  rintro ⟨h', -⟩
  rw [h] at h'
  exact absurd h' (by decide)

/-- Demoting a mandatory constraint to a suggestion removes its error. -/
theorem not_error_of_demoted : ¬ ({C with status := .suggestion} : ConstraintDecl I P).IsError L :=
  suggestion_not_error _ rfl

/-- A violated constraint is an error or a warning according to its status. -/
theorem error_or_warning (h : ¬ C.Holds L) : C.IsError L ∨ C.IsWarning L := by
  cases hst : C.status
  · exact Or.inl ⟨hst, h⟩
  · exact Or.inr ⟨hst, h⟩

/-- Errors are exactly the unlisted violators of a mandatory constraint. -/
theorem isError_iff (h : C.status = .mandatory) :
    C.IsError L ↔ ¬ (L.Violators C.prop C.ok ⊆ C.exceptions) := by
  simp only [IsError, h, true_and, Holds, PropertyLayer.satisfiesUpTo_iff_violators_subset]

/-- Adding the missing exceptions always silences a constraint. -/
theorem holds_of_exceptions_violators
    (h : L.Violators C.prop C.ok ⊆ C.exceptions) : C.Holds L :=
  PropertyLayer.satisfiesUpTo_iff_violators_subset.2 h

end ConstraintDecl

/-! ### Constraint scope -/

/-- The **constraint scope** (P4680): where a constraint is checked. -/
inductive Scope
  /-- The main value of a statement (Q46466787). -/
  | mainValue
  /-- The qualifiers of a statement (Q46466783). -/
  | qualifier
  /-- The references of a statement (Q46466805). -/
  | reference
deriving DecidableEq, Repr, Inhabited

namespace PropertyLayer

variable {I P : Type*}

/-- A requirement checked only in the declared scopes, where `St sc s o` records
the `⟨subject, value⟩` pairs occurring in scope `sc`. -/
def SatisfiesScoped (St : Scope → I → I → Prop) (S : Set Scope) (ok : I → I → Prop)
    (E : Set I) : Prop :=
  ∀ ⦃sc : Scope⦄, sc ∈ S → ∀ ⦃s o : I⦄, St sc s o → s ∉ E → ok s o

/-- Checking over a union of scopes is checking over each. -/
theorem satisfiesScoped_union {St : Scope → I → I → Prop} {S S' : Set Scope}
    {ok : I → I → Prop} {E : Set I} :
    SatisfiesScoped St (S ∪ S') ok E ↔
      SatisfiesScoped St S ok E ∧ SatisfiesScoped St S' ok E := by
  constructor
  · intro h
    exact ⟨fun sc hsc => h (Or.inl hsc), fun sc hsc => h (Or.inr hsc)⟩
  · rintro ⟨h, h'⟩ sc (hsc | hsc)
    · exact h hsc
    · exact h' hsc

/-- Enlarging the scope strengthens the constraint. -/
theorem satisfiesScoped_mono {St : Scope → I → I → Prop} {S S' : Set Scope}
    {ok : I → I → Prop} {E : Set I} (hS : S ⊆ S') (h : SatisfiesScoped St S' ok E) :
    SatisfiesScoped St S ok E := fun _ hsc => h (hS hsc)

/-- An empty scope imposes nothing. -/
theorem satisfiesScoped_empty {St : Scope → I → I → Prop} {ok : I → I → Prop}
    {E : Set I} : SatisfiesScoped St ∅ ok E := fun _ hsc => absurd hsc (by simp)

/-- The single-scope check is the plain requirement on the statements of that
scope. -/
theorem satisfiesScoped_singleton {St : Scope → I → I → Prop} {sc : Scope}
    {ok : I → I → Prop} {E : Set I} :
    SatisfiesScoped St {sc} ok E ↔ ∀ ⦃s o : I⦄, St sc s o → s ∉ E → ok s o := by
  constructor
  · intro h s o hst hne; exact h rfl hst hne
  · rintro h sc' rfl s o hst hne; exact h hst hne

end PropertyLayer

/-! ### The executable checker -/

/-- The violating statements of a finite list that are not exempted by the
`exception to constraint` list. -/
def exceptionalViolations (stmts : List (Qid × Qid)) (ok : Qid → Qid → Bool)
    (exc : List Qid) : List (Qid × Qid) :=
  stmts.filter (fun st => !ok st.1 st.2 && !exc.contains st.1)

/-- The checker reports nothing exactly when every listed statement either has an
exempted subject or meets the requirement. -/
theorem exceptionalViolations_eq_nil_iff (stmts : List (Qid × Qid)) (ok : Qid → Qid → Bool)
    (exc : List Qid) :
    exceptionalViolations stmts ok exc = [] ↔
      ∀ st ∈ stmts, st.1 ∈ exc ∨ ok st.1 st.2 = true := by
  rw [exceptionalViolations, List.filter_eq_nil_iff]
  constructor
  · intro h st hst
    have hth := h st hst
    revert hth
    cases hok : ok st.1 st.2 <;> cases hmem : decide (st.1 ∈ exc) <;> simp_all
  · intro h st hst
    rcases h st hst with hmem | hok
    · simp [hmem]
    · simp [hok]

/-- Every statement the checker reports really is a violation with an unexempted
subject. -/
theorem mem_exceptionalViolations_iff {stmts : List (Qid × Qid)} {ok : Qid → Qid → Bool}
    {exc : List Qid} {st : Qid × Qid} :
    st ∈ exceptionalViolations stmts ok exc ↔
      st ∈ stmts ∧ ok st.1 st.2 = false ∧ st.1 ∉ exc := by
  simp [exceptionalViolations, List.mem_filter]

/-- Soundness against the abstract constraint: if all derived statements of the
property are listed, an empty report means the constraint holds up to its
exceptions. -/
theorem satisfiesUpTo_of_exceptionalViolations_eq_nil {P : Type*} {L : PropertyLayer Qid P}
    {p : P} {stmts : List (Qid × Qid)} {ok : Qid → Qid → Bool} {exc : List Qid}
    (hcomplete : ∀ s o, L.Holds p s o → (s, o) ∈ stmts)
    (h : exceptionalViolations stmts ok exc = []) :
    L.SatisfiesUpTo p (fun s o => ok s o = true) {s | s ∈ exc} := by
  intro s o hs hne
  rcases (exceptionalViolations_eq_nil_iff stmts ok exc).1 h (s, o) (hcomplete s o hs) with
    hmem | hok
  · exact absurd hmem hne
  · exact hok

/-! ### A worked fragment: the `sex or gender` one-of constraint -/

namespace ExceptionExample

open Wikidata

/-- *male* (Q6581097). -/
def male : Qid := .wd "Q6581097"
/-- *female* (Q6581072). -/
def female : Qid := .wd "Q6581072"
/-- *non-binary* (Q48270). -/
def nonBinary : Qid := .wd "Q48270"

/-- An item whose `sex or gender` value is male. -/
def alice : Qid := .wd "Q1"
/-- An item whose `sex or gender` value is female. -/
def bob : Qid := .wd "Q2"
/-- The item whose value is outside the declared list. -/
def robin : Qid := .wd "Q3"

/-- The asserted `sex or gender` (P21) statements of the fragment. -/
def stmts : List (Qid × Qid) := [(alice, male), (bob, female), (robin, nonBinary)]

/-- The **one-of** requirement: the value is male or female. -/
def okOneOf (_ : Qid) (v : Qid) : Bool := v == male || v == female

/-- Without exceptions the constraint is violated, by exactly one statement. -/
theorem violations_no_exception :
    exceptionalViolations stmts okOneOf [] = [(robin, nonBinary)] := by
  decide

/-- Declaring the offending item as an `exception to constraint` (P2303) silences
the check. -/
theorem violations_with_exception :
    exceptionalViolations stmts okOneOf [robin] = [] := by
  decide

/-- An exception for an item that satisfies the requirement changes nothing: it
is redundant. -/
theorem redundant_exception :
    exceptionalViolations stmts okOneOf [alice] = [(robin, nonBinary)] := by
  decide

/-- Enlarging the value list is the other way to make the constraint pass. -/
def okThree (_ : Qid) (v : Qid) : Bool := v == male || v == female || v == nonBinary

theorem violations_relaxed : exceptionalViolations stmts okThree [] = [] := by
  decide

end ExceptionExample

end Wikidata
