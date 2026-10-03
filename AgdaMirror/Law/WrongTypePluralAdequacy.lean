/-!
DASHI-original nonfactorability counterexample for McNamara's Care /
Transaction / Power nine-cell grid. One cell does not determine situated
custodial permission, intersectional positioning, or epistemic authority.

Conceptual sources are NOT authors of this proof:
* McNamara, "A System of Wrong", episode 4, user transcript 2026-09-30.
* Etuaptmumk / Two-Eyed Seeing: Mi'kmaw Elders Albert and Murdena
  Marshall with Cheryl Bartlett. Provenance-respecting coordination.
* Robin Wall Kimmerer, Braiding Sweetgrass (2013): relational reciprocity.
* Kimberlé Crenshaw (1991): DOI 10.2307/1229039.
* Luce Irigaray, This Sex Which Is Not One (1985 English edition).
* Lacan: distinct, source-bounded psychoanalytic grammar.

The example is abstract: it claims nothing about the permissions,
traditional laws or practices of any real Indigenous community.
A source mention never proves legal applicability or liability.
-/
import AgdaMirror.Law.WrongTypeGrid

namespace AgdaMirror.Law.WrongTypeGrid.PluralAdequacy

inductive SituatedCase where
  | permissionEstablished
  | permissionNotEstablished
  deriving DecidableEq

inductive CustodialDecision where
  | established
  | notEstablished
  deriving DecidableEq

def gridProjection (_ : SituatedCase) : Cell := ⟨.care, .transaction⟩

def permissionDecision : SituatedCase → CustodialDecision
  | .permissionEstablished => .established
  | .permissionNotEstablished => .notEstablished

def FactorsThrough {State Flat Outcome : Type}
    (flatten : State → Flat) (query : State → Outcome) : Prop :=
  ∃ f : Flat → Outcome, ∀ s, query s = f (flatten s)

/-- Exact collision: one abstract grid cell conceals distinct permissions. -/
theorem grid_not_sufficient :
    ¬ FactorsThrough gridProjection permissionDecision := by
  intro h
  obtain ⟨f, h⟩ := h
  have one := h .permissionEstablished
  have two := h .permissionNotEstablished
  have contradiction :
      CustodialDecision.established = CustodialDecision.notEstablished :=
    one.trans two.symm
  cases contradiction

theorem no_rechart_recovers_permission {Chart : Type}
    (chart : Cell → Chart) :
    ¬ FactorsThrough (fun s => chart (gridProjection s))
      permissionDecision := by
  intro h
  obtain ⟨f, hf⟩ := h
  apply grid_not_sufficient
  exact ⟨fun c => f (chart c), hf⟩

def situatedProjection (s : SituatedCase) : Cell × CustodialDecision :=
  (gridProjection s, permissionDecision s)

theorem situated_projection_sufficient :
    FactorsThrough situatedProjection permissionDecision := by
  exact ⟨Prod.snd, by intro s; rfl⟩

end AgdaMirror.Law.WrongTypeGrid.PluralAdequacy
