import RequestProject.Slr.FiniteConsumerCertificate
import RequestProject.Slr.GwbCoreferenceFormalRepair

/-! Consumer-relative semantic coordinates. Source-local identity is not world
identity. An outside-model referent is retained; missing support is not denial.
This is a bounded typed interpretation algebra, not a claim of natural-language
coverage. The original producer must supply the source correspondence. -/
namespace Wikidata.Slr.WorldSemanticFibre

inductive Referent where
  | entity (key : String)
  | eventuality (key : String)
  | proposition (key : String)
  | expletive
  | outside
  deriving DecidableEq, Repr

inductive Role where
  | agent | patient | speaker | experiencer | other | unknown
  deriving DecidableEq, Repr

inductive Scope where
  | asserted | reported | predicted | hypothetical | mentioned | unknown
  deriving DecidableEq, Repr

inductive Sign where
  | negative | zero | positive
  deriving DecidableEq, Repr

structure Anchor where
  revision : String
  digest : String
  region : String
  predicate : String
  deriving DecidableEq, Repr

structure Reading where
  anchor : Anchor
  referent : Referent
  role : Role
  scope : Scope
  sign : Sign
  event : String
  capacity : Option String
  time : Option String
  attribution : Option String
  deriving DecidableEq, Repr

/-- Three-valued answer: zero is neither denial nor established action.
A positive action requires the appropriate semantic role and asserted scope.
A negative answer is an explicit negative assertion in that same fibre. -/
def action (actor : Referent) (r : Reading) : Sign :=
  if r.referent = actor ∧ r.role = .agent ∧ r.scope = .asserted
  then r.sign else .zero

def actionCoordinate (r : Reading) : Referent × Role × Scope × Sign :=
  (r.referent, r.role, r.scope, r.sign)

def actionAt (actor : Referent) (c : Referent × Role × Scope × Sign) : Sign :=
  if c.1 = actor ∧ c.2.1 = .agent ∧ c.2.2.1 = .asserted
  then c.2.2.2 else .zero

theorem actionFactors (actor : Referent) (r : Reading) :
    action actor r = actionAt actor (actionCoordinate r) := rfl

theorem patientNotAction (actor : Referent) (r : Reading)
    (h : r.role = .patient) : action actor r = .zero := by
  simp [action, h]

theorem predictionNotAction (actor : Referent) (r : Reading)
    (h : r.scope = .predicted) : action actor r = .zero := by
  simp [action, h]

theorem outsideNotNamedEntity (key : String) :
    Referent.outside ≠ Referent.entity key := by decide

/-- Fixed source coordinates can be returned without resolving referent identity. -/
theorem anchorInvariant (a : Anchor) (live : Reading → Prop)
    (bound : ∀ r, live r → r.anchor = a) :
    ∀ x, live x → ∀ y, live y → x.anchor = y.anchor := by
  intro x hx y hy
  exact (bound x hx).trans (bound y hy).symm

/-- Concrete action descent reuses the existing projected-envelope theorem. -/
theorem actionClosed (actor : Referent) (live : Reading → Prop)
    (domain : List (Referent × Role × Scope × Sign))
    (covers : ∀ r, live r → actionCoordinate r ∈ domain)
    (checked : FiniteConsumer.checkConstant domain (actionAt actor) = true) :
    ∀ x, live x → ∀ y, live y → action actor x = action actor y :=
  FiniteConsumer.projectedEnvelopeConsumerClosed live actionCoordinate domain
    (actionAt actor) (action actor) covers (fun r _ => actionFactors actor r) checked

/-- Reverse solve a failed action projection into exact coordinate debt. -/
theorem actionDiscriminator (actor : Referent)
    (domain : List (Referent × Role × Scope × Sign))
    (failed : FiniteConsumer.checkConstant domain (actionAt actor) = false) :
    ∃ x ∈ domain, ∃ y ∈ domain, actionAt actor x ≠ actionAt actor y :=
  FiniteConsumer.projectedEnvelopeDisagreement domain (actionAt actor) failed

/-- Distinguish source support from world truth and preserve both signs. -/
structure Support where
  positive : Bool
  negative : Bool
  deriving DecidableEq, Repr

def support (s : Sign) : Support :=
  ⟨s == .positive, s == .negative⟩

def join (a b : Support) : Support :=
  ⟨a.positive || b.positive, a.negative || b.negative⟩

theorem unknownNeutral (a : Support) : join a (support .zero) = a := by
  cases a with
  | mk p n => cases p <;> cases n <;> rfl

theorem bothSigns : join (support .positive) (support .negative) = ⟨true,true⟩ := rfl

/-- A common proposition coordinate explicitly includes all relevant axes.
Equality of event labels alone is insufficient. -/
def propositionCoordinate (r : Reading) :=
  (r.referent, r.role, r.scope, r.event, r.capacity, r.time, r.attribution)

def compare (a b : Reading) : Option (Support × Support) :=
  if propositionCoordinate a = propositionCoordinate b
  then some (support a.sign, support b.sign) else none

theorem reciprocalComparison (a b : Reading) :
    compare b a = (compare a b).map Prod.swap := by
  by_cases h : propositionCoordinate a = propositionCoordinate b
  · simp [compare, h, h.symm, Prod.swap]
  · have hr : propositionCoordinate b ≠ propositionCoordinate a := Ne.symm h
    simp [compare, h, hr]

/-- Explicit comparison licence consumes the original document query model.
The semantic model and source factorisation are not manufactured here. -/
def actionLicence
    {S O Q : Type} (m : DocumentQueryModel S O Reading Q Sign)
    (s : S) (q : Q) (actor : Referent)
    (chosen : Reading) (chosenLive : m.live (m.observe s) chosen)
    (domain : List (Referent × Role × Scope × Sign))
    (covers : ∀ r, m.live (m.observe s) r → actionCoordinate r ∈ domain)
    (factor : ∀ r, m.live (m.observe s) r → m.readingAnswer r q = action actor r)
    (sourceFactor : ∀ t, m.observe t = m.observe s →
      m.documentAnswer t q = m.readingAnswer chosen q)
    (checked : FiniteConsumer.checkConstant domain (actionAt actor) = true) :
    SourceQueryLicence m s q :=
  FiniteConsumer.licenceOfProjectedEnvelope m s q (m.observe s) rfl
    chosen chosenLive actionCoordinate domain (actionAt actor) covers
    (fun r h => (factor r h).trans (actionFactors actor r)) sourceFactor checked

end Wikidata.Slr.WorldSemanticFibre

#print axioms Wikidata.Slr.WorldSemanticFibre.actionClosed
#print axioms Wikidata.Slr.WorldSemanticFibre.actionDiscriminator
#print axioms Wikidata.Slr.WorldSemanticFibre.reciprocalComparison
#print axioms Wikidata.Slr.WorldSemanticFibre.actionLicence
