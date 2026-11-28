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
  deriving DecidableEq, BEq, Repr

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
def namedEntity : Referent → Bool
  | .entity _ => true
  | _ => false

def action (actor : Referent) (r : Reading) : Sign :=
  if namedEntity actor = true ∧ r.referent = actor ∧ (r.role = .agent ∨ r.role = .speaker) ∧ r.scope = .asserted
  then r.sign else .zero

def actionCoordinate (r : Reading) : Referent × Role × Scope × Sign :=
  (r.referent, r.role, r.scope, r.sign)

def actionAt (actor : Referent) (c : Referent × Role × Scope × Sign) : Sign :=
  if namedEntity actor = true ∧ c.1 = actor ∧ (c.2.1 = .agent ∨ c.2.1 = .speaker) ∧ c.2.2.1 = .asserted
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
    Referent.outside ≠ Referent.entity key := by
  intro h
  cases h

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
  match s with
  | .positive => ⟨true,false⟩
  | .negative => ⟨false,true⟩
  | .zero => ⟨false,false⟩

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

def compare (a b : Reading) : Option (Support × Support) := by
  classical
  exact if propositionCoordinate a = propositionCoordinate b
    then some (support a.sign, support b.sign) else none

theorem reciprocalComparison (a b : Reading) :
    compare b a = (compare a b).map Prod.swap := by
  classical
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


/-- Compare independent *licensed* answers to the SAME declared typed query.
    none = unavailable/unlicensed answer; some zero = recorded no support
    under the licensed query scope. Neither means a negative assertion.
    This is a consumer of the original licences, not a translation checker. -/
def viewProofDelta (left right : Option Support) : Option (Support × Support) :=
  match left, right with
  | some l, some r =>
    some (⟨l.positive && !r.positive, l.negative && !r.negative⟩,
          ⟨r.positive && !l.positive, r.negative && !l.negative⟩)
  | _, _ => none

theorem viewDeltaReciprocal (left right : Option Support) :
    viewProofDelta right left = (viewProofDelta left right).map Prod.swap := by
  cases left <;> cases right <;> rfl

theorem missingViewIsNotProofAgreement :
    viewProofDelta none none = none := rfl

theorem sameSupportPreservesBothProofSigns (s : Support) :
    viewProofDelta (some s) (some s) = some (support .zero, support .zero) := by
  cases s with
  | mk p n => cases p <;> cases n <;> rfl

theorem positiveToNegativeRetainsBothDeltas :
    viewProofDelta (some (support .positive)) (some (support .negative)) =
      some (support .positive, support .negative) := rfl

/-- Source-licensed directional preservation/difference. Both models must
    already interpret the identical typed query coordinate; that source
    correspondence must be produced independently, never inferred from
    QID, translated labels, constructor shape, or role overlap. -/
theorem reciprocalLicensedViewProofDelta
    {S O R T P U Q : Type}
    {left : DocumentQueryModel S O R Q (Option Support)}
    {right : DocumentQueryModel T P U Q (Option Support)}
    {s : S} {t : T} {q : Q}
    (l : SourceQueryLicence left s q) (r : SourceQueryLicence right t q)
    (x : R) (y : U) (hx : left.live l.observation x)
    (hy : right.live r.observation y) :
    (viewProofDelta (left.readingAnswer x q) (right.readingAnswer y q),
      viewProofDelta (right.readingAnswer y q) (left.readingAnswer x q)) =
    (viewProofDelta (left.documentAnswer s q) (right.documentAnswer t q),
      viewProofDelta (right.documentAnswer t q) (left.documentAnswer s q)) :=
  reciprocalLicensedComparison l r viewProofDelta viewProofDelta x y hx hy

/-- Full proof preservation in both signed channels, not mere absence of
    known contradictions. Requires two positive source licences and equal
    checked support; a missing view cannot inhabit this endpoint. -/
theorem licensedViewsPreserveBothSigns
    {S O R T P U Q : Type}
    {left : DocumentQueryModel S O R Q (Option Support)}
    {right : DocumentQueryModel T P U Q (Option Support)}
    {s : S} {t : T} {q : Q}
    (l : SourceQueryLicence left s q) (r : SourceQueryLicence right t q)
    (a : Support)
    (hl : left.readingAnswer l.chosenReading q = some a)
    (hr : right.readingAnswer r.chosenReading q = some a) :
    viewProofDelta (left.documentAnswer s q) (right.documentAnswer t q) =
      some (support .zero, support .zero) := by
  rw [slrJmdDocumentQuerySound l _ hl, slrJmdDocumentQuerySound r _ hr]
  exact sameSupportPreservesBothProofSigns a


/-- Bidi endpoint: an available pair has no lost or gained signed proof
    exactly when its two support channels coincide. This is deliberately
    stricter than absence of a contradiction. -/
theorem zeroViewDeltaIffEqualSupport (l r : Support) :
    viewProofDelta (some l) (some r) = some (support .zero, support .zero) ↔ l = r := by
  cases l with
  | mk lp ln =>
    cases r with
    | mk rp rn =>
      cases lp <;> cases ln <;> cases rp <;> cases rn <;> decide

/-- An abstraction with a dropped positive claim is not parity even if
    neither representation contains an explicit negative assertion. -/
theorem omittedPositiveIsNotProofParity :
    viewProofDelta (some (support .positive)) (some (support .zero)) ≠
      some (support .zero, support .zero) := by decide

/-- A nonconstant live fibre obstructs a licence before any comparison.
    Reuses the original negative gate instead of treating abstention as
    the semantic answer of a lossy representation. -/
theorem differingLiveProofSignsBlockViewLicence
    {S O R Q : Type} {m : DocumentQueryModel S O R Q (Option Support)}
    {s : S} {q : Q}
    (x y : R) (hx : m.live (m.observe s) x) (hy : m.live (m.observe s) y)
    (different : m.readingAnswer x q ≠ m.readingAnswer y q) :
    ¬ Nonempty (SourceQueryLicence m s q) :=
  incompatibleLiveReadingsBlockQueryLicence x y hx hy different


/-- The proof-bearing value exported to the existing referee as the
    signed-view-query answer. The external query identifier, source
    digests, statement digest and native selectors must still be bound
    by that referee; a JSON rendering is not the proof. -/
structure LicensedSignedViewAnswer
    {S O R T P U Q : Type}
    (left : DocumentQueryModel S O R Q (Option Support))
    (right : DocumentQueryModel T P U Q (Option Support))
    (s : S) (t : T) (q : Q) where
  leftSupport : Option Support
  rightSupport : Option Support
  leftSound : left.documentAnswer s q = leftSupport
  rightSound : right.documentAnswer t q = rightSupport

def signedViewAnswerOfLicences
    {S O R T P U Q : Type}
    {left : DocumentQueryModel S O R Q (Option Support)}
    {right : DocumentQueryModel T P U Q (Option Support)}
    {s : S} {t : T} {q : Q}
    (l : SourceQueryLicence left s q) (r : SourceQueryLicence right t q) :
    LicensedSignedViewAnswer left right s t q :=
  ⟨left.readingAnswer l.chosenReading q, right.readingAnswer r.chosenReading q,
    slrJmdDocumentQuerySound l _ rfl, slrJmdDocumentQuerySound r _ rfl⟩

/-- The answer contains the actual source-bound support, not the
    outcome of a candidate similarity or source-local polarity heuristic. -/
theorem licensedSignedViewAnswerDelta
    {S O R T P U Q : Type}
    {left : DocumentQueryModel S O R Q (Option Support)}
    {right : DocumentQueryModel T P U Q (Option Support)}
    {s : S} {t : T} {q : Q}
    (a : LicensedSignedViewAnswer left right s t q) :
    viewProofDelta (left.documentAnswer s q) (right.documentAnswer t q) =
      viewProofDelta a.leftSupport a.rightSupport := by
  rw [a.leftSound, a.rightSound]

/-- If two pair witnesses share exactly the same typed source and query,
    their answer coordinate agrees. A mismatch in native pair readback
    therefore signals a binding/model problem, not an ontology fact. -/
theorem sharedLicensedViewAnswerUnique
    {S O R T P U X Y Z Q : Type}
    {left : DocumentQueryModel S O R Q (Option Support)}
    {middle : DocumentQueryModel T P U Q (Option Support)}
    {right : DocumentQueryModel X Y Z Q (Option Support)}
    {s : S} {t : T} {u : X} {q : Q}
    (a : LicensedSignedViewAnswer left middle s t q)
    (b : LicensedSignedViewAnswer middle right t u q) :
    a.rightSupport = b.leftSupport :=
  a.rightSound.symm.trans b.leftSound

end Wikidata.Slr.WorldSemanticFibre

#print axioms Wikidata.Slr.WorldSemanticFibre.actionClosed
#print axioms Wikidata.Slr.WorldSemanticFibre.actionDiscriminator
#print axioms Wikidata.Slr.WorldSemanticFibre.reciprocalComparison
#print axioms Wikidata.Slr.WorldSemanticFibre.actionLicence

#print axioms Wikidata.Slr.WorldSemanticFibre.reciprocalLicensedViewProofDelta
#print axioms Wikidata.Slr.WorldSemanticFibre.licensedViewsPreserveBothSigns

#print axioms Wikidata.Slr.WorldSemanticFibre.zeroViewDeltaIffEqualSupport
#print axioms Wikidata.Slr.WorldSemanticFibre.differingLiveProofSignsBlockViewLicence

#print axioms Wikidata.Slr.WorldSemanticFibre.licensedSignedViewAnswerDelta
#print axioms Wikidata.Slr.WorldSemanticFibre.sharedLicensedViewAnswerUnique
