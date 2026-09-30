/-!
DASHI source-grounded soft typing: single-value *consumer-scoped* contract.
JMD's RequestProject finite property checker remains upstream and unmodified.

A violation requires two separately witnessed applicable, distinct values
under an explicitly shared scope; failure to establish identity, relevance
or scope is Missing, not a counterexample. This file is generic over the
type of evidence values and does not claim that a source observation has
been authenticated, or that Wikidata itself violates a property constraint.
-/
import RequestProject.DASHIContextIndexedTransport

namespace DASHI.ContextIndexedOntology

/-- A consumer-selected scope is not automatically comparable to another. -/
structure ScopedValue (α : Type) where
  value : α
  scope : String
  sourceRevision : String
  statementRef : String

/-- The producer's positive evidence that two values are simultaneously
    in the scope of a single-value demand, rather than merely co-occurring. -/
structure CardinalityCounterexample (α : Type) where
  first : ScopedValue α
  second : ScopedValue α
  consumerScope : String
  firstInScope : first.scope = consumerScope
  secondInScope : second.scope = consumerScope
  distinct : first.value ≠ second.value
  firstApplicableWitnessRef : String
  secondApplicableWitnessRef : String
  distinctnessWitnessRef : String
  scopeWitnessRef : String

/-- A missing scope, applicability, or distinctness proof must not
    be silently converted into a violation. -/
inductive SingleValueJudgment (α : Type)
  | violation (witness : CardinalityCounterexample α)
  | missing (unpaid : List String)
  | outsideScope (reason : String)
  deriving Repr

def classifySingleValue {α : Type}
    (w : Option (CardinalityCounterexample α))
    (missingPremises : List String) : SingleValueJudgment α :=
  match w with
  | some certificate => .violation certificate
  | none => .missing missingPremises

theorem violationHasConcreteCounterexample {α : Type}
    (w : CardinalityCounterexample α) :
    ∃ first second : ScopedValue α,
      first.scope = w.consumerScope ∧
      second.scope = w.consumerScope ∧
      first.value ≠ second.value := by
  exact ⟨w.first, w.second, w.firstInScope,
    w.secondInScope, w.distinct⟩

theorem missingCannotBePromotedToViolation {α : Type}
    (debt : List String) :
    ∀ w : CardinalityCounterexample α,
      classifySingleValue none debt ≠ SingleValueJudgment.violation w := by
  intro w h
  cases h

theorem acceptedSourceScopesAreEqual {α : Type}
    (w : CardinalityCounterexample α) :
    w.first.scope = w.second.scope := by
  exact w.firstInScope.trans w.secondInScope.symm

/-- Consumer-local "repair" means that a stated residual was eliminated
    while an independent chosen observable was preserved. Existence of
    this *certificate* is a hypothesis, not a repair search algorithm. -/
structure MeasuredImprovement (α out : Type)
    (preserved : ConsumerView α out)
    (debt : α → Nat) where
  before : α
  after : α
  sameConsumerObservation : preserved.observe after = preserved.observe before
  strictlyLessDebt : debt after < debt before
  beforeReceiptRef : String
  afterReceiptRef : String
  rerunWitnessRef : String

theorem measuredRepairImprovesWithoutChangingConsumer {α out : Type}
    {view : ConsumerView α out} {debt : α → Nat}
    (r : MeasuredImprovement α out view debt) :
    debt r.after < debt r.before ∧
    view.observe r.after = view.observe r.before :=
  ⟨r.strictlyLessDebt, r.sameConsumerObservation⟩

/-- A bridge from different consumer outputs must be explicitly paid.
    The bridge statement is an assumption that carries an actual function
    and proof, not a lexical or QID-based inference. -/
structure HeterogeneousObservableBridge
    (outA outB common : Type)
    (a : outA → common) (b : outB → common) where
  forward : outA → outB
  preserves : ∀ x, b (forward x) = a x

/-- Compose a native representation translation with an explicitly
    established bridge between heterogeneous observations. -/
def Licensed.composeHeterogeneous
    {α β outA outB common : Type}
    {observeA : ConsumerView α outA}
    {observeB : ConsumerView β outA}
    {intoCommonA : outA → common} {intoCommonB : outB → common}
    (native : Licensed α β outA observeA observeB)
    (bridge : HeterogeneousObservableBridge outA outB common
      intoCommonA intoCommonB) :
    ∀ x : α,
      intoCommonB (bridge.forward (observeB.observe (native.map x))) =
      intoCommonA (observeA.observe x) := by
  intro x
  rw [bridge.preserves, native.preserves]

end DASHI.ContextIndexedOntology
