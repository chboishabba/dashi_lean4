import Integration.ScopedVerifierConsumerSufficiency

namespace Integration.ConsumerRelativeRepresentationParity

open Integration.ScopedVerifierConsumerSufficiency

------------------------------------------------------------------------
-- Consumer-relative parity: no global representation-equivalence claim.
------------------------------------------------------------------------

structure ConsumerParity {X L R C : Type}
    (left : X → L) (right : X → R) (consumer : X → C) where
  leftFactorization : ConsumerFactorization left consumer
  rightFactorization : ConsumerFactorization right consumer

structure EligibleRepresentation {X O C : Type}
    (observe : X → O) (consumer : X → C) where
  Admissible : Prop
  admissibilityReceipt : Admissible
  ConsumerAdequate : Prop
  consumerAdequacyReceipt : ConsumerAdequate
  consumerFactorization : ConsumerFactorization observe consumer

------------------------------------------------------------------------
-- Expressive complexity is an independent observer coordinate.
------------------------------------------------------------------------

structure ExpressiveAsymmetryWitness {X S K : Type}
    (semantic : X → S) (complexity : X → K) where
  leftState : X
  rightState : X
  sameSemantic : semantic leftState = semantic rightState
  complexitySeparates : complexity leftState ≠ complexity rightState

theorem factorizedConsumerIgnoresIndependentComplexity {X S K C : Type}
    {semantic : X → S} {complexity : X → K} {consumer : X → C}
    (factor : ConsumerFactorization semantic consumer)
    (left right : X)
    (sameSemantic : semantic left = semantic right) :
    consumer left = consumer right := by
  calc
    consumer left = factor.decode (semantic left) := (factor.factorizes left).symm
    _ = factor.decode (semantic right) := congrArg factor.decode sameSemantic
    _ = consumer right := factor.factorizes right

theorem expressiveComplexityCannotChangeFactorizedConsumer {X S K C : Type}
    {semantic : X → S} {complexity : X → K} {consumer : X → C}
    (factor : ConsumerFactorization semantic consumer)
    (w : ExpressiveAsymmetryWitness semantic complexity) :
    consumer w.leftState = consumer w.rightState :=
  factorizedConsumerIgnoresIndependentComplexity factor
    w.leftState w.rightState w.sameSemantic

------------------------------------------------------------------------
-- Typed semantic perturbations.
------------------------------------------------------------------------

structure ConsumerPerturbation {X C : Type} (consumer : X → C) where
  actState : X → X
  actOutcome : C → C
  commutes : ∀ x, consumer (actState x) = actOutcome (consumer x)

def ConsumerInvariant {X C : Type} {consumer : X → C}
    (p : ConsumerPerturbation consumer) : Prop :=
  ∀ x, consumer (p.actState x) = consumer x

theorem semanticPreservingPerturbationIsInvariant {X C : Type}
    {consumer : X → C}
    (p : ConsumerPerturbation consumer)
    (preserving : ∀ outcome, p.actOutcome outcome = outcome) :
    ConsumerInvariant p := by
  intro x
  calc
    consumer (p.actState x) = p.actOutcome (consumer x) := p.commutes x
    _ = consumer x := preserving _

structure RepresentationPerturbationAdequacy {X O C : Type}
    (observe : X → O) (consumer : X → C)
    (p : ConsumerPerturbation consumer) where
  factorization : ConsumerFactorization observe consumer
  actObservation : O → O
  representationCommutes : ∀ x, observe (p.actState x) = actObservation (observe x)
  quotientCommutes : ∀ o,
    factorization.decode (actObservation o) = p.actOutcome (factorization.decode o)

theorem representationSquarePaysConsumerPerturbation {X O C : Type}
    {observe : X → O} {consumer : X → C}
    {p : ConsumerPerturbation consumer}
    (w : RepresentationPerturbationAdequacy observe consumer p) :
    ∀ x, consumer (p.actState x) = p.actOutcome (consumer x) := by
  intro x
  calc
    consumer (p.actState x) = w.factorization.decode (observe (p.actState x)) :=
      (w.factorization.factorizes (p.actState x)).symm
    _ = w.factorization.decode (w.actObservation (observe x)) :=
      congrArg w.factorization.decode (w.representationCommutes x)
    _ = p.actOutcome (w.factorization.decode (observe x)) := w.quotientCommutes _
    _ = p.actOutcome (consumer x) :=
      congrArg p.actOutcome (w.factorization.factorizes x)

structure RepresentationParityBoundary where
  parityIsConsumerRelative : Bool
  admissibilitySeparateFromConsumerFactorization : Bool
  expressiveComplexityCreatesAuthority : Bool
  semanticPreservingPerturbationMustPreserveConsumer : Bool
  representationMapAlonePaysPerturbationAdequacy : Bool
  deriving DecidableEq, Repr

def canonicalBoundary : RepresentationParityBoundary :=
  ⟨true, true, false, true, false⟩

end Integration.ConsumerRelativeRepresentationParity
