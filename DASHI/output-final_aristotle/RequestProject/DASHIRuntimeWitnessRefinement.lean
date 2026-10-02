/-!
DASHI runtime-witness → formal-premise refinement boundary.

A validated runtime certificate carries source/provenance coordinates and a
validator receipt. It does NOT contain a proof of an arbitrary proposition P.
A RefinedWitness P can only be constructed by supplying an independent
inhabitant of P. This prevents opaque runtime strings from becoming theorem
premises by coercion.

No source extraction correctness or external validator soundness is proved
here; those are assumptions of the particular refinement procedure.
-/
import RequestProject.DASHIScopedSoftTyping

namespace DASHI.ContextIndexedOntology

inductive RuntimeWitnessKind
  | subjectIdentity
  | propertyAlignment
  | scopeComparability
  | leftApplicability
  | rightApplicability
  | valueDistinctness
  | positiveOutsideScope
  | consumerObservationPreservation
  | heterogeneousObservableBridge
  deriving DecidableEq, Repr

structure CheckedRuntimeWitness where
  witnessRef : String
  kind : RuntimeWitnessKind
  consumerRef : String
  sourceRevisionRefs : List String
  validationReceiptRef : String
  payloadDigestRef : String
  deriving Repr

/-- The formal premise remains a separate proof-carrying coordinate. -/
structure RefinedWitness (P : Prop) extends CheckedRuntimeWitness where
  premise : P

def refineWitness {P : Prop}
    (runtime : CheckedRuntimeWitness)
    (proof : P) : RefinedWitness P :=
  { runtime with premise := proof }

theorem refinedCarriesPremise {P : Prop}
    (w : RefinedWitness P) : P :=
  w.premise

/-- There is deliberately no constructor from CheckedRuntimeWitness to
    RefinedWitness P without an independently supplied P. The following
    function exposes only the runtime carrier and cannot synthesize P. -/
def forgetFormalPremise {P : Prop}
    (w : RefinedWitness P) : CheckedRuntimeWitness :=
  w.toCheckedRuntimeWitness

/-- Example of the intended cardinality seam: a runtime certificate may be
    associated with a concrete formal counterexample, but the counterexample
    itself must be supplied and remains the theorem-bearing object. -/
def refineValueDistinctness {α : Type}
    {first second : ScopedValue α}
    (runtime : CheckedRuntimeWitness)
    (counterexample : first.value ≠ second.value) :
    RefinedWitness (first.value ≠ second.value) :=
  refineWitness runtime counterexample

end DASHI.ContextIndexedOntology
