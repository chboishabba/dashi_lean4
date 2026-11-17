import RequestProject.Slr.DocumentQuerySound

/-!
Finite, query-indexed consumer descent for a source-indexed semantic fibre.

The checker is executable with decidable reading and answer equality. Its
soundness theorem is kernel-visible. It does NOT assert that the finite rows
enumerate the entire production semantic fibre: completeness is an explicit
proof input. No Rust success marker, QID or parser span can replace that proof.

Agda owners: DASHI.Core.ConsumerDescentMinimalObserverExact and
DASHI.Reasoning.SemanticConsumerRelativeClosureExact.
-/

namespace Wikidata
namespace Slr
namespace FiniteConsumer

/-- Check that one consumer returns the same result on all listed readings.
    The supplied list is NOT assumed to be semantically exhaustive. -/
def checkConstant {Reading Answer : Type}
    [DecidableEq Answer]
    (readings : List Reading) (answer : Reading → Answer) : Bool :=
  readings.all (fun x =>
    readings.all (fun y => decide (answer x = answer y)))

/-- If the executable test succeeds, answers agree on its concrete rows. -/
theorem checkConstant_sound {Reading Answer : Type}
    [DecidableEq Answer]
    (readings : List Reading) (answer : Reading → Answer)
    (h : checkConstant readings answer = true) :
    ∀ x ∈ readings, ∀ y ∈ readings, answer x = answer y := by
  simp only [checkConstant, List.all_eq_true, decide_eq_true_eq] at h
  exact h

/-- Exhaustive enumeration is supplied as a proof, not inferred from a
    candidate count or the absence of reported parser failures. -/
structure CompleteEnumeration
    {Source Observation Reading Query Answer : Type}
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (observation : Observation) where
  readings : List Reading
  complete : ∀ r, m.live observation r → r ∈ readings

/-- Convert a successful finite consumer check into closure over every
    production-live reading, *provided* the enumerator has a completeness
    witness. This is the crucial input that PR #112 does not yet supply. -/
theorem completeFiniteFibreConsumerClosed
    {Source Observation Reading Query Answer : Type}
    [DecidableEq Answer]
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (o : Observation) (q : Query)
    (rows : CompleteEnumeration m o)
    (h : checkConstant rows.readings (fun r => m.readingAnswer r q) = true) :
    ∀ x, m.live o x → ∀ y, m.live o y →
      m.readingAnswer x q = m.readingAnswer y q := by
  intro x hx y hy
  exact checkConstant_sound rows.readings
    (fun r => m.readingAnswer r q) h x
    (rows.complete x hx) y (rows.complete y hy)

/-- Construct an actual SourceQueryLicence from the checked finite-fibre
    result, its independent completeness proof and the separate
    source-to-reading correspondence. No semantic premise is synthesized
    from the output of SLR or from a string-valued review reference. -/
def licenceOfCompleteFiniteCheck
    {Source Observation Reading Query Answer : Type}
    [DecidableEq Answer]
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (source : Source) (q : Query) (o : Observation)
    (sourceEq : o = m.observe source)
    (rows : CompleteEnumeration m o)
    (chosen : Reading) (chosenLive : m.live o chosen)
    (factor :
      ∀ otherSource, m.observe otherSource = o →
        m.documentAnswer otherSource q = m.readingAnswer chosen q)
    (checked :
      checkConstant rows.readings (fun r => m.readingAnswer r q) = true) :
    SourceQueryLicence m source q where
  observation := o
  sameProducedObservation := sourceEq
  chosenReading := chosen
  chosenIsLive := chosenLive
  consumerFactorises := factor
  consumerClosed := by
    intro reading live
    exact completeFiniteFibreConsumerClosed m o q rows checked
      reading live chosen chosenLive

/-- A real production-live reading omitted from a finite Rust enumeration
is an exact obstruction to claiming that enumeration complete. This is the
fibre-coverage negative gate, not a heuristic based on candidate counts. -/
theorem omittedLiveReadingBlocksCompleteness
    {Source Observation Reading Query Answer : Type}
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (o : Observation) (readings : List Reading)
    (missing : Reading)
    (stillLive : m.live o missing)
    (omitted : missing ∉ readings) :
    ¬ ∃ rows : CompleteEnumeration m o, rows.readings = readings := by
  rintro ⟨rows, hRows⟩
  apply omitted
  simpa [hRows] using rows.complete missing stillLive

end FiniteConsumer
end Slr
end Wikidata
