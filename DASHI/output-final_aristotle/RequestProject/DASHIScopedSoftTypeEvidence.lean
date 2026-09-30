/-!
DASHI-local executable, consumer-scoped single-value diagnostic.

The original JMD RequestProject checker is not changed. This
checks a *producer-supplied* fact carrier. A Bool applicability receipt
is not an independent proof that the source was correctly extracted.
The checker makes its premises inspectable and cannot classify two
different scopes as a violation merely because two values differ.
-/
import RequestProject.DASHIScopedSoftTyping

namespace DASHI.ContextIndexedOntology

/-- Source-local fact. The producer's applicability observation is explicit. -/
structure ScopedEvidenceFact (α : Type) where
  subject : String
  property : String
  scope : String
  value : α
  applicable : Bool
  sourceRevision : String
  statementRef : String

structure ScopedEvidenceDemand where
  subject : String
  property : String
  scope : String
  consumerRef : String
  contractRef : String

/-- All premises must hold simultaneously in the declared consumer scope. -/
structure ApplicableCounterexample (α : Type)
    (d : ScopedEvidenceDemand)
    (a b : ScopedEvidenceFact α) : Prop where
  firstSubject : a.subject = d.subject
  secondSubject : b.subject = d.subject
  firstProperty : a.property = d.property
  secondProperty : b.property = d.property
  firstScope : a.scope = d.scope
  secondScope : b.scope = d.scope
  firstApplicable : a.applicable = true
  secondApplicable : b.applicable = true
  differentValues : a.value ≠ b.value

/-- A computable decision relative to supplied source/contract coordinates.
    None means not certified: it need not mean the assertion is false. -/
def checkApplicable [DecidableEq α]
    (d : ScopedEvidenceDemand)
    (a b : ScopedEvidenceFact α) :
    Option (ApplicableCounterexample α d a b) :=
  if h : a.subject = d.subject ∧
         b.subject = d.subject ∧
         a.property = d.property ∧
         b.property = d.property ∧
         a.scope = d.scope ∧
         b.scope = d.scope ∧
         a.applicable = true ∧
         b.applicable = true ∧
         a.value ≠ b.value then
    some {
      firstSubject := h.1
      secondSubject := h.2.1
      firstProperty := h.2.2.1
      secondProperty := h.2.2.2.1
      firstScope := h.2.2.2.2.1
      secondScope := h.2.2.2.2.2.1
      firstApplicable := h.2.2.2.2.2.2.1
      secondApplicable := h.2.2.2.2.2.2.2.1
      differentValues := h.2.2.2.2.2.2.2.2
    }
  else none

/-- Positive results certify the exact conjunction, including applicability. -/
theorem checkApplicable_sound [DecidableEq α]
    {d : ScopedEvidenceDemand}
    {a b : ScopedEvidenceFact α}
    {w : ApplicableCounterexample α d a b}
    (h : checkApplicable d a b = some w) :
    a.scope = b.scope ∧
    a.applicable = true ∧ b.applicable = true ∧ a.value ≠ b.value := by
  exact ⟨w.firstScope.trans w.secondScope.symm,
    w.firstApplicable, w.secondApplicable, w.differentValues⟩

/-- If every required premise was supplied, the checker does return a witness. -/
theorem checkApplicable_complete [DecidableEq α]
    {d : ScopedEvidenceDemand}
    {a b : ScopedEvidenceFact α}
    (h : a.subject = d.subject ∧
         b.subject = d.subject ∧
         a.property = d.property ∧
         b.property = d.property ∧
         a.scope = d.scope ∧
         b.scope = d.scope ∧
         a.applicable = true ∧
         b.applicable = true ∧
         a.value ≠ b.value) :
    (checkApplicable d a b).isSome = true := by
  simp [checkApplicable, h]

/-- The executable negative control shares subject/property but not scope. -/
def sampleDemand : ScopedEvidenceDemand :=
  ⟨"subject", "property", "2020", "consumer", "single-value"⟩

def sampleEarlier : ScopedEvidenceFact Bool :=
  ⟨"subject", "property", "2020", false, true, "source-a", "statement-a"⟩

def sampleLater : ScopedEvidenceFact Bool :=
  ⟨"subject", "property", "2021", true, true, "source-b", "statement-b"⟩

theorem differentScopeIsNotAViolation :
    checkApplicable sampleDemand sampleEarlier sampleLater = none := by
  decide

/-- Missing applicability is not a negative assertion about the value. -/
def sampleMissingApplicability : ScopedEvidenceFact Bool :=
  ⟨"subject", "property", "2020", true, false, "source-c", "statement-c"⟩

theorem missingApplicabilityIsNotAViolation :
    checkApplicable sampleDemand sampleEarlier sampleMissingApplicability = none := by
  decide

/-- A positive local test with independently supplied true applicability. -/
def sampleApplicableOther : ScopedEvidenceFact Bool :=
  ⟨"subject", "property", "2020", true, true, "source-d", "statement-d"⟩

theorem positiveScopedWitness :
    (checkApplicable sampleDemand sampleEarlier sampleApplicableOther).isSome =
      true := by
  decide

end DASHI.ContextIndexedOntology
