import RequestProject.Slr.WorldSemanticFibre
import RequestProject.Slr.GwbArticleSystemSoundness

/-! Bounded full-lead rule; independent source provenance, native attachment
and interpretation coverage are not manufactured by this module. -/
namespace Wikidata.Slr.GwbMultilingualOffice
open WorldSemanticFibre

inductive Edition where
  | en | simple | es
  deriving DecidableEq, Repr

def lead : Edition → String
  | .en => "George Walker Bush (born July 6, 1946) is an American retired politician and businessman who served as the 43rd president of the United States from 2001 to 2009."
  | .simple => "George Walker Bush (born July 6, 1946) is an American politician and businessman. He was the 43rd president of the United States from 2001 to 2009."
  | .es => "George Walker Bush (pronunciación en inglés: /bʊʃ/ (); New Haven, Connecticut, 6 de julio de 1946), es un político y empresario estadounidense que ejerció como el 43.er presidente de los Estados Unidos entre el 20 de enero de 2001 y el 20 de enero de 2009."

structure OfficeClaim where
  holder : String
  property : String
  office : String
  ordinal : Nat
  startYear : Nat
  endYear : Nat
  deriving DecidableEq, Repr

def claim : OfficeClaim := ⟨"Q207", "P39", "Q11696", 43, 2001, 2009⟩

inductive Query where
  | officeYears (expected : OfficeClaim)
  | exactDays (expected : OfficeClaim) (startDay endDay startMonth endMonth : Nat)
  deriving DecidableEq

abbrev Source := Edition × String

def answer (s : Source) (q : Query) : Option Support :=
  if s.2.startsWith (lead s.1) then
    match q with
    | .officeYears c => if c = claim then some (support .positive) else none
    | .exactDays c sd ed sm em =>
        if c = claim ∧ s.1 = .es ∧ sd = 20 ∧ ed = 20 ∧ sm = 1 ∧ em = 1
        then some (support .positive) else none
  else none

def model : DocumentQueryModel Source Source Source Query (Option Support) where
  observe := id
  live := fun o r => r = o
  documentAnswer := answer
  readingAnswer := answer

def licence (s : Source) (q : Query) : SourceQueryLicence model s q where
  observation := s
  sameProducedObservation := rfl
  chosenReading := s
  chosenIsLive := rfl
  consumerFactorises := fun t h => congrArg (fun x => answer x q) h
  consumerClosed := fun r h => congrArg (fun x => answer x q) h

def yearQuery : Query := .officeYears claim
def dayQuery : Query := .exactDays claim 20 20 1 1

theorem yearAnswer (s : Source) (h : s.2.startsWith (lead s.1) = true) :
    model.documentAnswer s yearQuery = some (support .positive) := by
  change answer s yearQuery = _
  simp [answer, h, yearQuery]

theorem reciprocalYears (a b : Source)
    (ha : a.2.startsWith (lead a.1) = true)
    (hb : b.2.startsWith (lead b.1) = true) :
    viewProofDelta (model.documentAnswer a yearQuery) (model.documentAnswer b yearQuery) =
      some (support .zero, support .zero) := by
  rw [yearAnswer a ha, yearAnswer b hb]
  exact sameSupportPreservesBothProofSigns _

theorem enDaysHeld : answer (.en, lead .en) dayQuery = none := by decide
theorem simpleDaysHeld : answer (.simple, lead .simple) dayQuery = none := by decide
theorem esDaysAvailable : answer (.es, lead .es) dayQuery = some (support .positive) := by decide
theorem unrelatedHeld : answer (.en, "He flew warplanes.") yearQuery = none := by decide

theorem yearSupportCannotRecoverDays :
    ¬ (∃ f : Option Support → Option Support,
       ∀ s : Source, f (answer s yearQuery) = answer s dayQuery) := by
  rintro ⟨f, hf⟩
  have h1 := hf (.en, lead .en)
  have h2 := hf (.es, lead .es)
  have same : answer (.en, lead .en) yearQuery = answer (.es, lead .es) yearQuery := by decide
  rw [same] at h1
  have contra := h1.symm.trans h2
  rw [enDaysHeld, esDaysAvailable] at contra
  contradiction


/-- Exact occurrence selected within the independently named full-lead rule.
The original parser coordinate remains a separate checked premise. -/
def occurrence : Edition → Nat × Nat × String
  | .en => (93, 99, "served")
  | .simple => (85, 88, "was")
  | .es => (147, 154, "ejerció")

def predicateMatches (s : Source) : Bool :=
  let (a,b,literal) := occurrence s.1
  decide (a < b ∧ b ≤ s.2.toList.length) &&
    String.ofList ((s.2.toList.drop a).take (b-a)) == literal

def attachedAnswer (s : Source) (q : Query) : Option Support :=
  if predicateMatches s then answer s q else none

theorem attachedYearSound (s : Source)
    (leadMatched : s.2.startsWith (lead s.1) = true)
    (predicateMatched : predicateMatches s = true) :
    attachedAnswer s yearQuery = some (support .positive) := by
  have h := yearAnswer s leadMatched
  change answer s yearQuery = _ at h
  simp [attachedAnswer, predicateMatched, h]

theorem exactLeadOccurrences : ∀ e : Edition, predicateMatches (e, lead e) = true := by
  intro e
  cases e <;> decide

theorem attachedReciprocal (a b : Source)
    (ha : a.2.startsWith (lead a.1) = true)
    (hb : b.2.startsWith (lead b.1) = true)
    (pa : predicateMatches a = true)
    (pb : predicateMatches b = true) :
    viewProofDelta (attachedAnswer a yearQuery) (attachedAnswer b yearQuery) =
      some (support .zero, support .zero) := by
  rw [attachedYearSound a ha pa, attachedYearSound b hb pb]
  exact sameSupportPreservesBothProofSigns _

/-- A producer cannot transfer the controlled interpretation to an unrelated
predicate merely because the same article and QID were selected. -/
theorem wrongOccurrenceRejected :
    predicateMatches (.en, "He flew warplanes.") = false := by decide


/-- The golden pair answer, not merely an equality of signed deltas.
The two query coordinates are deliberately different. -/
inductive OfficeConsumer where
  | years | days
  deriving DecidableEq, Repr

def OfficeConsumer.query : OfficeConsumer → Query
  | .years => yearQuery
  | .days => dayQuery

def expectedSupport (e : Edition) (q : OfficeConsumer) : Option Support :=
  match q with
  | .years => some (support .positive)
  | .days => if e = .es then some (support .positive) else none

theorem attachedConsumerExact (s : Source) (q : OfficeConsumer)
    (h : s.2.startsWith (lead s.1) = true)
    (p : predicateMatches s = true) :
    attachedAnswer s q.query = expectedSupport s.1 q := by
  cases q with
  | years => exact attachedYearSound s h p
  | days =>
    rcases s with ⟨e, text⟩
    cases e <;> simp [OfficeConsumer.query, dayQuery, attachedAnswer,
      answer, expectedSupport, h, p]

/-- Independent ordered source pair. No inference via a third source. -/
theorem exactPairAnswer (a b : Source) (q : OfficeConsumer)
    (ha : a.2.startsWith (lead a.1) = true)
    (hb : b.2.startsWith (lead b.1) = true)
    (pa : predicateMatches a = true) (pb : predicateMatches b = true) :
    (attachedAnswer a q.query, attachedAnswer b q.query) =
      (expectedSupport a.1 q, expectedSupport b.1 q) := by
  rw [attachedConsumerExact a q ha pa, attachedConsumerExact b q hb pb]

end Wikidata.Slr.GwbMultilingualOffice

#print axioms Wikidata.Slr.GwbMultilingualOffice.reciprocalYears
#print axioms Wikidata.Slr.GwbMultilingualOffice.yearSupportCannotRecoverDays

#print axioms Wikidata.Slr.GwbMultilingualOffice.exactPairAnswer
