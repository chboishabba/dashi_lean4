/-!
# Sentence-level belief, mistaken belief, and retrospective correction

A bounded Lean fixture for the SLR -> PNF -> article-contents programme.
Reuses the orthogonal attribution / proposition / occurrence separation from
DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact and
SensibLawAttributionPropositionOccurrenceBidiExact, and the chronology /
contestation approach of SensibLawChronologyContestationSpineExact.

No lexical parser, Wikidata theorem, source reviewer or semantic authority is
reimplemented here. These are proofs *about explicitly supplied readings*;
the live SLR producer-to-reading licensing remains a separate open obligation.

JMD's existing Wikidata getter/proof engine remains credited to
meta-introspector/RequestProject. This is a DASHI integration fixture.
-/
import RequestProject.Slr.Producer

namespace Wikidata
namespace Slr

/-- Proposition identity remains constant across assertion, belief and denial. -/
structure CallProposition where
  actor : String
  patient : String
  deriving DecidableEq, Repr, Inhabited

/-- A semantic reading says whose attitude the text represents; a source
    assertion is not an occurrence proof. The marker 'mistaken' records the
    narrator's appraisal of a belief, not an independently checked world fact. -/
inductive DiscourseScope where
  | narratorAssertion
  | attributedBelief (holder : String)
  | narratorMistakeAssessment (holder : String)
  | narratorRetrospectiveCorrection
  deriving DecidableEq, Repr

inductive Polarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- A source-bound, licensed reading *after* semantic interpretation.
    A future runtime instantiation must establish that SLR's exact observations
    and the relevant admissibility review actually justify these fields. -/
structure SentenceReading where
  sourceRevision : String
  sourceSpan : String
  proposition : CallProposition
  scope : DiscourseScope
  polarity : Polarity
  deriving DecidableEq, Repr

def aliceCallsBob : CallProposition :=
  ⟨"Alice", "Bob"⟩

def directAssertion : SentenceReading :=
  ⟨"fixture:revision:1", "sentence:1", aliceCallsBob,
    .narratorAssertion, .positive⟩

def charlieBelief : SentenceReading :=
  ⟨"fixture:revision:1", "sentence:2", aliceCallsBob,
    .attributedBelief "Charlie", .positive⟩

def mistakenAppraisal : SentenceReading :=
  ⟨"fixture:revision:1", "sentence:2", aliceCallsBob,
    .narratorMistakeAssessment "Charlie", .positive⟩

def retrospectiveDenial : SentenceReading :=
  ⟨"fixture:revision:1", "sentence:3", aliceCallsBob,
    .narratorRetrospectiveCorrection, .negative⟩

def beforeCorrection : List SentenceReading :=
  [directAssertion, charlieBelief, mistakenAppraisal]

def afterCorrection : List SentenceReading :=
  beforeCorrection ++ [retrospectiveDenial]

/-- The embedded event proposition is identical despite distinct epistemic
    scopes and polarities. -/
theorem sameEmbeddedCall :
    charlieBelief.proposition = retrospectiveDenial.proposition := by
  rfl

/-- A source belief is not literally a source assertion of event occurrence. -/
theorem beliefNotDirectAssertion :
    charlieBelief.scope ≠ directAssertion.scope := by
  decide

/-- A mistaken-belief assessment and the later denial are different acts. -/
theorem appraisalNotCorrection :
    mistakenAppraisal.scope ≠ retrospectiveDenial.scope := by
  decide

/-- An added correction preserves earlier, attributed assertions. -/
theorem earlierBeliefRemains :
    charlieBelief ∈ afterCorrection := by
  simp [afterCorrection, beforeCorrection]

theorem mistakenAssessmentRemains :
    mistakenAppraisal ∈ afterCorrection := by
  simp [afterCorrection, beforeCorrection]

theorem laterDenialPresent :
    retrospectiveDenial ∈ afterCorrection := by
  simp [afterCorrection]

theorem conflictingPolarityIsDifferentScope :
    charlieBelief.scope ≠ retrospectiveDenial.scope ∧
    charlieBelief.polarity ≠ retrospectiveDenial.polarity := by
  decide

/-- A countermodel prevents the invalid inference:
    'Charlie believes the call happened' => 'the call happened'.
    The premise is about belief in a possible world, the conclusion about
    occurrence in that world. -/
structure PossibleWorld where
  callOccurred : Bool
  charlieBelievesCall : Bool
  narratorReportsNoCall : Bool
  narratorLabelsBeliefMistaken : Bool
  deriving Repr

theorem beliefDoesNotEntailOccurrence :
    ¬ (∀ w : PossibleWorld,
        w.charlieBelievesCall = true → w.callOccurred = true) := by
  intro h
  have impossible : false = true :=
    h ⟨false, true, true, true⟩ rfl
  cases impossible

/-- Even an explicit narrator correction cannot independently establish
    an event's historical non-occurrence: a source may itself be mistaken.
    An external evidence/admission argument is necessary. -/
theorem narratorCorrectionDoesNotEntailWorldFalsity :
    ¬ (∀ w : PossibleWorld,
        w.narratorReportsNoCall = true → w.callOccurred = false) := by
  intro h
  have impossible : true = false :=
    h ⟨true, true, true, true⟩ rfl
  cases impossible

/-- Nor does the phrase 'mistakenly thought' itself license an independent
    occurrence conclusion without an explicitly admitted interpretation. -/
theorem narratorMistakeAssessmentDoesNotEntailWorldFalsity :
    ¬ (∀ w : PossibleWorld,
        w.narratorLabelsBeliefMistaken = true → w.callOccurred = false) := by
  intro h
  have impossible : true = false :=
    h ⟨true, true, true, true⟩ rfl
  cases impossible

/-- Reading-relative document questions can be answered from the preserved
    source observations without conflating them with world-occurrence claims. -/
def mentionedCall (rs : List SentenceReading) (p : CallProposition) : Prop :=
  ∃ r, r ∈ rs ∧ r.proposition = p

theorem pageMentionsCall :
    mentionedCall afterCorrection aliceCallsBob := by
  exact ⟨charlieBelief, earlierBeliefRemains, rfl⟩

/-- A correction does not mutate the prior record: the two source spans
    can be reopened independently. -/
theorem beliefAndDenialKeepDistinctSpans :
    charlieBelief.sourceSpan ≠ retrospectiveDenial.sourceSpan := by
  decide

end Slr
end Wikidata
