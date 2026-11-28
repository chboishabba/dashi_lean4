import RequestProject.Slr.Producer

/-!
# Generic source-relative document-query soundness

The semantics are indexed by arbitrary source, interpretation, query and
answer types. This is the Lean consumer-side expression of the existing Agda
DASHI/Core/ConsumerDescentMinimalObserverExact and
DASHI/Reasoning/SemanticConsumerRelativeClosureExact laws.

This file deliberately does NOT implement another NLP semantics, reader,
admission service, or corpus ontology. In particular, SourceQueryLicence is
proof-relevant: the SLR JSON candidate producer cannot construct it merely
by returning a candidate or a string identifying a supposed review.

The later production weld must instantiate the model and discharge the
source-binding and interpretation-soundness obligations by independent,
checked evidence. An abstract proof under these premises is NOT a proof
that a particular article has been successfully interpreted.
-/

namespace Wikidata
namespace Slr

universe uSource uObservation uReading uQuery uAnswer

/-- The existing SLR producer supplies observations; existing SLR/DASHI
    interpretation and consumer owners supply the actual semantic maps.
    The model is not an alternative interpretation engine. -/
structure DocumentQueryModel
    (Source : Type uSource) (Observation : Type uObservation)
    (Reading : Type uReading) (Query : Type uQuery)
    (Answer : Type uAnswer) where
  observe : Source → Observation
  live : Observation → Reading → Prop
  documentAnswer : Source → Query → Answer
  readingAnswer : Reading → Query → Answer

/-- A proof-bearing semantic licence for a PARTICULAR source and query.
    Distinct queries can require different resolution strength.
    'consumerFactorises' is the real, currently unfilled correspondence;
    it cannot be inferred from parser output, QIDs, or a review-reference string.

    'closed' is consumer sufficiency on the live semantic fibre.
    No global unique reading is required. -/
structure SourceQueryLicence
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (source : Source) (query : Query) where
  observation : Observation
  sameProducedObservation : observation = m.observe source
  chosenReading : Reading
  chosenIsLive : m.live observation chosenReading
  consumerFactorises :
    ∀ otherSource : Source, m.observe otherSource = observation →
      m.documentAnswer otherSource query =
        m.readingAnswer chosenReading query
  consumerClosed :
    ∀ reading, m.live observation reading →
      m.readingAnswer reading query = m.readingAnswer chosenReading query

/-- No semantic answer depends on the arbitrary choice of a still-live
    reading when the consumer is closed. -/
theorem liveReadingQueryInvariant
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (reading : Reading)
    (live : m.live licence.observation reading) :
    m.readingAnswer reading query =
      m.readingAnswer licence.chosenReading query :=
  licence.consumerClosed reading live

/-- The original producer attachment is retained: a checked interpretation
    cannot silently substitute an unrelated observation at query time. -/
theorem licensedReadingBelongsToProducedObservation
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query) :
    m.live (m.observe source) licence.chosenReading := by
  rw [← licence.sameProducedObservation]
  exact licence.chosenIsLive

/-- The end-to-end *general* theorem. The checked evaluator's answer must
    itself be justified against the selected reading; it is not accepted on
    the authority of a mere external success flag. -/
theorem slrJmdDocumentQuerySound
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (answer : Answer)
    (checked : m.readingAnswer licence.chosenReading query = answer) :
    m.documentAnswer source query = answer :=
  (licence.consumerFactorises source licence.sameProducedObservation.symm).trans checked

/-- If a different reading remains live, a certified checked answer for it
    yields the SAME document answer. This is the actual consumer-relative
    adequacy law, not a requirement to resolve every ambiguity. -/
theorem slrJmdDocumentQuerySoundForAnyLiveReading
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (reading : Reading)
    (live : m.live licence.observation reading)
    (answer : Answer)
    (checked : m.readingAnswer reading query = answer) :
    m.documentAnswer source query = answer :=
  (licence.consumerFactorises source licence.sameProducedObservation.symm).trans
    ((licence.consumerClosed reading live).symm.trans checked)

/-- An actual pair of still-live readings with different answers is
    a constructive negative gate: no query licence can be formed for this
    observation without further refinement or changing the query. This is the
    consumer-relative WrongType/non-factorability failure mode. -/
theorem incompatibleLiveReadingsBlockQueryLicence
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (left right : Reading)
    (leftLive : m.live (m.observe source) left)
    (rightLive : m.live (m.observe source) right)
    (disagree : m.readingAnswer left query ≠ m.readingAnswer right query) :
    ¬ Nonempty (SourceQueryLicence m source query) := by
  intro h
  rcases h with ⟨licence⟩
  have hl : m.live licence.observation left := by
    simpa [licence.sameProducedObservation] using leftLive
  have hr : m.live licence.observation right := by
    simpa [licence.sameProducedObservation] using rightLive
  exact disagree ((licence.consumerClosed left hl).trans
    (licence.consumerClosed right hr).symm)

/-- A concrete source pair that collides under the observation but
    disagrees on this consumer is a negative witness to factorisation.
    This is the same DASHI non-factorability criterion that forbids loss
    of epistemic scope, speaker, temporal interpretation, or provenance
    when those distinctions matter to the query. -/
theorem sourceObservationCollisionBlocksQueryLicence
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    (left right : Source) (query : Query)
    (sameObservation : m.observe left = m.observe right)
    (differentAnswers :
      m.documentAnswer left query ≠ m.documentAnswer right query) :
    ¬ Nonempty (SourceQueryLicence m left query) := by
  intro h
  rcases h with ⟨licence⟩
  have hleft : m.observe left = licence.observation :=
    licence.sameProducedObservation.symm
  have hright : m.observe right = licence.observation :=
    sameObservation.symm.trans hleft
  exact differentAnswers
    ((licence.consumerFactorises left hleft).trans
      (licence.consumerFactorises right hright).symm)

/-- A smaller live fibre retains consumer closure, matching the generic
    DASHI semantic-refinement theorem. -/
theorem semanticClosurePreservedByRefinement
    {Observation : Type uObservation} {Reading : Type uReading}
    {Answer : Type uAnswer}
    (oldLive newLive : Observation → Reading → Prop)
    (consumer : Reading → Answer)
    (refines : ∀ o r, newLive o r → oldLive o r)
    (closed : ∀ o x y, oldLive o x → oldLive o y →
      consumer x = consumer y) :
    ∀ o x y, newLive o x → newLive o y →
      consumer x = consumer y := by
  intro o x y hx hy
  exact closed o x y (refines o x hx) (refines o y hy)


/-- Independent source licences compose without requiring a global unique
reading. The comparison is a consumer of the two independently licensed
answers, not a new identity or source-independence witness. -/
theorem bilateralLicensedComparison
    {S O R Q A T P U V B C : Type}
    {left : DocumentQueryModel S O R Q A}
    {right : DocumentQueryModel T P U V B}
    {s : S} {t : T} {q : Q} {v : V}
    (l : SourceQueryLicence left s q)
    (r : SourceQueryLicence right t v)
    (compare : A → B → C)
    (x : R) (y : U)
    (hx : left.live l.observation x)
    (hy : right.live r.observation y) :
    compare (left.readingAnswer x q) (right.readingAnswer y v) =
      compare (left.documentAnswer s q) (right.documentAnswer t v) := by
  rw [← slrJmdDocumentQuerySoundForAnyLiveReading l x hx _ rfl,
      ← slrJmdDocumentQuerySoundForAnyLiveReading r y hy _ rfl]

/-- Bidirectionality is a second evaluation with the argument order swapped,
not an assumption that a directional semantic licence is symmetric. -/
theorem reciprocalLicensedComparison
    {S O R Q A T P U V B C D : Type}
    {left : DocumentQueryModel S O R Q A}
    {right : DocumentQueryModel T P U V B}
    {s : S} {t : T} {q : Q} {v : V}
    (l : SourceQueryLicence left s q)
    (r : SourceQueryLicence right t v)
    (forward : A → B → C) (backward : B → A → D)
    (x : R) (y : U)
    (hx : left.live l.observation x)
    (hy : right.live r.observation y) :
    (forward (left.readingAnswer x q) (right.readingAnswer y v),
      backward (right.readingAnswer y v) (left.readingAnswer x q)) =
    (forward (left.documentAnswer s q) (right.documentAnswer t v),
      backward (right.documentAnswer t v) (left.documentAnswer s q)) := by
  rw [← slrJmdDocumentQuerySoundForAnyLiveReading l x hx _ rfl,
      ← slrJmdDocumentQuerySoundForAnyLiveReading r y hy _ rfl]


/-- A consumer-specific answer projection: this changes the answer algebra,
    not the observation or live fibre. Source factorisation and closure
    transport through the same map. It does not certify omitted queries. -/
def projectQueryAnswer
    {S O R Q A B : Type} (m : DocumentQueryModel S O R Q A)
    (project : A → B) : DocumentQueryModel S O R Q B where
  observe := m.observe
  live := m.live
  documentAnswer := fun s q => project (m.documentAnswer s q)
  readingAnswer := fun r q => project (m.readingAnswer r q)

def projectSourceQueryLicence
    {S O R Q A B : Type} {m : DocumentQueryModel S O R Q A}
    {s : S} {q : Q} (l : SourceQueryLicence m s q) (project : A → B) :
    SourceQueryLicence (projectQueryAnswer m project) s q where
  observation := l.observation
  sameProducedObservation := l.sameProducedObservation
  chosenReading := l.chosenReading
  chosenIsLive := l.chosenIsLive
  consumerFactorises := fun t h => congrArg project (l.consumerFactorises t h)
  consumerClosed := fun r h => congrArg project (l.consumerClosed r h)

/-- The exact compression cut: a query family factors through the retained
    coordinate if and only if every collision preserves all its answers.
    The section is supplied by the existing source/provenance inverse;
    this does not assert that an arbitrary summary has such a section. -/
theorem sectionedContextCompressionIff
    {S C Q A : Type} (compress : S → C) (expand : C → S)
    (hsection : ∀ c, compress (expand c) = c)
    (answer : S → Q → A) :
    (∃ compactAnswer : C → Q → A, ∀ s q, answer s q = compactAnswer (compress s) q) ↔
    (∀ s t, compress s = compress t → ∀ q, answer s q = answer t q) := by
  constructor
  · rintro ⟨f, hf⟩ s t h q
    rw [hf s q, hf t q, h]
  · intro h
    refine ⟨fun c q => answer (expand c) q, ?_⟩
    intro s q
    exact h s (expand (compress s)) (hsection (compress s)).symm q

/-- Reverse solve: if an omitted context coordinate separates two live
    sources on a requested query, no compressed answer can serve both. -/
theorem contextCollisionBlocksCompression
    {S C Q A : Type} (compress : S → C) (answer : S → Q → A)
    (s t : S) (q : Q) (collision : compress s = compress t)
    (different : answer s q ≠ answer t q) :
    ¬ (∃ compactAnswer : C → Q → A, ∀ x k, answer x k = compactAnswer (compress x) k) := by
  rintro ⟨f, hf⟩
  apply different
  rw [hf s q, hf t q, collision]

end Slr
end Wikidata

#print axioms Wikidata.Slr.sectionedContextCompressionIff
#print axioms Wikidata.Slr.contextCollisionBlocksCompression
#print axioms Wikidata.Slr.projectSourceQueryLicence
