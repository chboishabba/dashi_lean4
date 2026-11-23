import RequestProject.Slr.FiniteConsumerCertificate
import RequestProject.Slr.GwbConsumerFibreProof
import RequestProject.Slr.GwbNativeFibreReceipt
import RequestProject.Slr.Proof

/-!
GWB proof-composition cut.

Reuse the existing JMD original KB theorem, SLR query-soundness
theorem and source-checked GWB Rust semantic receipt. This is a
conditional *system-soundness* theorem, not a claim of historical
truth, production fibre coverage, or a semantic alignment that has
not been supplied.

Original JMD attribution: meta-introspector/RequestProject.Cli.Derive,
RequestProject.PropertyEngine; original SLR/DASHI sources remain the
semantic and runtime owners. No independent NLP semantics are defined.
-/

namespace Wikidata
namespace Slr
namespace GwbProofComposition

open FiniteConsumer

/-- The existing real GWB receipt is source-bound, but this alone does
not discharge any of the semantic closure premises below. -/
theorem originalObservationRemainsChecked
    {article : String} {source projection receipt : Lean.Json}
    (h : GwbNativeFibre.CheckedRealGwbNativeFibre
      article source projection receipt) :
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article source projection receipt = true :=
  GwbNativeFibre.checkedGwbFibreObservationsRetainResiduals h

/-- The proof-bearing endpoint for a finite semantic model. It uses the
EXISTING SLR consumer licence rather than a second interpretation engine.
Its hypothesis 'complete' is the real semantic gap: a finite Rust JSON
enumeration is not assumed to contain every production-live reading. -/
theorem checkedFiniteArticleAnswerSound
    {Source Observation Reading Query Answer : Type}
    [DecidableEq Reading] [DecidableEq Answer]
    (m : DocumentQueryModel Source Observation Reading Query Answer)
    (source : Source) (query : Query) (observation : Observation)
    (sameSource : observation = m.observe source)
    (enumeration : CompleteEnumeration m observation)
    (chosen : Reading) (chosenLive : m.live observation chosen)
    (sourceMeaning :
      ∀ otherSource, m.observe otherSource = observation →
        m.documentAnswer otherSource query =
          m.readingAnswer chosen query)
    (allSame : checkConstant enumeration.readings
      (fun reading => m.readingAnswer reading query) = true)
    (value : Answer)
    (evaluated : m.readingAnswer chosen query = value) :
    m.documentAnswer source query = value := by
  let licence :=
    licenceOfCompleteFiniteCheck m source query observation
      sameSource enumeration chosen chosenLive sourceMeaning allSame
  exact slrJmdDocumentQuerySound licence value evaluated

/-- A reviewed JMD property query gives a statement-of-the-imported-KB
witness. This proof is not a judgement about the historical event or the
textual meaning of a GWB sentence. -/
theorem checkedJmdPropertyStillKBRelative
    (question : ReviewedPropertyQuestion) :
    ∃ p, (p, question.subject, question.object) ∈
      question.pkb.stmts ∧
      question.pkb.isSubPropertyOf p question.property = true :=
  reviewedPropertySupportSound question

/-- Simultaneous, non-collapsing composition of an article-local semantic
answer and a JMD checked property: each result retains its OWN premises.
A separate checked semantic alignment is required before claiming the
two conclusions refer to the same world fact. -/
theorem independentArticleAndKBResultsSound
    {Source Observation Reading Query Answer : Type}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (answerValue : Answer)
    (answerChecked : m.readingAnswer licence.chosenReading query = answerValue)
    (property : ReviewedPropertyQuestion) :
    m.documentAnswer source query = answerValue ∧
    (∃ p, (p, property.subject, property.object) ∈
      property.pkb.stmts ∧
      property.pkb.isSubPropertyOf p property.property = true) := by
  exact ⟨slrJmdDocumentQuerySound licence answerValue answerChecked,
    reviewedPropertySupportSound property⟩

/-- Source-preserving annotation joins are monotone in each input. The
semantic reading can later be refined, while the provenance annotations
must stay accessible. -/
theorem joinRetainsLeftAnnotations {Meaning Metadata : Type}
    (a b : GwbConsumer.EvidenceFibre Meaning Metadata)
    (x : Metadata) (hx : a.annotations x) :
    (GwbConsumer.EvidenceFibre.join a b).annotations x :=
  Or.inl hx

theorem joinRetainsRightAnnotations {Meaning Metadata : Type}
    (a b : GwbConsumer.EvidenceFibre Meaning Metadata)
    (x : Metadata) (hx : b.annotations x) :
    (GwbConsumer.EvidenceFibre.join a b).annotations x :=
  Or.inr hx

end GwbProofComposition
end Slr
end Wikidata
