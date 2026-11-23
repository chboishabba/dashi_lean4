import Lean

/-!
# Native source-grounded anaphor maximum cut

This proves the *consumer-relative* soundness contract and exact separation
of source, review workflow, local antecedent proof, and external QID.

It DOES NOT manufacture the premises from parser tokens, original C4.12 S29
Pending state, semantic label strings or JMD Q207 entity labels. The runtime
frontier is a bounded original-parser nomination set, not a globally exhaustive
set of language interpretations.

Authoritative origins:
- SLR: original PostgreSQL source, M12 parser, S29 and resolution receipts
- SensibLaw binding_candidate_sets: accessibility/morph compatibility reference
- JMD: independently pinned QID, statement and KB-support proof
- This Lean module: exact conditional implication and negative boundaries.
-/

namespace Wikidata
namespace Slr
namespace GwbNativeAntecedentMaxCut

/-- Source identity requires both original document AND source revision.
    A shared surname, QID, source work or parser token is not enough. -/
structure SourceRevision where
  documentRef : String
  revisionRef : String
  deriving Repr, DecidableEq, BEq

def SameSource (a b : SourceRevision) : Prop :=
  a.documentRef = b.documentRef ∧ a.revisionRef = b.revisionRef

theorem no_cross_document_antecedent
    {a b : SourceRevision} (h : a.documentRef ≠ b.documentRef) :
    ¬ SameSource a b := by
  intro same
  exact h same.1

theorem no_cross_revision_antecedent
    {a b : SourceRevision} (h : a.revisionRef ≠ b.revisionRef) :
    ¬ SameSource a b := by
  intro same
  exact h same.2

structure OriginalMention where
  source : SourceRevision
  statementRef : String
  regionRef : String
  startChar : Nat
  endChar : Nat
  surface : String
  deriving Repr

/-- This is structural source evidence, not a pronoun identity theorem. -/
structure SameSourcePrecedent (focus candidate : OriginalMention) : Prop where
  sameSource : SameSource focus.source candidate.source
  precedes : candidate.endChar ≤ focus.startChar
  candidateValid : candidate.startChar < candidate.endChar
  focusValid : focus.startChar < focus.endChar

/-- An S29 workflow receipt has no local identity authority by definition.
    The distinct semantic receipt must be supplied explicitly. -/
structure WorkflowReview where
  sourceReviewItemRef : String
  commandRef : String
  reviewerRef : String
  statusAccepted : Bool
  deriving Repr

structure SemanticResolutionEvidence (focus candidate : OriginalMention) where
  originalPrecedent : SameSourcePrecedent focus candidate
  candidateSetRef : String
  accessibilityWitnessRef : String
  competitorDispositionWitnessRefs : List String
  policyRef : String
  resolverRef : String
  semanticReviewRef : String
  /-- A distinct check supplied by the admitted source-local owner. -/
  semanticAdmission : Prop
  paid : semanticAdmission

/-- A candidate row and even an S29 Accept never synthesize the paid field
    of SemanticResolutionEvidence. -/
theorem workflow_does_not_supply_semantic_evidence
    (w : WorkflowReview) (focus candidate : OriginalMention)
    (h : ¬ ∃ _ : SemanticResolutionEvidence focus candidate, True) :
    ¬ ∃ _ : SemanticResolutionEvidence focus candidate, w.statusAccepted = true := by
  intro witness
  exact h ⟨witness.1, trivial⟩

/-- Existing source Level-1 is retained; Level-3 is an optional *separate*
    projection, not a destructive rewrite of original source coordinates. -/
structure ReversibleLocalProjection where
  levelOne : OriginalMention
  levelThreeReferent : Option String
  semanticResolutionRef : Option String
  deriving Repr

def projectLocal (premise : OriginalMention)
    (referent resolutionRef : Option String) : ReversibleLocalProjection :=
  ⟨premise, referent, resolutionRef⟩

def retractLocal (projection : ReversibleLocalProjection) :
    ReversibleLocalProjection :=
  { projection with
      levelThreeReferent := none
      semanticResolutionRef := none }

theorem levelOne_preserved (premise : OriginalMention)
    (referent resolutionRef : Option String) :
    (projectLocal premise referent resolutionRef).levelOne = premise := rfl

theorem retraction_restores_original
    (premise : OriginalMention) (referent resolutionRef : Option String) :
    retractLocal (projectLocal premise referent resolutionRef) =
      projectLocal premise none none := rfl

/-- Consumer-specific completeness over all *live* readings is a separate
    payment. A bounded parser-nomination enumeration cannot instantiate it
    by itself. -/
def ConsumerCoverage {Reading : Type} (live : Reading → Prop)
    (enumerated : List Reading) : Prop :=
  ∀ r, live r → r ∈ enumerated

def ConsumerInvariant {Reading Answer : Type} (enumerated : List Reading)
    (evaluate : Reading → Answer) (answer : Answer) : Prop :=
  ∀ r, r ∈ enumerated → evaluate r = answer

/-- This is the exact consumer certificate: once the independent scope
    coverage and pointwise invariance witnesses exist, the value is justified
    for any actual live reading within the declared scope. -/
theorem licensed_source_answer
    {Reading Answer : Type}
    (live : Reading → Prop) (enumerated : List Reading)
    (evaluate : Reading → Answer) (answer : Answer)
    (coverage : ConsumerCoverage live enumerated)
    (invariant : ConsumerInvariant enumerated evaluate answer) :
    ∀ r, live r → evaluate r = answer := by
  intro r belongs
  exact invariant r (coverage r belongs)

/-- If even one live admissible reading contradicts the claimed value,
    the claim cannot possess a valid consumer-coverage/invariance pair. -/
theorem counterexample_blocks_licence
    {Reading Answer : Type}
    (live : Reading → Prop) (enumerated : List Reading)
    (evaluate : Reading → Answer) (answer : Answer)
    (rival : Reading) (rivalIsLive : live rival)
    (contradiction : evaluate rival ≠ answer) :
    ¬ (ConsumerCoverage live enumerated ∧
       ConsumerInvariant enumerated evaluate answer) := by
  intro pair
  exact contradiction (licensed_source_answer live enumerated
    evaluate answer pair.1 pair.2 rival rivalIsLive)

/-- A resolved local actor is not a world QID. Property/KB support must
    carry its own pinned revision and independent JMD proof. -/
structure ExternalKBWitness where
  wikidataQid : String
  wikidataRevisionRef : String
  statementRef : String
  propertyRef : String
  checkerRef : String
  deriving Repr

structure ReviewedArticlePropertyAlignment where
  articleSource : SourceRevision
  originalStatementRef : String
  articleSubjectRef : String
  kb : ExternalKBWitness
  independentAlignment : Prop
  alignmentPaid : independentAlignment

/-- A Q207 book-reader mismatch is concrete and decidable. -/
example : ("Q207" : String) ≠ "Q23505" := by decide

/-- The actual GWB Wikipedia source and GHWB book source are unequal. -/
example :
    ("a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233" : String)
    ≠ "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30" := by
  decide

end GwbNativeAntecedentMaxCut
end Slr
end Wikidata
