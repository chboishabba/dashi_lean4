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
  rcases witness with ⟨evidence, _⟩
  exact h ⟨evidence, trivial⟩

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


open Lean

namespace Wikidata.Slr.GwbNativeAntecedentMaxCut

private def stringField (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

private def natField (j : Json) (key : String) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD 0

private def trueField (j : Json) (key : String) : Bool :=
  (j.getObjValAs? Bool key).toOption.getD false

private def falseField (j : Json) (key : String) : Bool :=
  (j.getObjValAs? Bool key).toOption == some false

/-- Audit the *structural* bounded parser frontier emitted by the original
    SLR Rust/PG command. It cannot elevate a token, a surname or S29 status
    into a reviewed actor. Identity and external KB obligations remain open. -/
def checkBoundedFrontier (j : Json) : Bool :=
  let nominations := (j.getObjValAs? (Array Json) "nominations").toOption.getD #[]
  let focus := natField j "focus_start_char"
  let finish := natField j "focus_end_char"
  let start := natField j "nominated_source_anchor_start_char"
  let stop := natField j "nominated_source_anchor_end_char"
  let hasExactBush := nominations.any (fun n =>
    stringField n "surface" == "Bush" &&
    natField n "original_start_char" == 4310 &&
    natField n "original_end_char" == 4314 &&
    falseField n "semantic_admission_paid")
  stringField j "schema" == "slr-native-antecedent-bounded-frontier-v1" &&
  stringField j "canonical_content_sha256" ==
    "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30" &&
  stringField j "focus_surface" == "he" &&
  focus == 4534 && finish == 4536 &&
  start == 4310 && stop == 4314 && decide (stop ≤ focus) &&
  !(stringField j "source_revision_ref").isEmpty &&
  !(stringField j "review_item_ref").isEmpty &&
  !(stringField j "parser_run_ref").isEmpty &&
  !(stringField j "candidate_set_ref").isEmpty &&
  natField j "parser_nomination_count" == nominations.size &&
  natField j "original_regions_covered" == 5 &&
  trueField j "structural_region_coverage_complete" &&
  falseField j "semantic_candidate_exhaustiveness_paid" &&
  falseField j "local_antecedent_admission_paid" &&
  falseField j "external_qid_paid" &&
  falseField j "claim_truth_paid" &&
  stringField j "source_relative_answer" == "UNRESOLVED_REVIEW_REQUIRED" &&
  hasExactBush

structure CheckedBoundedFrontier (j : Json) where
  evidence : checkBoundedFrontier j = true

theorem checked_bounded_frontier_not_identity (j : Json)
    (checked : CheckedBoundedFrontier j) :
    checkBoundedFrontier j = true := checked.evidence

end Wikidata.Slr.GwbNativeAntecedentMaxCut

/-- The only acceptance marker is source/structural and consumer-boundary
    validation. It does not certify coreference, S29 reviewer action, QID,
    article alignment, event occurrence, claim truth or historical fact. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [frontierPath] =>
    let source ← IO.FS.readFile frontierPath
    match Lean.Json.parse source with
    | .error err =>
      IO.eprintln s!"GWB_NATIVE_FRONTIER_REJECTED: invalid JSON {err}"
      return 1
    | .ok json =>
      if h : Wikidata.Slr.GwbNativeAntecedentMaxCut.checkBoundedFrontier json = true then
        let checked : Wikidata.Slr.GwbNativeAntecedentMaxCut.CheckedBoundedFrontier json := ⟨h⟩
        let _ := Wikidata.Slr.GwbNativeAntecedentMaxCut.checked_bounded_frontier_not_identity json checked
        IO.println "GWB_NATIVE_FRONTIER_BOUNDARY_KERNEL_OK"
        IO.println "Book source/parser nominated frontier is bounded, nonpromoting, same-revision and unresolved"
        IO.println "Still open: typed accessibility, S29 judgment, local identity, Q23505, consumer-live coverage, JMD property"
        return 0
      else
        IO.eprintln "GWB_NATIVE_FRONTIER_REJECTED: source/digest/spans/nomination/nonpromotion mismatch"
        return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run DASHI/output-final_aristotle/RequestProject/Slr/GwbNativeAntecedentMaxCut.lean FRONTIER.json"
    return 2

#print axioms Wikidata.Slr.GwbNativeAntecedentMaxCut.licensed_source_answer
#print axioms Wikidata.Slr.GwbNativeAntecedentMaxCut.counterexample_blocks_licence
#print axioms Wikidata.Slr.GwbNativeAntecedentMaxCut.retraction_restores_original
#print axioms Wikidata.Slr.GwbNativeAntecedentMaxCut.no_cross_document_antecedent
