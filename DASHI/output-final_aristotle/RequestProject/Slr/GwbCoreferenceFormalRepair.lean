import Lean
import RequestProject.Slr.NumericPnfRustPortContract

/-!
GWB native semantic repair.

Source coordinates -> original typed and complete antecedent candidate set
-> independent S29 review plus semantic admission -> unique local referent
-> source-local consumer agreement. No automatic world/QID identity.

The original 27 parser nominations and 25 spans do not establish coverage.
A 64-member binder cap requires a proof about omitted candidates.
All non-computational original-source, typed-resolution and reviewer
payments are explicit, rather than manufactured from parser flags.
-/

namespace Wikidata.Slr.GwbCoreferenceFormalRepair

structure SourceKey where
  documentRef : String
  sourceRevisionRef : String
  deriving Repr, DecidableEq, BEq

structure Mention where
  source : SourceKey
  statementRef : String
  regionRef : String
  startChar : Nat
  endChar : Nat
  surface : String
  deriving Repr

def SameOriginalSpan (a b : Mention) : Prop :=
  a.source = b.source ∧
  a.statementRef = b.statementRef ∧
  a.regionRef = b.regionRef ∧
  a.startChar = b.startChar ∧
  a.endChar = b.endChar

/-- Same physical span across token/NER channels is only source co-location. -/
theorem colocated_observations_share_coordinates
    {a b : Mention} (h : SameOriginalSpan a b) :
    a.source = b.source ∧ a.startChar = b.startChar ∧
      a.endChar = b.endChar := by
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Scope has one immutable source revision and a declared live referent
    domain; merely listing candidates cannot prove the domain complete. -/
structure ScopedFrontier (Factor : Type) where
  originalSource : SourceKey
  focus : Mention
  candidates : List Factor
  isLive : Factor → Prop
  focusOriginal : focus.source = originalSource

def ScopedCoverage {Factor : Type} (f : ScopedFrontier Factor) : Prop :=
  ∀ c, f.isLive c → c ∈ f.candidates

/-- If an omitted candidate is live, the finite binder frontier is NOT
    complete, regardless of nearest surface, list length or reviewer choice. -/
theorem omitted_live_candidate_blocks_coverage
    {Factor : Type} (f : ScopedFrontier Factor) (omitted : Factor)
    (live : f.isLive omitted) (notListed : omitted ∉ f.candidates) :
    ¬ ScopedCoverage f := by
  intro coverage
  exact notListed (coverage omitted live)

/-- Coreference is a reviewed equivalence of referents; distinct factor
    references and duplicate token/NER rows do not establish or refute it. -/
structure ReviewedDispositions {Factor : Type}
    (f : ScopedFrontier Factor) (chosen : Factor) where
  chosenMember : chosen ∈ f.candidates
  chosenLive : f.isLive chosen
  sameActor : Factor → Factor → Prop
  refl : ∀ x, sameActor x x
  symm : ∀ x y, sameActor x y → sameActor y x
  trans : ∀ x y z, sameActor x y → sameActor y z → sameActor x z
  everySurvivingFactor :
    ∀ c, c ∈ f.candidates → f.isLive c → sameActor c chosen

inductive S29Status where
  | pending | accepted | rejected | needsEvidence | qualified | abstained
  deriving Repr, DecidableEq

/-- Workflow acceptance and separately proven source-local semantic
    authority must BOTH exist; checked receipt provenance is an
    independent premise supplied by the original owner. -/
structure GovernedSemanticPayment (status : S29Status) where
  workflowAccepted : status = .accepted
  originalS29CommandRef : String
  originalReviewItemRef : String
  reviewerRef : String
  policyRef : String
  resolverRef : String
  typedCandidateSetRef : String
  independentSemanticOwnerCheck : Prop
  semanticProof : independentSemanticOwnerCheck

theorem pending_s29_cannot_pay :
    ¬ Nonempty (GovernedSemanticPayment .pending) := by
  intro witness
  cases witness with
  | intro payment => cases payment.workflowAccepted

theorem rejected_s29_cannot_pay :
    ¬ Nonempty (GovernedSemanticPayment .rejected) := by
  intro witness
  cases witness with
  | intro payment => cases payment.workflowAccepted

/-- Original SLR supports a separate deterministic reviewed-policy
    authority. The policy must be actual source/revision-bound evidence,
    not a name-proximity guess or a magic JSON success flag. -/
structure DeterministicPolicyPayment where
  policyRef : String
  sourceRevisionRef : String
  resolverRef : String
  originalEvidenceCheck : Prop
  evidenceProof : originalEvidenceCheck
  reviewedPolicyCheck : Prop
  policyProof : reviewedPolicyCheck

/-- The earlier formal proof model accidentally required human S29 for ALL
    source-local resolution. That was overconstrained: SLR has two distinct
    semantic-admission authority routes. -/
inductive SourceLocalResolutionAuthority (status : S29Status) where
  | byHuman : GovernedSemanticPayment status →
      SourceLocalResolutionAuthority status
  | byDeterministicPolicy : DeterministicPolicyPayment →
      SourceLocalResolutionAuthority status

theorem deterministic_policy_need_not_wait_for_s29
    (policy : DeterministicPolicyPayment) :
    Nonempty (SourceLocalResolutionAuthority .pending) :=
  ⟨.byDeterministicPolicy policy⟩

/-- A source-local named-topic inference is weaker than institutionally
    admitted, all-live coreference: it can name Bush under a bounded,
    source-checked convention without fabricating full semantic coverage. -/
structure ScopedLinguisticInference (Factor : Type) where
  source : SourceKey
  focus : Mention
  selected : Factor
  algorithmRef : String
  boundedSourceEvidence : Prop
  evidenceChecked : boundedSourceEvidence
  humanReviewRequired : Bool := false

theorem bounded_linguistic_answer_available
    {Factor : Type} (inference : ScopedLinguisticInference Factor) :
    ∃ selected : Factor, selected = inference.selected :=
  ⟨inference.selected, rfl⟩

structure ResolvedSourceLocal
    {Factor : Type} (f : ScopedFrontier Factor)
    (chosen : Factor) (status : S29Status) where
  coverage : ScopedCoverage f
  dispositions : ReviewedDispositions f chosen
  governed : SourceLocalResolutionAuthority status

/-- Positive result is unique up to reviewed same-local-actor equivalence,
    not equality of two Bush strings or two distinct span positions. -/
theorem unique_source_local_referent
    {Factor : Type} {f : ScopedFrontier Factor}
    {chosen : Factor} {status : S29Status}
    (paid : ResolvedSourceLocal f chosen status) :
    ∀ c, f.isLive c →
      paid.dispositions.sameActor c chosen := by
  intro c live
  exact paid.dispositions.everySurvivingFactor c
    (paid.coverage c live) live

/-- A consumer gets a source-relative stable answer only if evaluating two
    reviewed equivalent local actors yields the same answer. -/
theorem all_surviving_readings_agree
    {Factor Answer : Type} {f : ScopedFrontier Factor}
    {chosen : Factor} {status : S29Status}
    (paid : ResolvedSourceLocal f chosen status)
    (evaluate : Factor → Answer)
    (congruent :
      ∀ x y, paid.dispositions.sameActor x y →
        evaluate x = evaluate y) :
    ∀ r, f.isLive r → evaluate r = evaluate chosen := by
  intro r live
  exact congruent r chosen (unique_source_local_referent paid r live)

/-- A genuine live rival with another answer defeats an unjustified
    source-relative licence, including a convenient surname-first answer. -/
theorem rival_reading_blocks_answer
    {Factor Answer : Type} (f : ScopedFrontier Factor)
    (chosen rival : Factor) (evaluate : Factor → Answer)
    (liveRival : f.isLive rival)
    (differentAnswer : evaluate rival ≠ evaluate chosen) :
    ¬ (∀ r, f.isLive r → evaluate r = evaluate chosen) := by
  intro invariant
  exact differentAnswer (invariant rival liveRival)

/-- Level-3 substitution is separate and reversible, preserving the
    exact Level-1 immutable source premise. -/
structure LevelThree (Factor : Type) where
  original : Mention
  localReferent : Option Factor
  semanticPaymentRef : Option String

def retract {Factor : Type} (p : LevelThree Factor) : LevelThree Factor :=
  { p with localReferent := none, semanticPaymentRef := none }

theorem retract_preserves_original {Factor : Type} (p : LevelThree Factor) :
    (retract p).original = p.original := rfl

theorem retract_clears_semantic_payment {Factor : Type}
    (p : LevelThree Factor) :
    (retract p).localReferent = none ∧
    (retract p).semanticPaymentRef = none := ⟨rfl, rfl⟩

/-- Original JMD/entity-data evidence remains an independent property
    and world-identity payment, not a field on the local referent. -/
structure IndependentWorldBridge where
  originalSource : SourceKey
  originalLocalActorRef : String
  pinnedExternalQid : String
  externalRevisionRef : String
  JmdStatementRef : String
  independentExternalAuthority : Prop
  externalProof : independentExternalAuthority

theorem q207_is_not_q23505 :
    ("Q207" : String) ≠ "Q23505" := by decide

theorem book_is_not_wikipedia_source :
    ("7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30" : String) ≠
    ("a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233" : String) := by
  decide

/-- Weld the existing numeric typed selection to the original
    source-scoped coreference coverage contract. This does not construct
    a governed payment or conflate a class with an occurrence. -/
theorem numeric_selection_pays_original_scoped_coverage
    (f : ScopedFrontier NumericPnfRustPortContract.CandidateKey)
    (chosen : NumericPnfRustPortContract.CandidateKey)
    (cert : NumericPnfRustPortContract.ExactTypedSelection
      f.isLive f.candidates chosen) :
    ScopedCoverage f := cert.complete

/-- Reuse the original scoped-live-rival obstruction, rather than
    interpreting a bounded numeric candidate list as exhaustive. -/
theorem original_omitted_rival_blocks_numeric_selection
    (f : ScopedFrontier NumericPnfRustPortContract.CandidateKey)
    (chosen rival : NumericPnfRustPortContract.CandidateKey)
    (live : f.isLive rival) (omitted : rival ∉ f.candidates) :
    ¬ Nonempty (NumericPnfRustPortContract.ExactTypedSelection
      f.isLive f.candidates chosen) := by
  intro h
  obtain ⟨cert⟩ := h
  exact omitted_live_candidate_blocks_coverage f rival live omitted
    (numeric_selection_pays_original_scoped_coverage f chosen cert)

/-- Exact independent current authority is a proof-bearing binding, not
a digest or a successful generic source kernel check. The existing governed
resolution remains the semantic owner. -/
structure CurrentFocusOwnerProof {Factor : Type}
    (f : ScopedFrontier Factor) (chosen : Factor) (status : S29Status)
    (currentBinding : String) where
  issuedBinding : String
  exactBinding : issuedBinding = currentBinding
  resolution : ResolvedSourceLocal f chosen status

theorem current_focus_owner_proof_pays_exact_scope
    {Factor : Type} {f : ScopedFrontier Factor} {chosen : Factor}
    {status : S29Status} {binding : String}
    (proof : CurrentFocusOwnerProof f chosen status binding) :
    proof.issuedBinding = binding ∧ ScopedCoverage f ∧
      (∀ c, f.isLive c → proof.resolution.dispositions.sameActor c chosen) := by
  exact ⟨proof.exactBinding, proof.resolution.coverage,
    unique_source_local_referent proof.resolution⟩

theorem foreign_focus_binding_cannot_pay
    {Factor : Type} {f : ScopedFrontier Factor} {chosen : Factor}
    {status : S29Status} {binding : String}
    (proof : CurrentFocusOwnerProof f chosen status binding)
    (other : String) (changed : other ≠ binding) :
    proof.issuedBinding ≠ other := by
  intro eq
  exact changed (eq.symm.trans proof.exactBinding)


/-- The same packet cannot be both the candidate-only warm replay and
the closed authority endpoint. Acceptance must join separate evidence,
never weaken either predicate to make a Boolean conjunction pass. -/
theorem candidate_replay_cannot_be_closed
    (outsideModelPossible governedIdentityPaid : Bool)
    (candidate : outsideModelPossible = true ∧ governedIdentityPaid = false) :
    ¬ (outsideModelPossible = false ∧ governedIdentityPaid = true) := by
  intro closed
  have impossible : true = false := candidate.1.symm.trans closed.1
  cases impossible

/-- A historical candidate execution receipt can establish execution
parity, not current semantic authority. Its exact source and complete
implementation/scope coordinate must agree with the independently
checked governed lane. Full relation parity and inverse replay are
independent premises, not inferred from a supplied-prefix comparator.
The current owner proof supplies the actual all-live consumer result. -/
theorem joined_endpoint_lanes_pay_scoped_consumer
    {Factor Answer : Type} {f : ScopedFrontier Factor}
    {chosen : Factor} {status : S29Status} {binding : String}
    (candidateSource : SourceKey) (sameSource : candidateSource = f.originalSource)
    (candidateScope currentScope : String) (sameScope : candidateScope = currentScope)
    (candidateExecution wholeRelationParity inverseReplay : Prop)
    (candidateChecked : candidateExecution)
    (relationChecked : wholeRelationParity) (inverseChecked : inverseReplay)
    (owner : CurrentFocusOwnerProof f chosen status binding)
    (evaluate : Factor → Answer)
    (congruent : ∀ x y, owner.resolution.dispositions.sameActor x y →
      evaluate x = evaluate y) :
    candidateSource = f.originalSource ∧ candidateScope = currentScope ∧
      candidateExecution ∧ wholeRelationParity ∧ inverseReplay ∧
      ScopedCoverage f ∧ (∀ r, f.isLive r → evaluate r = evaluate chosen) := by
  exact ⟨sameSource, sameScope, candidateChecked, relationChecked, inverseChecked,
    owner.resolution.coverage, all_surviving_readings_agree owner.resolution evaluate congruent⟩

end Wikidata.Slr.GwbCoreferenceFormalRepair

#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.omitted_live_candidate_blocks_coverage
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.pending_s29_cannot_pay
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.deterministic_policy_need_not_wait_for_s29
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.bounded_linguistic_answer_available
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.unique_source_local_referent
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.all_surviving_readings_agree
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.rival_reading_blocks_answer
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.retract_preserves_original

#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.numeric_selection_pays_original_scoped_coverage
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.original_omitted_rival_blocks_numeric_selection

#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.current_focus_owner_proof_pays_exact_scope
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.foreign_focus_binding_cannot_pay

#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.candidate_replay_cannot_be_closed
#print axioms Wikidata.Slr.GwbCoreferenceFormalRepair.joined_endpoint_lanes_pay_scoped_consumer
