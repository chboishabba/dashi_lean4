/-!
# Australian contracts reviewed-hop compiler mirror

Golden owner:
`dashi_agda/DASHI/Law/AustralianContractsReviewedHopCompilerExact.agda`.

This Lean module mirrors the finite control surface only.
It does not replace the Agda owner.
It does not create legal authority.
It does not create a current-law conclusion.
It does not edit or depend on an ESD surface.

Source attribution remains with the original legal authorities and source authors.
DASHI owns this normalization and non-promotion boundary.
Ibrahim and meta-introspector ownership remains unchanged.
-/

namespace AgdaMirror.Law.AustralianContractsReviewedHopCompiler

inductive PropositionEvidenceDisposition
  | supports
  | contests
  | contextOnly
  deriving DecidableEq, Repr

inductive ReviewedHopDisposition
  | appendCandidateDelta
  | retainReviewedResidual
  deriving DecidableEq, Repr

def propositionDisposition : PropositionEvidenceDisposition → ReviewedHopDisposition
  | .supports => .appendCandidateDelta
  | .contests => .retainReviewedResidual
  | .contextOnly => .retainReviewedResidual

theorem supports_may_append :
    propositionDisposition .supports = .appendCandidateDelta := rfl

theorem contests_remain_residual :
    propositionDisposition .contests = .retainReviewedResidual := rfl

theorem context_only_remains_residual :
    propositionDisposition .contextOnly = .retainReviewedResidual := rfl

inductive CitationUseStatus
  | mentioned
  | quoted
  | reliedOn
  | adopted
  | applied
  | followed
  | distinguished
  | criticised
  | rejected
  | overruled
  | partySubmission
  | historicalBackground
  | unresolved
  deriving DecidableEq, Repr

inductive ContractTreatment
  | supports
  | applies
  | follows
  | distinguishes
  | displaces
  deriving DecidableEq, Repr

def citationUseTreatment : CitationUseStatus → Option ContractTreatment
  | .applied => some .applies
  | .followed => some .follows
  | .distinguished => some .distinguishes
  | .adopted => some .supports
  | .reliedOn => some .supports
  | .overruled => some .displaces
  | .mentioned => none
  | .quoted => none
  | .criticised => none
  | .rejected => none
  | .partySubmission => none
  | .historicalBackground => none
  | .unresolved => none

theorem followed_maps_to_follows :
    citationUseTreatment .followed = some .follows := rfl

theorem mention_does_not_create_treatment :
    citationUseTreatment .mentioned = none := rfl

theorem quotation_does_not_create_treatment :
    citationUseTreatment .quoted = none := rfl

structure ReviewedDocumentAlias where
  sourceDocumentReference : String
  semanticAuthorityReference : String
  reviewerReference : String
  candidateOnly : Bool := true
  createsLegalAuthority : Bool := false
  deriving Repr

structure ReviewedContractsMaxCutBoundary where
  rawSourceNeedsIdentityReview : Bool
  sourceIdentityNeedsExactRevisionBinding : Bool
  propositionSupportNeedsReviewedPayment : Bool
  citationTreatmentNeedsReviewedUse : Bool
  contestedAndContextRemainResidual : Bool
  reviewedResidualsSurviveTrajectory : Bool
  acceptedHopForcesFrontierRecompute : Bool
  qidMayScheduleButCannotPromote : Bool
  createsLegalAuthority : Bool
  createsCurrentLawConclusion : Bool
  deriving Repr

def canonicalMaxCut : ReviewedContractsMaxCutBoundary where
  rawSourceNeedsIdentityReview := true
  sourceIdentityNeedsExactRevisionBinding := true
  propositionSupportNeedsReviewedPayment := true
  citationTreatmentNeedsReviewedUse := true
  contestedAndContextRemainResidual := true
  reviewedResidualsSurviveTrajectory := true
  acceptedHopForcesFrontierRecompute := true
  qidMayScheduleButCannotPromote := true
  createsLegalAuthority := false
  createsCurrentLawConclusion := false

theorem reviewed_residuals_survive :
    canonicalMaxCut.reviewedResidualsSurviveTrajectory = true := rfl

theorem accepted_hop_recomputes :
    canonicalMaxCut.acceptedHopForcesFrontierRecompute = true := rfl

theorem no_legal_authority :
    canonicalMaxCut.createsLegalAuthority = false := rfl

theorem no_current_law_conclusion :
    canonicalMaxCut.createsCurrentLawConclusion = false := rfl

def dischargedCoreKnowledgeFibres : Nat := 584
def polarityContradictionGaps : Nat := 44
def unformalisedFormalGaps : Nat := 58

theorem discharged_count_is_584 :
    dischargedCoreKnowledgeFibres = 584 := rfl

theorem contradiction_count_is_44 :
    polarityContradictionGaps = 44 := rfl

theorem formal_gap_budget_is_58 :
    unformalisedFormalGaps = 58 := rfl

structure ZKPFrame where
  objective : String
  reuse : String
  construction : String
  safetyInvariant : String
  lane : String
  preconditions : String
  governance : String
  postconditions : String
  verification : String
  esdMutationAllowed : Bool
  createsLegalAuthority : Bool
  createsCurrentLawConclusion : Bool
  deriving Repr

def canonicalZKPFrame : ZKPFrame where
  objective :=
    "O: close pinned Australian primary source to reviewed adaptive S14 residual recomputation"
  reuse :=
    "R: reuse OALC, review, non-promotion, adaptive residual, Pareto, snowball, attribution and fleet owners"
  construction :=
    "C: require reviewed identity before trace alias and reviewed proposition or citation use before a positive edge"
  safetyInvariant :=
    "S: acquisition, lexical match, QID, citation occurrence and ranking remain candidate or residual state"
  lane :=
    "L: one disjoint legal reviewed-hop lane; accepted hops append provenance and recompute the frontier"
  preconditions :=
    "P: exact source revision and reviewer evidence exist; discharged fibres remain excluded"
  governance :=
    "G: preserve source, DASHI, Ibrahim and meta-introspector attribution; ESD remains read-only"
  postconditions :=
    "F: emit candidate nodes or reviewed edges plus residuals; emit no legal authority or current-law conclusion"
  verification :=
    "duplicate search; exact identity binding; non-promotion; residual preservation; TOE reachability; kernel check"
  esdMutationAllowed := false
  createsLegalAuthority := false
  createsCurrentLawConclusion := false

theorem zkp_esd_read_only :
    canonicalZKPFrame.esdMutationAllowed = false := rfl

theorem zkp_no_legal_authority :
    canonicalZKPFrame.createsLegalAuthority = false := rfl

theorem zkp_no_current_law :
    canonicalZKPFrame.createsCurrentLawConclusion = false := rfl



structure RuntimeParityBoundary where
  corroboratingReviewUnitsMayDeduplicateToOneSemanticHop : Bool
  allSupportingReviewProvenanceIsRetained : Bool
  unsupportedReviewedResidualsSurviveDeduplication : Bool
  paidIdentityWorkMayResurrectAsFreshSourceWork : Bool
  paidTreatmentWorkMayResurrectAsFreshTreatmentWork : Bool
  frontierClosureMeansFormalConsumerAdequacy : Bool
  runtimeCoverageIsFormalFactorsThroughProof : Bool
  theoremBackedAdequacyRequiresActualWitness : Bool
  genericKernelAcceptsOnlyReviewedDelta : Bool
  genericKernelMayConvertRawSourceToReviewedDelta : Bool
  recursiveCampaignRecomputesAfterAcceptedHop : Bool
  recursiveCampaignUsesFixedUpfrontQueue : Bool
  recursiveResearchPriorityIsLegalTruthRank : Bool
  recursiveCampaignIsBudgetBounded : Bool
  createsLegalAuthority : Bool
  createsCurrentLawConclusion : Bool
  deriving Repr

def canonicalRuntimeParity : RuntimeParityBoundary where
  corroboratingReviewUnitsMayDeduplicateToOneSemanticHop := true
  allSupportingReviewProvenanceIsRetained := true
  unsupportedReviewedResidualsSurviveDeduplication := true
  paidIdentityWorkMayResurrectAsFreshSourceWork := false
  paidTreatmentWorkMayResurrectAsFreshTreatmentWork := false
  frontierClosureMeansFormalConsumerAdequacy := false
  runtimeCoverageIsFormalFactorsThroughProof := false
  theoremBackedAdequacyRequiresActualWitness := true
  genericKernelAcceptsOnlyReviewedDelta := true
  genericKernelMayConvertRawSourceToReviewedDelta := false
  recursiveCampaignRecomputesAfterAcceptedHop := true
  recursiveCampaignUsesFixedUpfrontQueue := false
  recursiveResearchPriorityIsLegalTruthRank := false
  recursiveCampaignIsBudgetBounded := true
  createsLegalAuthority := false
  createsCurrentLawConclusion := false

theorem dedup_retains_provenance :
    canonicalRuntimeParity.allSupportingReviewProvenanceIsRetained = true := rfl

theorem paid_treatment_does_not_resurrect :
    canonicalRuntimeParity.paidTreatmentWorkMayResurrectAsFreshTreatmentWork = false := rfl

theorem closed_frontier_is_not_formal_adequacy :
    canonicalRuntimeParity.frontierClosureMeansFormalConsumerAdequacy = false := rfl

theorem runtime_coverage_is_not_factors_through :
    canonicalRuntimeParity.runtimeCoverageIsFormalFactorsThroughProof = false := rfl

theorem generic_kernel_accepts_reviewed_delta_only :
    canonicalRuntimeParity.genericKernelAcceptsOnlyReviewedDelta = true := rfl

theorem recursive_campaign_recomputes :
    canonicalRuntimeParity.recursiveCampaignRecomputesAfterAcceptedHop = true := rfl

end AgdaMirror.Law.AustralianContractsReviewedHopCompiler
