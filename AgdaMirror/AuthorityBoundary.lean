import Mathlib

/-!
# Lean mirror of `DASHI/Core/AuthorityBoundary.agda` (genuine interface + witness)

Faithful transcription of the authority-boundary bookkeeping:

* `AuthorityKind` — `CitationAuthority` vs `ArtifactAuthority` (distinct kinds),
* `AuthorityBoundary kind` — a kind-indexed boundary receipt whose stored kind is
  proven to match its index (`authorityKindMatches`),
* `CitationAuthorityNoArtifact` — the genuine boundary fact that a *citation*
  authority closes a source slot **without** authorizing a machine-readable
  artifact.

We give a genuine *witness* `citationOnly` exhibiting an accepted citation
boundary with both artifact flags `false`, packaged as a
`CitationAuthorityNoArtifact`.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.AuthorityBoundaries

/-- The two distinct authority kinds (Agda `data AuthorityKind`). -/
inductive AuthorityKind | CitationAuthority | ArtifactAuthority
  deriving DecidableEq, Repr

open AuthorityKind

/-- A kind-indexed authority boundary receipt (Agda `record AuthorityBoundary`). -/
structure AuthorityBoundary (kind : AuthorityKind) where
  authorityKind : AuthorityKind
  authorityKindMatches : authorityKind = kind
  recordIdentifier : String
  citation : String
  authorityAccepted : Bool
  artifactAuthority : Bool
  machineReadableArtifactPresent : Bool
  notes : List String

/-- A citation-kind boundary (Agda `CitationAuthorityBoundary`). -/
abbrev CitationAuthorityBoundary := AuthorityBoundary CitationAuthority

/-- An artifact-kind boundary (Agda `ArtifactAuthorityBoundary`). -/
abbrev ArtifactAuthorityBoundary := AuthorityBoundary ArtifactAuthority

/-- The genuine "citation closes a slot but authorizes no artifact" fact
(Agda `record CitationAuthorityNoArtifact`). -/
structure CitationAuthorityNoArtifact where
  citationBoundary : CitationAuthorityBoundary
  citationAuthorityAccepted : citationBoundary.authorityAccepted = true
  artifactAuthorityIsFalse : citationBoundary.artifactAuthority = false
  machineReadableArtifactPresentIsFalse :
    citationBoundary.machineReadableArtifactPresent = false

/-- Genuine witness: an accepted citation boundary with no artifact authority. -/
def citationOnly : CitationAuthorityNoArtifact where
  citationBoundary :=
    { authorityKind := CitationAuthority
      authorityKindMatches := rfl
      recordIdentifier := "rec-001"
      citation := "source citation"
      authorityAccepted := true
      artifactAuthority := false
      machineReadableArtifactPresent := false
      notes := [] }
  citationAuthorityAccepted := rfl
  artifactAuthorityIsFalse := rfl
  machineReadableArtifactPresentIsFalse := rfl

end AgdaMirror.AuthorityBoundaries


namespace AgdaMirror.AuthorityBoundaries

/-!
## Golden Agda safe/just and legal-governance mirror

Golden owners:

* `DASHI.Core.CompositionalComplianceExact`
* `DASHI.Governance.Fanning2022LiteralSituatedQualifiedUseBridgeExact`
* `DASHI.Unified.FleetFormalGapTargetTOEExact`
* `DASHI.EverythingTOESymmetryResolved369`
* `DASHI.Unifier`

Fanning, O'Neill, Hickel, and Roux retain source ownership for
"The social shortfall and ecological overshoot of nations",
Nature Sustainability 5 (2022), DOI 10.1038/s41893-021-00799-z.

Necula retains source attribution for CMU-CS-98-154.
No DOI is asserted here for that thesis.

Bitansky, Canetti, Chiesa, and Tromer retain source attribution for the
STOC 2013 proof-carrying-data composition result,
DOI 10.1145/2488608.2488623.

The structures and theorems below mirror the current Agda exports.
Agda remains the semantic owner.
-/

inductive EndpointOnlyCompositionCreatesCompliance : Prop

theorem endpointOnlyCompositionDoesNotCreateCompliance :
    ¬ EndpointOnlyCompositionCreatesCompliance := by
  intro h
  cases h

inductive OperationalRecordCreatesLegalAuthority : Prop

theorem operationalRecordDoesNotCreateLegalAuthority :
    ¬ OperationalRecordCreatesLegalAuthority := by
  intro h
  cases h

structure CompositionalComplianceBoundary where
  downstreamReceiptRetainsIntermediateWitness : Bool
  downstreamReceiptRetainsIntermediateWitnessIsTrue :
    downstreamReceiptRetainsIntermediateWitness = true
  endpointEqualityAloneCreatesCompliance : Bool
  endpointEqualityAloneCreatesComplianceIsFalse :
    endpointEqualityAloneCreatesCompliance = false
  sourceCitationAloneCreatesLegalAuthority : Bool
  sourceCitationAloneCreatesLegalAuthorityIsFalse :
    sourceCitationAloneCreatesLegalAuthority = false
  operationalRecordAloneCreatesLegalAuthority : Bool
  operationalRecordAloneCreatesLegalAuthorityIsFalse :
    operationalRecordAloneCreatesLegalAuthority = false

def canonicalCompositionalComplianceBoundary : CompositionalComplianceBoundary where
  downstreamReceiptRetainsIntermediateWitness := true
  downstreamReceiptRetainsIntermediateWitnessIsTrue := rfl
  endpointEqualityAloneCreatesCompliance := false
  endpointEqualityAloneCreatesComplianceIsFalse := rfl
  sourceCitationAloneCreatesLegalAuthority := false
  sourceCitationAloneCreatesLegalAuthorityIsFalse := rfl
  operationalRecordAloneCreatesLegalAuthority := false
  operationalRecordAloneCreatesLegalAuthorityIsFalse := rfl

structure FanningLiteralSituatedAuthorityBoundary where
  literalSourceReceiptSurvivesSituatedQualification : Bool
  literalSourceReceiptSurvivesSituatedQualificationIsTrue :
    literalSourceReceiptSurvivesSituatedQualification = true
  historicalObservationCanSilentlyBecomeBAUForecastEvidence : Bool
  historicalObservationCanSilentlyBecomeBAUForecastEvidenceIsFalse :
    historicalObservationCanSilentlyBecomeBAUForecastEvidence = false
  qualifiedLiteralResearchUseCreatesCausalAuthority : Bool
  qualifiedLiteralResearchUseCreatesCausalAuthorityIsFalse :
    qualifiedLiteralResearchUseCreatesCausalAuthority = false
  qualifiedLiteralResearchUseCreatesDecisionAuthority : Bool
  qualifiedLiteralResearchUseCreatesDecisionAuthorityIsFalse :
    qualifiedLiteralResearchUseCreatesDecisionAuthority = false
  thisModuleClaimsWorkbookAlreadyIngested : Bool
  thisModuleClaimsWorkbookAlreadyIngestedIsFalse :
    thisModuleClaimsWorkbookAlreadyIngested = false

def canonicalFanningLiteralSituatedAuthorityBoundary :
    FanningLiteralSituatedAuthorityBoundary where
  literalSourceReceiptSurvivesSituatedQualification := true
  literalSourceReceiptSurvivesSituatedQualificationIsTrue := rfl
  historicalObservationCanSilentlyBecomeBAUForecastEvidence := false
  historicalObservationCanSilentlyBecomeBAUForecastEvidenceIsFalse := rfl
  qualifiedLiteralResearchUseCreatesCausalAuthority := false
  qualifiedLiteralResearchUseCreatesCausalAuthorityIsFalse := rfl
  qualifiedLiteralResearchUseCreatesDecisionAuthority := false
  qualifiedLiteralResearchUseCreatesDecisionAuthorityIsFalse := rfl
  thisModuleClaimsWorkbookAlreadyIngested := false
  thisModuleClaimsWorkbookAlreadyIngestedIsFalse := rfl

inductive SensibLawRecordCreatesLegalAuthority : Prop

theorem sensibLawRecordDoesNotCreateLegalAuthority :
    ¬ SensibLawRecordCreatesLegalAuthority := by
  intro h
  cases h

inductive ActionstepRecordCreatesLegalAuthority : Prop

theorem actionstepRecordDoesNotCreateLegalAuthority :
    ¬ ActionstepRecordCreatesLegalAuthority := by
  intro h
  cases h

structure SafeJustLegalGovernanceBoundary where
  goldenAgdaOwnsFormalSemantics : Bool
  goldenAgdaOwnsFormalSemanticsIsTrue : goldenAgdaOwnsFormalSemantics = true
  sensibLawOperationalRecordCreatesLegalAuthority : Bool
  sensibLawOperationalRecordCreatesLegalAuthorityIsFalse :
    sensibLawOperationalRecordCreatesLegalAuthority = false
  actionstepOperationalRecordCreatesLegalAuthority : Bool
  actionstepOperationalRecordCreatesLegalAuthorityIsFalse :
    actionstepOperationalRecordCreatesLegalAuthority = false
  legalComplianceHandoffRequiresTypedIntermediateWitness : Bool
  legalComplianceHandoffRequiresTypedIntermediateWitnessIsTrue :
    legalComplianceHandoffRequiresTypedIntermediateWitness = true
  literalDataReceiptCreatesPolicyMandate : Bool
  literalDataReceiptCreatesPolicyMandateIsFalse :
    literalDataReceiptCreatesPolicyMandate = false
  discharged584FibresRetargeted : Bool
  discharged584FibresRetargetedIsFalse :
    discharged584FibresRetargeted = false
  only58UnformalisedFormalGapsRemainTargeted : Bool
  only58UnformalisedFormalGapsRemainTargetedIsTrue :
    only58UnformalisedFormalGapsRemainTargeted = true
  esdSurfaceEditedByThisLane : Bool
  esdSurfaceEditedByThisLaneIsFalse :
    esdSurfaceEditedByThisLane = false

def canonicalSafeJustLegalGovernanceBoundary : SafeJustLegalGovernanceBoundary where
  goldenAgdaOwnsFormalSemantics := true
  goldenAgdaOwnsFormalSemanticsIsTrue := rfl
  sensibLawOperationalRecordCreatesLegalAuthority := false
  sensibLawOperationalRecordCreatesLegalAuthorityIsFalse := rfl
  actionstepOperationalRecordCreatesLegalAuthority := false
  actionstepOperationalRecordCreatesLegalAuthorityIsFalse := rfl
  legalComplianceHandoffRequiresTypedIntermediateWitness := true
  legalComplianceHandoffRequiresTypedIntermediateWitnessIsTrue := rfl
  literalDataReceiptCreatesPolicyMandate := false
  literalDataReceiptCreatesPolicyMandateIsFalse := rfl
  discharged584FibresRetargeted := false
  discharged584FibresRetargetedIsFalse := rfl
  only58UnformalisedFormalGapsRemainTargeted := true
  only58UnformalisedFormalGapsRemainTargetedIsTrue := rfl
  esdSurfaceEditedByThisLane := false
  esdSurfaceEditedByThisLaneIsFalse := rfl

structure TOEZKPFrame where
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
  createsPhysicalPromotion : Bool
  createsHistoricalIdentity : Bool
  createsMonsterRecognition : Bool

def canonicalSafeJustLegalGovernanceZKPFrame : TOEZKPFrame where
  objective :=
    "O: converge literal safe-and-just evidence, legal compliance handoffs, and semantic non-promotion into the existing DASHI TOE"
  reuse :=
    "R: reuse the golden Agda Fanning literal bridge, compositional compliance owner, fleet formal-gap TOE owner, and TOE roots"
  construction :=
    "C: mirror aliases and exact boundary receipts only; do not create an independent Lean authority calculus"
  safetyInvariant :=
    "S: literal data does not create causal or decision authority; operational case records do not create legal authority; endpoint equality does not replace a typed intermediate witness"
  lane :=
    "L: one disjoint nonblocking governance-convergence lane; 584 discharged fibres stay outside the 58-gap target"
  preconditions :=
    "P: golden Agda owners exist; source identifiers remain stable; ESD surfaces are read-only"
  governance :=
    "G: ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma, and C4/PlantUML are process lenses only; meta-introspector attribution remains separate"
  postconditions :=
    "F: Lean mirrors the stable TOE and Unifier non-promotion surface without changing Agda ownership"
  verification :=
    "verify source parity, no sorry, no accidental ESD dependency, and run exact-head Lake build before claiming Lean kernel success"
  esdMutationAllowed := false
  createsPhysicalPromotion := false
  createsHistoricalIdentity := false
  createsMonsterRecognition := false

end AgdaMirror.AuthorityBoundaries


namespace AgdaMirror.AuthorityBoundaries

theorem goldenAgdaOwnershipPinned :
    canonicalSafeJustLegalGovernanceBoundary.goldenAgdaOwnsFormalSemantics = true := by
  rfl

theorem dischargedFleetFibresStayOutsideTarget :
    canonicalSafeJustLegalGovernanceBoundary.discharged584FibresRetargeted = false := by
  rfl

theorem onlyFormalGapFrontierRemainsTargeted :
    canonicalSafeJustLegalGovernanceBoundary.only58UnformalisedFormalGapsRemainTargeted = true := by
  rfl

/-!
## Settlement-mediated institutional norm transmission

This mirrors the golden Agda owner
`DASHI.Core.InstitutionalNormProductionExact`.

The mirror keeps party binding force, platform policy, competitor adoption,
industry convention, and generally binding law distinct.
-/

inductive NormativeReach where
  | partyBound
  | platformPolicy
  | competitorAdoption
  | industryConvention
  | generallyBindingLaw
  deriving DecidableEq, Repr

inductive AuthoritySource where
  | settlementAuthority
  | voluntaryPolicyAuthority
  | competitorPressureAuthority
  | legislativeAuthority
  | judicialHoldingAuthority
  deriving DecidableEq, Repr

structure SettlementTransmission where
  origin : NormativeReach
  platformSurface : NormativeReach
  competitorSurface : NormativeReach
  industrySurface : NormativeReach
  deriving Repr

def canonicalSettlementTransmission : SettlementTransmission where
  origin := .partyBound
  platformSurface := .platformPolicy
  competitorSurface := .competitorAdoption
  industrySurface := .industryConvention

inductive IndustryConventionCreatesFederalLaw : Prop
inductive SettlementCreatesSupremeCourtHolding : Prop
inductive SettlementCreatesConstitutionalPrecedent : Prop
inductive SameVisiblePolicyImpliesSameAuthoritySource : Prop

theorem industryConventionDoesNotCreateFederalLaw :
    ¬ IndustryConventionCreatesFederalLaw := by
  intro h
  cases h

theorem settlementDoesNotCreateSupremeCourtHolding :
    ¬ SettlementCreatesSupremeCourtHolding := by
  intro h
  cases h

theorem settlementDoesNotCreateConstitutionalPrecedent :
    ¬ SettlementCreatesConstitutionalPrecedent := by
  intro h
  cases h

theorem sameVisiblePolicyDoesNotImplySameAuthoritySource :
    ¬ SameVisiblePolicyImpliesSameAuthoritySource := by
  intro h
  cases h

structure SettlementTransmissionBoundary where
  settlementCanBindParties : Bool
  settlementCanBindPartiesIsTrue : settlementCanBindParties = true
  settlementAloneBindsCompetitors : Bool
  settlementAloneBindsCompetitorsIsFalse : settlementAloneBindsCompetitors = false
  competitorAdoptionCanConvergePolicy : Bool
  competitorAdoptionCanConvergePolicyIsTrue :
    competitorAdoptionCanConvergePolicy = true
  industryConventionIsFederalLaw : Bool
  industryConventionIsFederalLawIsFalse : industryConventionIsFederalLaw = false
  settlementIsSupremeCourtHolding : Bool
  settlementIsSupremeCourtHoldingIsFalse : settlementIsSupremeCourtHolding = false
  settlementIsConstitutionalPrecedent : Bool
  settlementIsConstitutionalPrecedentIsFalse :
    settlementIsConstitutionalPrecedent = false
  sameVisiblePolicyImpliesSameAuthority : Bool
  sameVisiblePolicyImpliesSameAuthorityIsFalse :
    sameVisiblePolicyImpliesSameAuthority = false
  productionHistoryRemainsRelevant : Bool
  productionHistoryRemainsRelevantIsTrue :
    productionHistoryRemainsRelevant = true

def canonicalSettlementTransmissionBoundary : SettlementTransmissionBoundary where
  settlementCanBindParties := true
  settlementCanBindPartiesIsTrue := rfl
  settlementAloneBindsCompetitors := false
  settlementAloneBindsCompetitorsIsFalse := rfl
  competitorAdoptionCanConvergePolicy := true
  competitorAdoptionCanConvergePolicyIsTrue := rfl
  industryConventionIsFederalLaw := false
  industryConventionIsFederalLawIsFalse := rfl
  settlementIsSupremeCourtHolding := false
  settlementIsSupremeCourtHoldingIsFalse := rfl
  settlementIsConstitutionalPrecedent := false
  settlementIsConstitutionalPrecedentIsFalse := rfl
  sameVisiblePolicyImpliesSameAuthority := false
  sameVisiblePolicyImpliesSameAuthorityIsFalse := rfl
  productionHistoryRemainsRelevant := true
  productionHistoryRemainsRelevantIsTrue := rfl

structure Meta2026SettlementNormCalibration where
  competitorAdoptionConditionsPartOfPaymentStructure : Bool
  competitorAdoptionConditionsPartOfPaymentStructureIsTrue :
    competitorAdoptionConditionsPartOfPaymentStructure = true
  officialMetaSourceStatesIndustryWideAdoptionAim : Bool
  officialMetaSourceStatesIndustryWideAdoptionAimIsTrue :
    officialMetaSourceStatesIndustryWideAdoptionAim = true
  settlementAloneLegallyBindsTikTokOrYouTube : Bool
  settlementAloneLegallyBindsTikTokOrYouTubeIsFalse :
    settlementAloneLegallyBindsTikTokOrYouTube = false
  settlementCreatesFederalStatute : Bool
  settlementCreatesFederalStatuteIsFalse :
    settlementCreatesFederalStatute = false
  settlementCreatesSupremeCourtHolding : Bool
  settlementCreatesSupremeCourtHoldingIsFalse :
    settlementCreatesSupremeCourtHolding = false
  jmdPosterCreatesLegalAuthority : Bool
  jmdPosterCreatesLegalAuthorityIsFalse :
    jmdPosterCreatesLegalAuthority = false

def canonicalMeta2026SettlementNormCalibration :
    Meta2026SettlementNormCalibration where
  competitorAdoptionConditionsPartOfPaymentStructure := true
  competitorAdoptionConditionsPartOfPaymentStructureIsTrue := rfl
  officialMetaSourceStatesIndustryWideAdoptionAim := true
  officialMetaSourceStatesIndustryWideAdoptionAimIsTrue := rfl
  settlementAloneLegallyBindsTikTokOrYouTube := false
  settlementAloneLegallyBindsTikTokOrYouTubeIsFalse := rfl
  settlementCreatesFederalStatute := false
  settlementCreatesFederalStatuteIsFalse := rfl
  settlementCreatesSupremeCourtHolding := false
  settlementCreatesSupremeCourtHoldingIsFalse := rfl
  jmdPosterCreatesLegalAuthority := false
  jmdPosterCreatesLegalAuthorityIsFalse := rfl

theorem metaSettlementDoesNotBindCompetitors :
    canonicalMeta2026SettlementNormCalibration.settlementAloneLegallyBindsTikTokOrYouTube = false := by
  rfl

theorem metaSettlementDoesNotCreateFederalStatute :
    canonicalMeta2026SettlementNormCalibration.settlementCreatesFederalStatute = false := by
  rfl

theorem jmdPosterDoesNotCreateLegalAuthority :
    canonicalMeta2026SettlementNormCalibration.jmdPosterCreatesLegalAuthority = false := by
  rfl

def canonicalSettlementNormTransmissionZKPFrame : TOEZKPFrame where
  objective :=
    "O: formalize settlement-mediated norm transmission without promoting convergence into generally binding law"
  reuse :=
    "R: mirror the golden Agda institutional norm owner and existing TOE governance handoff"
  construction :=
    "C: mirror only the stable boundary and non-promotion receipts"
  safetyInvariant :=
    "S: party obligation, platform policy, competitor adoption, industry convention, and generally binding law remain distinct"
  lane :=
    "L: one disjoint governance lane; the 584 discharged fibres remain outside the 58-gap target"
  preconditions :=
    "P: a settlement source, party scope, policy surface, and authority source are typed before downstream claims"
  governance :=
    "G: process standards are governance lenses only; they do not create legal or theorem authority"
  postconditions :=
    "F: same visible policy does not imply the same authority source; convergence does not create federal law"
  verification :=
    "Lean mirrors Agda only; exact-head kernel verification is required before claiming Lean success"
  esdMutationAllowed := false
  createsPhysicalPromotion := false
  createsHistoricalIdentity := false
  createsMonsterRecognition := false

end AgdaMirror.AuthorityBoundaries
