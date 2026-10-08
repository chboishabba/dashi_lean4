namespace Dashi.Biology.AutismVaccineClaimPromotionAuditExact

inductive ClaimSpeaker where
  | unidentifiedOct2026Speaker
  | hbomberguy
  | wakefield
  | brianDeer
  | quotedJournalist
  | quotedParent
  | quotedPaper
  | externalScientificSource
  | dashiSynthesis
  deriving Repr, DecidableEq

inductive SourceSurface where
  | oct2026Transcript
  | measuredResponseTranscript
  | wakefieldLancet1998
  | lancetRetraction2010
  | bmjFraudInvestigation2011
  | hviidDanishCohort2019
  | cochraneMMRReview2020
  | microbiomeTransferOpenLabelStudy
  | pronounDepressionMetaEvidence
  | synchronyBondingEvidence
  | otherExternalEvidence
  deriving Repr, DecidableEq

inductive ClaimKind where
  | fundingPurposeClaim
  | biomedicalAssociationClaim
  | causalMechanismClaim
  | interventionClaim
  | diagnosisClaim
  | individualPsychologyClaim
  | socialPropagationClaim
  | mediaRepresentationClaim
  | conflictOfInterestClaim
  | publicHealthClaim
  deriving Repr, DecidableEq

inductive ClaimStatus where
  | sourceReportedOnly
  | supportedBounded
  | associationOnly
  | mechanismHypothesisOnly
  | domainBridgeMissing
  | blockedPromotion
  | independentlyCorroborated
  | unsupported
  deriving Repr, DecidableEq

structure AttributedClaim where
  claimKey : String
  claimSpeaker : ClaimSpeaker
  sourceSurface : SourceSurface
  claimKind : ClaimKind
  boundedReading : String
  status : ClaimStatus
  attributionBoundary : String
  deriving Repr, DecidableEq

def octGrantFramingClaim : AttributedClaim := {
  claimKey := "oct26-grant-depathologisation-framing"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .fundingPurposeClaim
  boundedReading := "The speaker frames the Australian $455,000 Reframing Autism grant as taxpayer funding to depathologise autism."
  status := .blockedPromotion
  attributionBoundary := "Amount/recipient and speaker framing remain separate from the government's stated programme purpose."
}

def octGlymphaticAutismClaim : AttributedClaim := {
  claimKey := "oct26-glymphatic-autism-severity"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .biomedicalAssociationClaim
  boundedReading := "The speaker links autism severity to impaired glymphatic clearance and then to dementia risk."
  status := .associationOnly
  attributionBoundary := "Imaging association and population dementia-risk observations do not create a causal chain."
}

def octEndogenousOpioidClaim : AttributedClaim := {
  claimKey := "oct26-endogenous-opioid-autism"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .causalMechanismClaim
  boundedReading := "The speaker proposes impaired endogenous-opioid-system function as an autism mechanism and uses it to explain an advocate's distress."
  status := .blockedPromotion
  attributionBoundary := "Mechanistic hypothesis does not license individual neurochemical diagnosis from language or advocacy."
}

def octFMTAutismClaim : AttributedClaim := {
  claimKey := "oct26-fmt-removes-autism-diagnosis"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .interventionClaim
  boundedReading := "The speaker treats microbiota-transfer results as evidence that autism diagnoses can disappear after FMT."
  status := .blockedPromotion
  attributionBoundary := "Uncontrolled multicomponent intervention and symptom-scale cutoff do not establish FMT-specific diagnosis removal."
}

def octPronounDepressionClaim : AttributedClaim := {
  claimKey := "oct26-pronoun-count-depression"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .individualPsychologyClaim
  boundedReading := "The speaker treats first-person-pronoun frequency in a short quotation as a strong indicator of depression/defence cascade."
  status := .blockedPromotion
  attributionBoundary := "Weak group correlation does not provide an individual diagnostic classifier."
}

def octSynchronyFalseBeliefClaim : AttributedClaim := {
  claimKey := "oct26-synchrony-endorphin-false-belief"
  claimSpeaker := .unidentifiedOct2026Speaker
  sourceSurface := .oct2026Transcript
  claimKind := .individualPsychologyClaim
  boundedReading := "The speaker moves from synchronised bonding to the claim that people confuse pleasurable synchrony with proposition truth."
  status := .blockedPromotion
  attributionBoundary := "Bonding and pain-threshold evidence does not identify proposition truth or false-belief formation."
}

def hbombMMRNoLinkClaim : AttributedClaim := {
  claimKey := "hbomb-mmr-autism-no-link"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .biomedicalAssociationClaim
  boundedReading := "The video states that large subsequent studies do not support an MMR-autism link."
  status := .independentlyCorroborated
  attributionBoundary := "Independent cohort/review evidence remains separately attributed."
}

def hbombWakefieldRetractionClaim : AttributedClaim := {
  claimKey := "hbomb-wakefield-paper-retracted"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .publicHealthClaim
  boundedReading := "The video states that the 1998 Lancet paper was retracted."
  status := .independentlyCorroborated
  attributionBoundary := "The video claim is separate from the Lancet/BMJ retraction record."
}

def hbombParentalRecallBoundaryClaim : AttributedClaim := {
  claimKey := "hbomb-parental-temporal-attribution"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .biomedicalAssociationClaim
  boundedReading := "The video emphasizes that the original timing signal depended substantially on parental attribution of symptom onset after vaccination."
  status := .supportedBounded
  attributionBoundary := "Temporal sequence is represented without causal promotion."
}

def wakefieldGutOpioidMechanismClaim : AttributedClaim := {
  claimKey := "wakefield-gut-morphine-like-autism-mechanism"
  claimSpeaker := .wakefield
  sourceSurface := .measuredResponseTranscript
  claimKind := .causalMechanismClaim
  boundedReading := "Wakefield is quoted proposing a gut-derived morphine-like dietary product mechanism linking vaccine-associated intestinal pathology to autism."
  status := .blockedPromotion
  attributionBoundary := "Wakefield-attributed mechanism; no validated same-object causal chain is imported."
}

def hbombMediaAmplificationClaim : AttributedClaim := {
  claimKey := "hbomb-media-amplification-vaccine-fear"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .socialPropagationClaim
  boundedReading := "The video argues that repeated media coverage amplified MMR-autism concern and vaccine hesitancy."
  status := .mechanismHypothesisOnly
  attributionBoundary := "Population media-exposure -> belief -> uptake causation requires its own design."
}

def hbombAutismRepresentationClaim : AttributedClaim := {
  claimKey := "hbomb-autism-tragedy-representation"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .mediaRepresentationClaim
  boundedReading := "The video criticises media selection of extreme suffering cases and tragedy framing of autism, and argues for accommodation."
  status := .sourceReportedOnly
  attributionBoundary := "Normative/media-analysis claim; not biomedical vaccine-safety evidence."
}

def hbombConflictOfInterestClaim : AttributedClaim := {
  claimKey := "hbomb-wakefield-conflict-of-interest"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .conflictOfInterestClaim
  boundedReading := "The video attributes litigation, patent and business conflicts to Wakefield."
  status := .independentlyCorroborated
  attributionBoundary := "Conflict evidence and biomedical no-association evidence remain separate."
}

def hbombFraudClaim : AttributedClaim := {
  claimKey := "hbomb-wakefield-fraud"
  claimSpeaker := .hbomberguy
  sourceSurface := .measuredResponseTranscript
  claimKind := .publicHealthClaim
  boundedReading := "The video characterises the Wakefield paper as fraudulent and discusses discrepancies in cases, pathology and recruitment."
  status := .independentlyCorroborated
  attributionBoundary := "Independent BMJ investigation remains a separate source owner."
}

inductive EvidenceShape where
  | governmentProgrammeDescription
  | imagingAssociation
  | populationCohort
  | systematicReview
  | uncontrolledMulticomponentIntervention
  | caseReport
  | languageCorrelation
  | socialSynchronyExperiment
  | regulatoryRetractionRecord
  | investigativeRecord
  deriving Repr, DecidableEq

structure EvidenceReceipt where
  evidenceKey : String
  evidenceSource : SourceSurface
  evidenceShape : EvidenceShape
  paidClaim : String
  evidenceBoundary : String
  causalAuthority : Bool
  deriving Repr, DecidableEq

def hviid2019Receipt : EvidenceReceipt := {
  evidenceKey := "hviid-2019-danish-mmr-autism"
  evidenceSource := .hviidDanishCohort2019
  evidenceShape := .populationCohort
  paidClaim := "Nationwide Danish cohort: MMR vaccination was not associated with increased autism risk in the studied population."
  evidenceBoundary := "Population observational no-association evidence; not a universal zero-risk theorem."
  causalAuthority := false
}

def cochrane2020Receipt : EvidenceReceipt := {
  evidenceKey := "cochrane-2020-mmr-autism"
  evidenceSource := .cochraneMMRReview2020
  evidenceShape := .systematicReview
  paidClaim := "Review evidence found no evidence of increased autism risk after MMR/MMRV/MMR+V vaccination in the included studies."
  evidenceBoundary := "Bounded to included designs/populations and the MMR/autism safety question."
  causalAuthority := false
}

def lancetRetractionReceipt : EvidenceReceipt := {
  evidenceKey := "lancet-2010-retraction"
  evidenceSource := .lancetRetraction2010
  evidenceShape := .regulatoryRetractionRecord
  paidClaim := "The Lancet retracted the 1998 Wakefield paper in 2010."
  evidenceBoundary := "Publication/governance fact, not the epidemiologic causal estimate."
  causalAuthority := false
}

def bmjFraudReceipt : EvidenceReceipt := {
  evidenceKey := "bmj-2011-fraud-investigation"
  evidenceSource := .bmjFraudInvestigation2011
  evidenceShape := .investigativeRecord
  paidClaim := "BMJ investigation characterised the Wakefield article as fraudulent and documented discrepancies/conflicts."
  evidenceBoundary := "Pays misconduct/fraud claims; epidemiologic no-association remains separately sourced."
  causalAuthority := false
}

def fmtExploratoryReceipt : EvidenceReceipt := {
  evidenceKey := "fmt-autism-exploratory-multicomponent"
  evidenceSource := .microbiomeTransferOpenLabelStudy
  evidenceShape := .uncontrolledMulticomponentIntervention
  paidClaim := "Small open-label microbiota-transfer programme reported durable symptom-scale changes in the followed cohort."
  evidenceBoundary := "No randomised control; multicomponent package; symptom cutoff != diagnosis removal."
  causalAuthority := false
}

def pronounCorrelationReceipt : EvidenceReceipt := {
  evidenceKey := "first-person-pronoun-negative-emotionality"
  evidenceSource := .pronounDepressionMetaEvidence
  evidenceShape := .languageCorrelation
  paidClaim := "First-person singular language has a small group-level association with depressive symptoms/negative emotionality in pooled evidence."
  evidenceBoundary := "Not an individual diagnostic classifier."
  causalAuthority := false
}

def synchronyBondingReceipt : EvidenceReceipt := {
  evidenceKey := "social-synchrony-bonding-pain-threshold"
  evidenceSource := .synchronyBondingEvidence
  evidenceShape := .socialSynchronyExperiment
  paidClaim := "Synchronised group activity can increase bonding and pain-threshold measures used as indirect opioid proxies."
  evidenceBoundary := "Does not measure proposition truth or demonstrate false-belief formation."
  causalAuthority := false
}

structure BoundPromotionReceipt (claim : AttributedClaim) (evidence : EvidenceReceipt) where
  claimObjectReference : String
  evidenceObjectReference : String
  targetObjectReference : String
  sameObjectBindingReference : String
  sameObjectBound : Bool
  causalIdentificationReference : String
  causalIdentificationBound : Bool
  deriving Repr, DecidableEq

inductive PromotionEdge where
  | grantRecipientToGrantPurpose
  | biologicalAssociationToCausalMechanism
  | groupAssociationToIndividualDiagnosis
  | autismToOpioidDeficit
  | opioidHypothesisToIndividualDistress
  | fmtPackageToFMTSpecificEffect
  | symptomCutoffToDiagnosisRemoval
  | pronounCorrelationToIndividualDepression
  | synchronyToFalseBelief
  | temporalSequenceToVaccineCausation
  | caseSeriesToPopulationCausalEffect
  | conflictOfInterestToBiomedicalNull
  | mediaRepetitionToBiomedicalTruth
  | autismRepresentationToVaccineSafety
  | populationEvidenceToBoundedNoAssociation
  deriving Repr, DecidableEq

inductive EdgeStatus where
  | paidBounded
  | candidateOnly
  | domainBridgeRequired
  | blockedPromotion
  deriving Repr, DecidableEq

structure EdgeAudit where
  edge : PromotionEdge
  edgeStatus : EdgeStatus
  edgeReason : String
  deriving Repr, DecidableEq

def vaccineToAutismEdge : EdgeAudit := {
  edge := .temporalSequenceToVaccineCausation
  edgeStatus := .blockedPromotion
  edgeReason := "Parental temporal attribution does not identify an MMR -> autism causal effect; large population evidence independently fails to support the association."
}

def caseSeriesPopulationEdge : EdgeAudit := {
  edge := .caseSeriesToPopulationCausalEffect
  edgeStatus := .blockedPromotion
  edgeReason := "A 12-child uncontrolled case series cannot identify a population causal effect."
}

def fmtToDiagnosisRemovalEdge : EdgeAudit := {
  edge := .symptomCutoffToDiagnosisRemoval
  edgeStatus := .blockedPromotion
  edgeReason := "Symptom-scale cutoff after an uncontrolled multicomponent intervention is not diagnosis removal."
}

def fmtSpecificEffectEdge : EdgeAudit := {
  edge := .fmtPackageToFMTSpecificEffect
  edgeStatus := .blockedPromotion
  edgeReason := "A multicomponent intervention cannot attribute observed change specifically to FMT without component-identifying design evidence."
}

def pronounIndividualEdge : EdgeAudit := {
  edge := .pronounCorrelationToIndividualDepression
  edgeStatus := .blockedPromotion
  edgeReason := "Weak group-level language correlation does not identify an individual's depression state."
}

def synchronyToFalseBeliefEdge : EdgeAudit := {
  edge := .synchronyToFalseBelief
  edgeStatus := .blockedPromotion
  edgeReason := "Bonding/opioid-proxy effects do not identify proposition truth or false-belief formation."
}

def conflictBiomedicalEdge : EdgeAudit := {
  edge := .conflictOfInterestToBiomedicalNull
  edgeStatus := .blockedPromotion
  edgeReason := "Conflict/misconduct evidence does not itself prove the biomedical null."
}

def mediaTruthEdge : EdgeAudit := {
  edge := .mediaRepetitionToBiomedicalTruth
  edgeStatus := .blockedPromotion
  edgeReason := "Media repetition may alter salience/belief but cannot determine biomedical truth."
}

def autismRepresentationSafetyEdge : EdgeAudit := {
  edge := .autismRepresentationToVaccineSafety
  edgeStatus := .blockedPromotion
  edgeReason := "Autism-representation critique is socially relevant but not vaccine-safety evidence."
}

def boundedPopulationNoAssociationEdge : EdgeAudit := {
  edge := .populationEvidenceToBoundedNoAssociation
  edgeStatus := .paidBounded
  edgeReason := "Large cohort and systematic-review evidence pay a bounded MMR/autism no-association conclusion."
}

inductive TemporalSequenceCreatesVaccineCausationPermission : Prop
inductive SymptomCutoffCreatesDiagnosisRemovalPermission : Prop
inductive PronounCountCreatesIndividualDiagnosisPermission : Prop
inductive SynchronyCreatesFalseBeliefPermission : Prop
inductive ConflictCreatesBiomedicalNullPermission : Prop
inductive MediaRepetitionCreatesBiomedicalTruthPermission : Prop
inductive RepresentationCritiqueCreatesVaccineSafetyPermission : Prop

theorem temporalSequenceDoesNotCreateVaccineCausation : TemporalSequenceCreatesVaccineCausationPermission → False := by intro h; cases h
theorem symptomCutoffDoesNotCreateDiagnosisRemoval : SymptomCutoffCreatesDiagnosisRemovalPermission → False := by intro h; cases h
theorem pronounCountDoesNotCreateIndividualDiagnosis : PronounCountCreatesIndividualDiagnosisPermission → False := by intro h; cases h
theorem synchronyDoesNotCreateFalseBelief : SynchronyCreatesFalseBeliefPermission → False := by intro h; cases h
theorem conflictDoesNotCreateBiomedicalNull : ConflictCreatesBiomedicalNullPermission → False := by intro h; cases h
theorem mediaRepetitionDoesNotCreateBiomedicalTruth : MediaRepetitionCreatesBiomedicalTruthPermission → False := by intro h; cases h
theorem representationCritiqueDoesNotCreateVaccineSafety : RepresentationCritiqueCreatesVaccineSafetyPermission → False := by intro h; cases h

structure WakefieldCaseSeriesSurface where
  sampleSize : Nat
  hasConcurrentControlGroup : Bool
  parentalTemporalAttributionRepresented : Bool
  populationCausalEstimandIdentified : Bool
  paperRetracted : Bool
  independentPopulationNoAssociationEvidenceExists : Bool
  deriving Repr, DecidableEq

def canonicalWakefieldCaseSeriesSurface : WakefieldCaseSeriesSurface := {
  sampleSize := 12
  hasConcurrentControlGroup := false
  parentalTemporalAttributionRepresented := true
  populationCausalEstimandIdentified := false
  paperRetracted := true
  independentPopulationNoAssociationEvidenceExists := true
}

structure FMTAutismStudySurface where
  openLabel : Bool
  randomizedControl : Bool
  multicomponentTreatment : Bool
  symptomScaleObserved : Bool
  symptomScaleCutoffIsFormalDiagnosticRemoval : Bool
  fmtComponentSpecificCausalEffectIdentified : Bool
  deriving Repr, DecidableEq

def canonicalFMTAutismStudySurface : FMTAutismStudySurface := {
  openLabel := true
  randomizedControl := false
  multicomponentTreatment := true
  symptomScaleObserved := true
  symptomScaleCutoffIsFormalDiagnosticRemoval := false
  fmtComponentSpecificCausalEffectIdentified := false
}

structure InformationPropagationBoundary where
  sourceAuthorityCanChangeBelief : Bool
  repetitionCanChangeSalience : Bool
  mediaExposureCanBeCausalResearchQuestion : Bool
  repetitionDeterminesTruth : Bool
  authorityDeterminesTruth : Bool
  biomedicalTruthDeterminesEthicalRepresentation : Bool
  ethicalRepresentationDeterminesBiomedicalTruth : Bool
  deriving Repr, DecidableEq

def canonicalInformationPropagationBoundary : InformationPropagationBoundary := {
  sourceAuthorityCanChangeBelief := true
  repetitionCanChangeSalience := true
  mediaExposureCanBeCausalResearchQuestion := true
  repetitionDeterminesTruth := false
  authorityDeterminesTruth := false
  biomedicalTruthDeterminesEthicalRepresentation := false
  ethicalRepresentationDeterminesBiomedicalTruth := false
}

structure CrossPollinationMap where
  attributionOwner : String
  genericImplicationConeOwner : String
  causalIdentificationOwner : String
  causalEstimandOwner : String
  observerPluralityOwner : String
  traumaMemoryDecisionOwner : String
  informationPropagationOwner : String
  biologyPromotionOwner : String
  reading : String
  deriving Repr, DecidableEq

def canonicalCrossPollinationMap : CrossPollinationMap := {
  attributionOwner := "DASHI.Core.AttributedSourceCore"
  genericImplicationConeOwner := "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
  causalIdentificationOwner := "DASHI.Biology.CausalIdentificationFamiliesExact"
  causalEstimandOwner := "DASHI.Biology.CausalEffectEstimandExact"
  observerPluralityOwner := "DASHI.Biology.AliceBrownThreadInquirySynthesisExact / multi-observer machinery"
  traumaMemoryDecisionOwner := "existing trauma-memory-learning-decision machinery"
  informationPropagationOwner := "existing cognitive-warfare/FIMI and source-provenance machinery"
  biologyPromotionOwner := "DASHI.Biology.GABAPhenotypeEvidenceExact / GABAPhenotypeBridgeExact"
  reading := "Reuse attribution, implication, causal-ID, observer and propagation owners; add only domain receipts and same-object promotion boundaries."
}

structure AutismVaccineAuditBoundary where
  sourceVoicesSeparated : Bool
  sourceReportCreatesTruth : Bool
  independentEvidenceKeptSeparate : Bool
  associationCreatesCausation : Bool
  symptomCutoffEqualsDiagnosisRemoval : Bool
  pronounCountDiagnosesIndividual : Bool
  synchronyCreatesFalseBelief : Bool
  conflictOfInterestProvesBiomedicalNull : Bool
  mediaPropagationDeterminesBiomedicalTruth : Bool
  autismRepresentationDeterminesVaccineSafety : Bool
  mmrAutismNoAssociationBoundedEvidenceRepresented : Bool
  sameObjectBindingRequiredForPromotion : Bool
  deriving Repr, DecidableEq

def canonicalAuditBoundary : AutismVaccineAuditBoundary := {
  sourceVoicesSeparated := true
  sourceReportCreatesTruth := false
  independentEvidenceKeptSeparate := true
  associationCreatesCausation := false
  symptomCutoffEqualsDiagnosisRemoval := false
  pronounCountDiagnosesIndividual := false
  synchronyCreatesFalseBelief := false
  conflictOfInterestProvesBiomedicalNull := false
  mediaPropagationDeterminesBiomedicalTruth := false
  autismRepresentationDeterminesVaccineSafety := false
  mmrAutismNoAssociationBoundedEvidenceRepresented := true
  sameObjectBindingRequiredForPromotion := true
}

end Dashi.Biology.AutismVaccineClaimPromotionAuditExact
