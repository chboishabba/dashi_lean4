namespace Dashi.Biology.GABAPhenotypeEvidenceExact

structure LiteratureSource where
  authors : String
  title : String
  venue : String
  year : Nat
  doi : String
  role : String
  deriving Repr, DecidableEq

def schmitz2017Source : LiteratureSource := {
  authors := "Thomas W. Schmitz; Michael C. Correia; Catarina S. Ferreira; Adrian Prescot; Michael C. Anderson"
  title := "Hippocampal GABA enables inhibitory control over unwanted thoughts"
  venue := "Nature Communications 8:1311"
  year := 2017
  doi := "10.1038/s41467-017-00956-z"
  role := "healthy-young-adult hippocampal GABA / Think-No-Think association; does not establish emotion suppression or diagnostic causation"
}

def autismGABAMetaAnalysis2024Source : LiteratureSource := {
  authors := "systematic-review / meta-analysis source registry row"
  title := "GABA concentration in autism spectrum disorder: a systematic review and meta-analysis of proton magnetic resonance spectroscopy studies"
  venue := "2024 systematic review and meta-analysis"
  year := 2024
  doi := "PMID:38796123"
  role := "group-level autism/GABA synthesis; heterogeneous regional and methodological evidence, not causal sufficiency"
}

def ptsdGABA2013Source : LiteratureSource := {
  authors := "PTSD magnetic-resonance-spectroscopy study source registry row"
  title := "Reduced GABA in the anterior insula in posttraumatic stress disorder"
  venue := "2013 magnetic resonance spectroscopy study"
  year := 2013
  doi := "PMID:23861191"
  role := "regional PTSD/GABA association fixture; does not define PTSD by GABA level"
}

def ptsdMRSReview2022Source : LiteratureSource := {
  authors := "systematic-review source registry row"
  title := "Magnetic resonance spectroscopy in post-traumatic stress disorder: an updated systematic review"
  venue := "2022 systematic review"
  year := 2022
  doi := "PMID:36237981"
  role := "cross-study heterogeneity boundary for PTSD metabolite claims"
}

inductive PopulationKind where
  | healthyYoungAdults
  | autisticParticipants
  | adhdParticipants
  | ptsdParticipants
  | mixedOrMetaAnalyticPopulation
  deriving Repr, DecidableEq

inductive BrainRegion where
  | hippocampus
  | sensorimotorCortex
  | medialPrefrontalCortex
  | anteriorInsula
  | multipleOrMixedRegions
  deriving Repr, DecidableEq

inductive MeasurementKind where
  | protonMRS
  | spectroscopyMetaAnalysis
  | otherGABAMeasurement
  deriving Repr, DecidableEq

inductive TaskKind where
  | thinkNoThinkTask
  | sensoryTask
  | symptomAssociation
  | noSingleTask
  deriving Repr, DecidableEq

inductive PhenotypeKind where
  | retrievalSuppressionPerformance
  | sensoryProcessingDifference
  | autismDiagnosticCoordinate
  | adhdDiagnosticCoordinate
  | ptsdDiagnosticCoordinate
  | attachmentSecurity
  | neuralSynchrony
  | neuroinflammation
  | emotionSuppression
  deriving Repr, DecidableEq

inductive Direction where
  | positiveAssociation
  | negativeAssociation
  | groupLower
  | groupHigher
  | heterogeneousOrMixed
  | directionNotPromoted
  deriving Repr, DecidableEq

inductive EvidenceClass where
  | observationalAssociation
  | groupDifference
  | systematicReviewEvidence
  | causalInterventionEvidence
  | syntheticBoundaryWitness
  deriving Repr, DecidableEq

structure RegionalGABAEvidence where
  source : LiteratureSource
  population : PopulationKind
  region : BrainRegion
  measurement : MeasurementKind
  task : TaskKind
  phenotype : PhenotypeKind
  direction : Direction
  evidenceClass : EvidenceClass
  attributionBoundary : String
  deriving Repr, DecidableEq

def schmitz2017ThoughtSuppression : RegionalGABAEvidence := {
  source := schmitz2017Source
  population := .healthyYoungAdults
  region := .hippocampus
  measurement := .protonMRS
  task := .thinkNoThinkTask
  phenotype := .retrievalSuppressionPerformance
  direction := .positiveAssociation
  evidenceClass := .observationalAssociation
  attributionBoundary := "Bound to the cited healthy-participant hippocampal Think/No-Think result; not promoted to emotion suppression, autism, ADHD, PTSD, or whole-brain GABA."
}

def autismGABAMetaAnalysis2024 : RegionalGABAEvidence := {
  source := autismGABAMetaAnalysis2024Source
  population := .mixedOrMetaAnalyticPopulation
  region := .multipleOrMixedRegions
  measurement := .spectroscopyMetaAnalysis
  task := .noSingleTask
  phenotype := .autismDiagnosticCoordinate
  direction := .groupLower
  evidenceClass := .systematicReviewEvidence
  attributionBoundary := "Group-level meta-analytic direction only; heterogeneity and regional variation block individual classification and causal-sufficiency promotion."
}

def ptsdAnteriorInsulaGABA2013 : RegionalGABAEvidence := {
  source := ptsdGABA2013Source
  population := .ptsdParticipants
  region := .anteriorInsula
  measurement := .protonMRS
  task := .symptomAssociation
  phenotype := .ptsdDiagnosticCoordinate
  direction := .groupLower
  evidenceClass := .observationalAssociation
  attributionBoundary := "Regional case-control association only; not a definition, necessity theorem, or sufficient mechanism of PTSD."
}

inductive AssociationIsCausalSufficiencyPermission : Prop
inductive RegionalDifferenceIsWholeBrainDifferencePermission : Prop
inductive GroupMeanClassifiesIndividualPermission : Prop
inductive DiagnosisDeterminesGABALevelPermission : Prop
inductive ThoughtSuppressionIsEmotionSuppressionPermission : Prop
inductive SynchronyDefinesAttachmentPermission : Prop
inductive GABADefinesNeuroinflammationPermission : Prop
inductive AutismCausedByLowGABAPermission : Prop
inductive ADHDCausedByLowGABAPermission : Prop

theorem associationDoesNotImplyCausalSufficiency :
    AssociationIsCausalSufficiencyPermission → False := by
  intro h
  cases h

theorem regionalGABADifferenceDoesNotImplyWholeBrainDifference :
    RegionalDifferenceIsWholeBrainDifferencePermission → False := by
  intro h
  cases h

theorem groupMeanDoesNotClassifyIndividual :
    GroupMeanClassifiesIndividualPermission → False := by
  intro h
  cases h

theorem diagnosisDoesNotDetermineGABALevel :
    DiagnosisDeterminesGABALevelPermission → False := by
  intro h
  cases h

theorem thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression :
    ThoughtSuppressionIsEmotionSuppressionPermission → False := by
  intro h
  cases h

theorem noAttachmentBridgeFromSynchronyWithoutReceipt :
    SynchronyDefinesAttachmentPermission → False := by
  intro h
  cases h

theorem noNeuroinflammationBridgeFromGABAWithoutReceipt :
    GABADefinesNeuroinflammationPermission → False := by
  intro h
  cases h

theorem autismLowGABAAssociationDoesNotProveCausalSufficiency :
    AutismCausedByLowGABAPermission → False := by
  intro h
  cases h

theorem adhdGABAHypothesisDoesNotProveCausalSufficiency :
    ADHDCausedByLowGABAPermission → False := by
  intro h
  cases h

inductive AuditStatus where
  | supportedBounded
  | candidateAssociationOnly
  | needsNamedReceipt
  | blockedPromotion
  | domainBridgeMissing
  deriving Repr, DecidableEq

structure TranscriptClaimAudit where
  transcriptClaim : String
  status : AuditStatus
  basis : String
  deriving Repr, DecidableEq

def transcriptClaimAudits : List TranscriptClaimAudit := [
  { transcriptClaim := "hippocampal GABA predicts successful thought suppression",
    status := .supportedBounded,
    basis := "Schmitz et al. 2017 receipt: bounded to hippocampus, healthy young adults, and Think/No-Think retrieval suppression." },
  { transcriptClaim := "the cited result specifically excludes emotional suppression",
    status := .needsNamedReceipt,
    basis := "The bounded receipt does not carry an emotion-suppression comparison." },
  { transcriptClaim := "autism has lower GABA",
    status := .candidateAssociationOnly,
    basis := "2024 meta-analytic group-level direction with heterogeneity; no individual or universal diagnostic promotion." },
  { transcriptClaim := "GABA is sufficient to create autism",
    status := .blockedPromotion,
    basis := "Association/group-difference receipts do not contain causal-sufficiency authority." },
  { transcriptClaim := "ADHD generally has lower GABA",
    status := .needsNamedReceipt,
    basis := "No general low-GABA ADHD receipt is admitted by this module." },
  { transcriptClaim := "higher GABA implies lower ADHD symptom severity",
    status := .needsNamedReceipt,
    basis := "Requires named population, region, measurement, severity instrument, direction, and source." },
  { transcriptClaim := "GABA is implicated in PTSD",
    status := .candidateAssociationOnly,
    basis := "Regional spectroscopy evidence is representable; systematic review heterogeneity blocks definition or sufficiency." },
  { transcriptClaim := "neural synchrony deficit means insecure attachment by definition",
    status := .domainBridgeMissing,
    basis := "Synchrony and attachment are distinct phenotype domains; no definitional bridge receipt is present." },
  { transcriptClaim := "GABA state determines neuroinflammation",
    status := .domainBridgeMissing,
    basis := "Neurochemical and neuroinflammatory coordinates require an explicit empirical adapter." }
]

structure GABAPhenotypeBoundary where
  regionalEvidenceIsRepresentable : Bool
  sourceAttributionIsRetained : Bool
  associationAutoPromotesToCausation : Bool
  groupDifferenceAutoClassifiesIndividuals : Bool
  diagnosisAutoDeterminesGABA : Bool
  crossDomainAttachmentBridgeIsAutomatic : Bool
  deriving Repr, DecidableEq

def canonicalGABAPhenotypeBoundary : GABAPhenotypeBoundary := {
  regionalEvidenceIsRepresentable := true
  sourceAttributionIsRetained := true
  associationAutoPromotesToCausation := false
  groupDifferenceAutoClassifiesIndividuals := false
  diagnosisAutoDeterminesGABA := false
  crossDomainAttachmentBridgeIsAutomatic := false
}

end Dashi.Biology.GABAPhenotypeEvidenceExact
