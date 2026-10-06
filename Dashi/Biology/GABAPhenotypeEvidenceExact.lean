namespace Dashi.Biology.GABAPhenotypeEvidenceExact

/-!
Bounded GABA/phenotype evidence mirror.

The source-side discipline mirrors the Agda attribution rules: a citation
identifies provenance and the formalisation relationship but does not import
proof or create scientific authority.  Regional/group evidence is not promoted
to whole-brain state, individual diagnosis, causal necessity/sufficiency,
attachment status, neuroinflammation, or an uncited cross-domain mechanism.
-/

structure AttributedSource where
  authors : String
  title : String
  publicationContext : String
  year : String
  doi : String
  canonicalURL : String
  relationship : String
  citationImportsProof : Bool
  citationCreatesAuthority : Bool
  deriving Repr, DecidableEq

def mkDOISource
    (authors title publicationContext year doi canonicalURL relationship : String) :
    AttributedSource := {
  authors := authors
  title := title
  publicationContext := publicationContext
  year := year
  doi := doi
  canonicalURL := canonicalURL
  relationship := relationship
  citationImportsProof := false
  citationCreatesAuthority := false
}

def schmitz2017Source : AttributedSource :=
  mkDOISource
    "Taylor W. Schmitz; Marta M. Correia; Catarina S. Ferreira; Andrew P. Prescot; Michael C. Anderson"
    "Hippocampal GABA enables inhibitory control over unwanted thoughts"
    "Nature Communications 8:1311"
    "2017"
    "10.1038/s41467-017-00956-z"
    "https://doi.org/10.1038/s41467-017-00956-z"
    "Pays the healthy-young-adult hippocampal GABA / Think-No-Think retrieval-suppression association. It does not pay emotion suppression, diagnosis, or causal sufficiency."

def autismGABAMetaAnalysis2024Source : AttributedSource :=
  mkDOISource
    "Alice R. Thomson; Duanghathai Pasanta; Tomoki Arichi; Nicolaas A. Puts"
    "Neurometabolite differences in Autism as assessed with Magnetic Resonance Spectroscopy: A systematic review and meta-analysis"
    "Neuroscience & Biobehavioral Reviews 162:105728"
    "2024"
    "10.1016/j.neubiorev.2024.105728"
    "https://doi.org/10.1016/j.neubiorev.2024.105728"
    "Pays a group-level meta-analytic autism/GABA direction while retaining demographic, regional, and methodological heterogeneity. It does not classify individuals or prove causal sufficiency."

def puts2017Source : AttributedSource :=
  mkDOISource
    "Nicolaas A. J. Puts; Ericka L. Wodka; Ashley D. Harris; Deana Crocetti; Mark Tommerdahl; Stewart H. Mostofsky; Richard A. E. Edden"
    "Reduced GABA and altered somatosensory function in children with autism spectrum disorder"
    "Autism Research 10(4):608-619"
    "2017"
    "10.1002/aur.1691"
    "https://doi.org/10.1002/aur.1691"
    "Pays reduced sensorimotor GABA in the studied autistic-child cohort and task-specific associations with tactile measures; occipital GABA was not reduced."

def umesawa2020Source : AttributedSource :=
  mkDOISource
    "Yumi Umesawa; Takeshi Atsumi; Mrinmoy Chakrabarty; Reiko Fukatsu; Masakazu Ide"
    "GABA Concentration in the Left Ventral Premotor Cortex Associates With Sensory Hyper-Responsiveness in Autism Spectrum Disorders Without Intellectual Disability"
    "Frontiers in Neuroscience 14:482"
    "2020"
    "10.3389/fnins.2020.00482"
    "https://doi.org/10.3389/fnins.2020.00482"
    "Pays a negative association between left ventral premotor-cortex GABA and sensory hyper-responsiveness in the studied cohort; it does not universalise a sensory-severity law."

def ptsdGABA2014Source : AttributedSource :=
  mkDOISource
    "Isabelle M. Rosso; Melissa R. Weiner; David J. Crowley; Marisa M. Silveri; Scott L. Rauch; J. Eric Jensen"
    "Insula and anterior cingulate GABA levels in posttraumatic stress disorder: preliminary findings using magnetic resonance spectroscopy"
    "Depression and Anxiety 31(2):115-123"
    "2014"
    "10.1002/da.22155"
    "https://doi.org/10.1002/da.22155"
    "Pays the preliminary right-anterior-insula group difference; dorsal ACC did not significantly differ and insula GABA was not significantly associated with PTSD symptom severity."

def ptsdMRSReview2022Source : AttributedSource :=
  mkDOISource
    "Kelley M. Swanberg; Leonardo Campos; Chadi G. Abdallah; Christoph Juchem"
    "Proton Magnetic Resonance Spectroscopy in Post-Traumatic Stress Disorder-Updated Systematic Review and Meta-Analysis"
    "Chronic Stress 6:24705470221128004"
    "2022"
    "10.1177/24705470221128004"
    "https://doi.org/10.1177/24705470221128004"
    "Pays the cross-study MRS review boundary: the strongest replicated meta-analytic signal was not a general GABA law, and heterogeneity varied widely across analyses."

def transcriptSource : AttributedSource := {
  authors := "unidentified speaker in user-supplied transcript"
  title := "transcript-2026-10-06 (1).srt"
  publicationContext := "user-supplied SRT transcript"
  year := "2026"
  doi := ""
  canonicalURL := ""
  relationship := "Primary source for the claims audited below. Speaker identity is not inferred. External scientific support is represented only by separate attributed-source receipts."
  citationImportsProof := false
  citationCreatesAuthority := false
}

def canonicalEvidenceSources : List AttributedSource := [
  schmitz2017Source,
  autismGABAMetaAnalysis2024Source,
  puts2017Source,
  umesawa2020Source,
  ptsdGABA2014Source,
  ptsdMRSReview2022Source
]

inductive PopulationKind where
  | healthyYoungAdults
  | autisticChildren
  | autisticParticipantsWithoutID
  | autisticParticipants
  | adhdParticipants
  | ptsdParticipants
  | mixedOrMetaAnalyticPopulation
  deriving Repr, DecidableEq

inductive BrainRegion where
  | hippocampus
  | sensorimotorCortex
  | occipitalCortex
  | leftVentralPremotorCortex
  | medialPrefrontalCortex
  | anteriorInsula
  | dorsalAnteriorCingulate
  | multipleOrMixedRegions
  deriving Repr, DecidableEq

inductive MeasurementKind where
  | protonMRS
  | gabaEditedMRS
  | spectroscopyMetaAnalysis
  | otherGABAMeasurement
  deriving Repr, DecidableEq

inductive TaskKind where
  | thinkNoThinkTask
  | tactileTaskBattery
  | sensoryQuestionnaire
  | symptomAssociation
  | noSingleTask
  deriving Repr, DecidableEq

inductive PhenotypeKind where
  | retrievalSuppressionPerformance
  | tactileProcessingDifference
  | sensoryHyperResponsiveness
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
  | noSignificantGroupDifference
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
  source : AttributedSource
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
  attributionBoundary := "Greater resting hippocampal GABA predicted better mnemonic control in the study. The functional-specificity comparison was action stopping, not emotional suppression."
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
  attributionBoundary := "Overall lower GABA at group level in the meta-analysis; demographic, regional, and methodological variation remains explicit and blocks individual or universal promotion."
}

def puts2017SensorimotorGABA : RegionalGABAEvidence := {
  source := puts2017Source
  population := .autisticChildren
  region := .sensorimotorCortex
  measurement := .gabaEditedMRS
  task := .tactileTaskBattery
  phenotype := .tactileProcessingDifference
  direction := .groupLower
  evidenceClass := .groupDifference
  attributionBoundary := "Sensorimotor GABA was lower in the studied autistic-child group; occipital GABA was reported as normal. Several tactile associations were task-specific, so this row does not encode a scalar symptom-severity law."
}

def umesawa2020SensoryHyperResponsiveness : RegionalGABAEvidence := {
  source := umesawa2020Source
  population := .autisticParticipantsWithoutID
  region := .leftVentralPremotorCortex
  measurement := .protonMRS
  task := .sensoryQuestionnaire
  phenotype := .sensoryHyperResponsiveness
  direction := .negativeAssociation
  evidenceClass := .observationalAssociation
  attributionBoundary := "Lower left-vPMC GABA was associated with greater sensory hyper-responsiveness in the studied ASD group; region, cohort, and instrument remain part of the receipt."
}

def ptsdAnteriorInsulaGABA2014 : RegionalGABAEvidence := {
  source := ptsdGABA2014Source
  population := .ptsdParticipants
  region := .anteriorInsula
  measurement := .protonMRS
  task := .symptomAssociation
  phenotype := .ptsdDiagnosticCoordinate
  direction := .groupLower
  evidenceClass := .groupDifference
  attributionBoundary := "Right anterior-insula GABA was lower in the preliminary PTSD sample; dorsal ACC did not significantly differ, and insula GABA was not significantly associated with PTSD symptom severity."
}

def ptsdMRSReview2022 : RegionalGABAEvidence := {
  source := ptsdMRSReview2022Source
  population := .mixedOrMetaAnalyticPopulation
  region := .multipleOrMixedRegions
  measurement := .spectroscopyMetaAnalysis
  task := .noSingleTask
  phenotype := .ptsdDiagnosticCoordinate
  direction := .heterogeneousOrMixed
  evidenceClass := .systematicReviewEvidence
  attributionBoundary := "The systematic review/meta-analysis reports strong methodological and regional heterogeneity; it does not license a general PTSD = low-GABA law."
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
inductive SensoryAssociationIsGlobalSeverityLawPermission : Prop

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

theorem sensoryAssociationDoesNotUniversalizeAutism :
    SensoryAssociationIsGlobalSeverityLawPermission → False := by
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
  origin : AttributedSource
  sourceSpan : String
  transcriptClaim : String
  status : AuditStatus
  basis : String
  deriving Repr, DecidableEq

def transcriptClaimAudits : List TranscriptClaimAudit := [
  { origin := transcriptSource,
    sourceSpan := "00:00:00,000 --> 00:00:05,620",
    transcriptClaim := "GABA goes as far as to predict successful thought suppression, not emotional suppression.",
    status := .supportedBounded,
    basis := "Schmitz et al. 2017 supports the hippocampal-GABA / retrieval-suppression component. Its explicit functional comparison is action stopping, not emotion suppression, so the final contrast is not promoted." },
  { origin := transcriptSource,
    sourceSpan := "00:00:13,030 --> 00:00:21,220",
    transcriptClaim := "GABA is enough to create autism.",
    status := .blockedPromotion,
    basis := "Group differences and associations do not supply a causal-sufficiency receipt." },
  { origin := transcriptSource,
    sourceSpan := "00:00:22,000 --> 00:00:28,020",
    transcriptClaim := "The GABA pathway is enough to create ADHD.",
    status := .blockedPromotion,
    basis := "No causal-sufficiency receipt is present; this module deliberately has no general ADHD-low-GABA evidence row." },
  { origin := transcriptSource,
    sourceSpan := "00:00:28,340 --> 00:00:38,440",
    transcriptClaim := "GABA levels in ADHD are lower.",
    status := .needsNamedReceipt,
    basis := "No general diagnosis-wide ADHD-low-GABA receipt is admitted here." },
  { origin := transcriptSource,
    sourceSpan := "00:00:38,440 --> 00:00:45,900",
    transcriptClaim := "Higher the GABA, lower the ADHD symptom severity.",
    status := .needsNamedReceipt,
    basis := "Requires a named population, brain region, measurement method, symptom instrument, direction/effect estimate, and source." },
  { origin := transcriptSource,
    sourceSpan := "00:01:09,380 --> 00:01:13,460",
    transcriptClaim := "lack of neurosynchrony means by definition insecure attachment",
    status := .domainBridgeMissing,
    basis := "Neural synchrony and attachment status are different empirical domains; no definitional or validated empirical adapter is present." },
  { origin := transcriptSource,
    sourceSpan := "00:01:22,930 --> 00:01:26,610",
    transcriptClaim := "GABA is lower in autism compared to healthy controls.",
    status := .candidateAssociationOnly,
    basis := "The 2024 meta-analysis supports a group-level lower-GABA direction overall, while preserving regional, demographic, and methodological heterogeneity." },
  { origin := transcriptSource,
    sourceSpan := "00:01:26,960 --> 00:01:35,190",
    transcriptClaim := "Lower GABA is associated with greater sensory sensitivity in autism.",
    status := .candidateAssociationOnly,
    basis := "Puts et al. 2017 and Umesawa et al. 2020 support bounded regional/task-specific sensory associations; they do not establish a universal whole-brain or global symptom-severity law." }
]

structure GABAPhenotypeBoundary where
  regionalEvidenceIsRepresentable : Bool
  sourceAttributionIsRetained : Bool
  citationImportsProof : Bool
  citationCreatesAuthority : Bool
  associationAutoPromotesToCausation : Bool
  groupDifferenceAutoClassifiesIndividuals : Bool
  diagnosisAutoDeterminesGABA : Bool
  crossDomainAttachmentBridgeIsAutomatic : Bool
  sensoryAssociationIsUniversalSeverityLaw : Bool
  deriving Repr, DecidableEq

def canonicalGABAPhenotypeBoundary : GABAPhenotypeBoundary := {
  regionalEvidenceIsRepresentable := true
  sourceAttributionIsRetained := true
  citationImportsProof := false
  citationCreatesAuthority := false
  associationAutoPromotesToCausation := false
  groupDifferenceAutoClassifiesIndividuals := false
  diagnosisAutoDeterminesGABA := false
  crossDomainAttachmentBridgeIsAutomatic := false
  sensoryAssociationIsUniversalSeverityLaw := false
}

end Dashi.Biology.GABAPhenotypeEvidenceExact
