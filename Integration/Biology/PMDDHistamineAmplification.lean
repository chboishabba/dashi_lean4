namespace DASHI.Biology.PMDDHistamineAmplification

/-
PMDD / HISTAMINE AMPLIFICATION MIRROR

This file mirrors the Agda attribution boundary in a deliberately small Lean
surface.  It does not assert that histamine causes PMDD, that antihistamine
response is diagnostic, or that gut dysfunction is a universal root cause.
-/

inductive EvidenceLayer where
  | externalSourceObservation
  | sourceBoundMechanisticObservation
  | dashiCrossSourceSynthesis
  | untestedClinicalSubtypeHypothesis
  deriving Repr, DecidableEq

inductive MechanismNode where
  | ovarianSteroidTransition
  | alloGABAAResponse
  | stressSensitivity
  | estradiolSensitiveMastCellState
  | histamineSignallingState
  | peripheralHistamineLoad
  | symptomAmplification
  | pmddPhenotype
  deriving Repr, DecidableEq

inductive AtomicChemistrySlot where
  | formula
  | molecularGraph
  | charge
  | protonation
  | stereochemistry
  | conformer
  | functionalGroup
  | spectralIdentity
  | concentration
  | unit
  | binding
  | kinetics
  deriving Repr, DecidableEq

structure AttributedSource where
  author : String
  title : String
  publication : String
  year : String
  doi : Option String
  url : String
  relationship : String
  citationImportsProof : Bool := false
  citationCreatesAuthority : Bool := false
  deriving Repr, DecidableEq

def hantsooEpperson2020 : AttributedSource :=
  { author := "Liisa Hantsoo; C. Neill Epperson"
    title := "Allopregnanolone in premenstrual dysphoric disorder (PMDD): Evidence for dysregulated sensitivity to GABA-A receptor modulating neuroactive steroids across the menstrual cycle"
    publication := "Neurobiology of Stress"
    year := "2020"
    doi := some "10.1016/j.ynstr.2020.100213"
    url := "https://pubmed.ncbi.nlm.nih.gov/32435664/"
    relationship := "External review source for the ALLO / GABA_A steroid-sensitivity account of PMDD." }

def zaitsuEtAl2007 : AttributedSource :=
  { author := "Masafumi Zaitsu et al."
    title := "Estradiol activates mast cells via a non-genomic estrogen receptor-alpha and calcium influx"
    publication := "Molecular Immunology"
    year := "2007"
    doi := some "10.1016/j.molimm.2006.09.030"
    url := "https://pubmed.ncbi.nlm.nih.gov/17084457/"
    relationship := "External cellular source for estradiol-sensitive mast-cell activation; not a PMDD study." }

def ito2000 : AttributedSource :=
  { author := "Chiaki Ito"
    title := "The role of brain histamine in acute and chronic stresses"
    publication := "Biomedicine & Pharmacotherapy"
    year := "2000"
    doi := some "10.1016/S0753-3322(00)80069-4"
    url := "https://pubmed.ncbi.nlm.nih.gov/10917464/"
    relationship := "External review source for stress-sensitive brain histamine signalling; not a PMDD-causation theorem." }

def doseClinicReel : AttributedSource :=
  { author := "Sera Ghaly / The Dose Clinic"
    title := "Instagram reel on antihistamines, PMDD, histamine and gut root-cause framing"
    publication := "Instagram / The Dose Clinic"
    year := "2026"
    doi := none
    url := "https://www.instagram.com/reel/Dc-dwJAuatg/"
    relationship := "Practitioner-source prompt for the synthesis; stronger diagnostic and root-cause claims are not promoted." }

structure SourceBoundEdge where
  from : MechanismNode
  to : MechanismNode
  layer : EvidenceLayer
  source : AttributedSource
  reading : String
  universalPopulationClaim : Bool := false
  deriving Repr, DecidableEq

def pmddSteroidSensitivityEdge : SourceBoundEdge :=
  { from := .ovarianSteroidTransition
    to := .alloGABAAResponse
    layer := .externalSourceObservation
    source := hantsooEpperson2020
    reading := "PMDD review literature supports dysregulated sensitivity to dynamic allopregnanolone / GABA_A signalling." }

def alloStressEdge : SourceBoundEdge :=
  { from := .alloGABAAResponse
    to := .stressSensitivity
    layer := .sourceBoundMechanisticObservation
    source := hantsooEpperson2020
    reading := "The source reviews impaired ALLO-GABA regulation of physiologic stress response in PMDD." }

def estradiolMastCellEdge : SourceBoundEdge :=
  { from := .ovarianSteroidTransition
    to := .estradiolSensitiveMastCellState
    layer := .sourceBoundMechanisticObservation
    source := zaitsuEtAl2007
    reading := "Physiological estradiol activated or potentiated mast-cell mediator release in the reported experimental systems." }

def histamineStressEdge : SourceBoundEdge :=
  { from := .histamineSignallingState
    to := .stressSensitivity
    layer := .sourceBoundMechanisticObservation
    source := ito2000
    reading := "The review reports stress-sensitive brain histamine turnover and histamine participation in stress-related signalling." }

def externalEdges : List SourceBoundEdge :=
  [pmddSteroidSensitivityEdge, alloStressEdge, estradiolMastCellEdge, histamineStressEdge]

structure HistamineAmplifiedPMDDCandidate where
  pmddPrimaryLane : MechanismNode
  histamineModifierLane : MechanismNode
  jointOutcome : MechanismNode
  evidence : List SourceBoundEdge
  steroidSensitivityPrimary : Bool
  histamineIsModifierNotUniversalCause : Bool
  interactionRequiresDirectTesting : Bool
  h1h2ResponseIsDiagnosticProof : Bool
  gutDysfunctionIsUniversalRootCause : Bool
  clinicalEfficacyEstablished : Bool
  therapeuticRecommendationImported : Bool
  reading : String
  deriving Repr, DecidableEq

def canonicalCandidate : HistamineAmplifiedPMDDCandidate :=
  { pmddPrimaryLane := .alloGABAAResponse
    histamineModifierLane := .histamineSignallingState
    jointOutcome := .symptomAmplification
    evidence := externalEdges
    steroidSensitivityPrimary := true
    histamineIsModifierNotUniversalCause := true
    interactionRequiresDirectTesting := true
    h1h2ResponseIsDiagnosticProof := false
    gutDysfunctionIsUniversalRootCause := false
    clinicalEfficacyEstablished := false
    therapeuticRecommendationImported := false
    reading := "DASHI synthesis candidate: histamine / mast-cell / stress signalling may amplify a steroid-sensitive PMDD state in a subset; this is not an externally established disease mechanism." }

theorem candidate_not_diagnostic :
    canonicalCandidate.h1h2ResponseIsDiagnosticProof = false := rfl

theorem candidate_not_universal_gut_root_cause :
    canonicalCandidate.gutDysfunctionIsUniversalRootCause = false := rfl

theorem candidate_not_clinical_efficacy :
    canonicalCandidate.clinicalEfficacyEstablished = false := rfl

theorem candidate_not_therapeutic_recommendation :
    canonicalCandidate.therapeuticRecommendationImported = false := rfl

inductive HistamineCausesAllPMDD : Prop
inductive AntihistamineResponseDiagnosesHistaminePMDD : Prop
inductive GutDysfunctionIsThePMDDRootCause : Prop
inductive CellularEstradiolMastCellResultIsClinicalPMDDProof : Prop

theorem histamineDoesNotBecomeUniversalCause
    (h : HistamineCausesAllPMDD) : False := by
  cases h

theorem antihistamineResponseIsNotDiagnosticProof
    (h : AntihistamineResponseDiagnosesHistaminePMDD) : False := by
  cases h

theorem gutRootCauseNotPromoted
    (h : GutDysfunctionIsThePMDDRootCause) : False := by
  cases h

theorem cellularMastCellResultDoesNotBecomePMDDProof
    (h : CellularEstradiolMastCellResultIsClinicalPMDDProof) : False := by
  cases h

structure ExperimentalFrontier where
  prospectiveCycleTracking : String
  histamineLaneMeasurement : String
  steroidLaneMeasurement : String
  interventionProtocol : String
  interactionTest : String
  subtypeReplication : String
  deriving Repr, DecidableEq

def experimentalFrontier : ExperimentalFrontier :=
  { prospectiveCycleTracking := "prospective within-person symptom tracking across multiple menstrual cycles"
    histamineLaneMeasurement := "protocol-indexed histamine / mast-cell / receptor-relevant readouts with timing preserved"
    steroidLaneMeasurement := "cycle phase plus ovarian-steroid / neurosteroid measurements sufficient to bind the steroid-transition lane"
    interventionProtocol := "pre-specified controlled intervention rather than retrospective response attribution"
    interactionTest := "test whether the histamine lane explains incremental symptom variance or modifies the steroid-sensitive lane"
    subtypeReplication := "replicate any apparent responder subgroup before treating it as a biological subtype" }

end DASHI.Biology.PMDDHistamineAmplification
