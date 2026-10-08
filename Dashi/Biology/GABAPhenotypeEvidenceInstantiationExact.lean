import Dashi.Biology.GABAPhenotypeBridgeExact

namespace Dashi.Biology.GABAPhenotypeEvidenceInstantiationExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.GABAPhenotypeBridgeExact

/-!
Evidence-instantiation mirror for the GABA max-cut.

This file mirrors only bounded source claims. It does not create diagnostic or
causal authority from citations, associations, subgroup differences, or assay
labels. Concrete causal-estimand authority remains Agda-owned as stated by the
bridge layer.
-/

def nguyen2024Source : AttributedSource :=
  mkDOISource
    "Trinh Nguyen; Melanie T Kungl; Stefanie Hoehl; Lars O White; Pascal Vrtička"
    "Visualizing the invisible tie: Linking parent-child neural synchrony to parents' and children's attachment representations"
    "Developmental Science 27(6):e13504"
    "2024"
    "10.1111/desc.13504"
    "https://doi.org/10.1111/desc.13504"
    "Pays a bounded fNIRS synchrony/attachment-representation association with subgroup and regional dependence; it does not define attachment security from synchrony."

def crowley2016Source : AttributedSource :=
  mkDOISource
    "Tadhg Crowley; John F Cryan; Eric J Downer; Olivia F O'Leary"
    "Inhibiting neuroinflammation: The role and therapeutic potential of GABA in neuro-immune interactions"
    "Brain, Behavior, and Immunity 54:260-277"
    "2016"
    "10.1016/j.bbi.2016.02.001"
    "https://doi.org/10.1016/j.bbi.2016.02.001"
    "Review-level support for reciprocal GABAergic/neuroimmune interactions; not diagnosis-level causal sufficiency."

def schur2016Source : AttributedSource :=
  mkDOISource
    "Remmelt R Schür; Luc W R Draisma; Jannie P Wijnen; Marco P Boks; Martijn G J C Koevoets; Marian Joëls; Dennis W Klomp; René S Kahn; Christiaan H Vinkers"
    "Brain GABA levels across psychiatric disorders: A systematic literature review and meta-analysis of (1) H-MRS studies"
    "Human Brain Mapping 37(9):3337-3352"
    "2016"
    "10.1002/hbm.23244"
    "https://doi.org/10.1002/hbm.23244"
    "Pays the reported absence of a significant pooled ADHD-control brain-GABA difference in the included H-MRS studies; not exact equality or a regional null theorem."

def puts2020Source : AttributedSource :=
  mkDOISource
    "Nicolaas A Puts; Matthew Ryan; Georg Oeltzschner; Alena Horska; Richard A E Edden; E Mark Mahone"
    "Reduced striatal GABA in unmedicated children with ADHD at 7T"
    "Psychiatry Research: Neuroimaging 301:111082"
    "2020"
    "10.1016/j.pscychresns.2020.111082"
    "https://doi.org/10.1016/j.pscychresns.2020.111082"
    "Pays reduced striatal GABA/Cr in the studied unmedicated children; ACC, DLPFC and premotor regions did not show the same group difference, and behavioral manifestations were not significantly correlated with metabolites."

def harris2021Source : AttributedSource :=
  mkDOISource
    "Ashley D Harris; Donald L Gilbert; Paul S Horn; Deana Crocetti; Kim M Cecil; Richard A E Edden; David A Huddleston; Stewart H Mostofsky; Nicolaas A J Puts"
    "Relationship between GABA levels and task-dependent cortical excitability in children with attention-deficit/hyperactivity disorder"
    "Clinical Neurophysiology 132(5):1163-1172"
    "2021"
    "10.1016/j.clinph.2021.01.023"
    "https://doi.org/10.1016/j.clinph.2021.01.023"
    "Pays a sensorimotor GABA+/TMS study in which GABA+ did not differ overall between groups or correlate with ADHD clinical symptoms."

def cheng2026Source : AttributedSource :=
  mkDOISource
    "Xue Cheng; Lingzhi Wang; Cong Diao; Yunhe Wang; Yuanyuan Xue"
    "The ratio of GABA/Glu as a biomarker in children with attention deficit hyperactivity disorder"
    "Physiology & Behavior 315:115445"
    "2026"
    "10.1016/j.physbeh.2026.115445"
    "https://doi.org/10.1016/j.physbeh.2026.115445"
    "Pays a peripheral-serum study reporting higher serum GABA/GABA-Glu and positive SNAP-IV associations; it is not a brain-MRS measurement and requires independent validation before clinical application."

structure SynchronyAttachmentAssociationReceipt where
  source : AttributedSource
  populationReference : String
  neuralMeasurementReference : String
  attachmentMeasurementReference : String
  associationReference : String
  subgroupAndRegionDependenceRetained : Bool
  definitionOrClassifierAuthority : Bool
  deriving Repr, DecidableEq

def nguyen2024SynchronyAttachmentAssociation : SynchronyAttachmentAssociationReceipt := {
  source := nguyen2024Source
  populationReference := "140 parents and their 5-6-year-old children in cooperative versus individual problem-solving"
  neuralMeasurementReference := "fNIRS hyperscanning interpersonal neural synchrony in frontal and temporal regions"
  attachmentMeasurementReference := "Adult Attachment Interview for parents and story-completion attachment task for children"
  associationReference := "Attachment representations were associated with interpersonal neural synchrony during cooperation; maternal insecurity and daughter security showed different regional directions."
  subgroupAndRegionDependenceRetained := true
  definitionOrClassifierAuthority := false
}

def nguyen2024SynchronyAttachmentBridge : SynchronyAttachmentBridge := {
  validation := {
    source := nguyen2024Source
    validationReference := "Validated only as a study-scoped synchrony/attachment association receipt; not definitional or diagnostic promotion."
    validated := true
  }
  synchronyMeasurementReference := "fNIRS interpersonal neural synchrony during parent-child cooperative problem-solving"
  attachmentConstructReference := "parent Adult Attachment Interview / child story-completion attachment representation measures"
  bridgeModelReference := "Nguyen et al. 2024 subgroup- and region-dependent association model"
}

inductive SynchronyDefinesAttachmentPermission : Prop

theorem synchronyAssociationDoesNotDefineAttachment :
    SynchronyDefinesAttachmentPermission → False := by
  intro h
  cases h

def crowley2016NeuroimmuneEvidence : RegionalGABAEvidence := {
  source := crowley2016Source
  population := .mixedOrMetaAnalyticPopulation
  region := .multipleOrMixedRegions
  measurement := .otherGABAMeasurement
  task := .noSingleTask
  phenotype := .neuroinflammation
  direction := .heterogeneousOrMixed
  evidenceClass := .systematicReviewEvidence
  attributionBoundary := "Review-level reciprocal GABAergic/neuroimmune mechanism evidence only; no diagnosis, universal direction, individual classifier, or neurodevelopmental causal sufficiency."
}

def crowley2016NeuroimmuneBridge : NeurochemicalInflammationBridge crowley2016NeuroimmuneEvidence := {
  validation := {
    source := crowley2016Source
    validationReference := "Validated as a review-level mechanistic bridge between GABAergic signalling and neuroinflammatory processes only."
    validated := true
  }
  inflammatoryReadoutReference := "glial/microglial inflammatory signalling, cytokine/chemokine responses, and immune-cell GABA receptor pathways reviewed across cited studies"
  mediatorReference := "reciprocal neural-immune signalling; no single mediator universalised"
  temporalDirectionReference := "bidirectional interaction retained; not collapsed to GABA -> inflammation"
}

inductive NeuroimmuneReviewIsDiagnosisCausalPermission : Prop

theorem neuroimmuneReviewDoesNotPayDiagnosisCausation :
    NeuroimmuneReviewIsDiagnosisCausalPermission → False := by
  intro h
  cases h

inductive ADHDMeasurementDomain where
  | brainMRS
  | regionSpecificBrainMRS
  | multimodalMRSTMS
  | peripheralSerum
  deriving Repr, DecidableEq

inductive ADHDDirectionFinding where
  | noSignificantOverallDifference
  | lowerInSelectedRegion
  | noGroupDifferenceInSelectedRegion
  | higherPeripheralLevel
  deriving Repr, DecidableEq

inductive ADHDSymptomRelationFinding where
  | noGeneralSymptomRelationPaid
  | noSignificantClinicalSymptomCorrelation
  | positiveSymptomCorrelation
  deriving Repr, DecidableEq

structure ADHDGABAStudyReceipt where
  source : AttributedSource
  domain : ADHDMeasurementDomain
  populationReference : String
  regionOrCompartmentReference : String
  assayReference : String
  directionFinding : ADHDDirectionFinding
  symptomRelationFinding : ADHDSymptomRelationFinding
  scopeBoundary : String
  deriving Repr, DecidableEq

def schur2016ADHDMetaReceipt : ADHDGABAStudyReceipt := {
  source := schur2016Source
  domain := .brainMRS
  populationReference := "ADHD subset within a seven-disorder H-MRS systematic review/meta-analysis"
  regionOrCompartmentReference := "brain H-MRS studies pooled across reported regions"
  assayReference := "1H-MRS meta-analysis"
  directionFinding := .noSignificantOverallDifference
  symptomRelationFinding := .noGeneralSymptomRelationPaid
  scopeBoundary := "No significant pooled difference is not exact equality and does not erase regional, age, task, or assay effects."
}

def puts2020ADHDStriatalReceipt : ADHDGABAStudyReceipt := {
  source := puts2020Source
  domain := .regionSpecificBrainMRS
  populationReference := "50 unmedicated children aged 5-9 years, 26 ADHD and 24 controls"
  regionOrCompartmentReference := "striatum, with DLPFC, ACC, and premotor cortex also measured"
  assayReference := "7T MRS with LCModel; GABA/Cr"
  directionFinding := .lowerInSelectedRegion
  symptomRelationFinding := .noSignificantClinicalSymptomCorrelation
  scopeBoundary := "Lower GABA/Cr was striatal; the same group difference was not present in ACC, DLPFC or premotor cortex, and behavioral manifestations did not significantly correlate with metabolites."
}

def harris2021ADHDSensorimotorReceipt : ADHDGABAStudyReceipt := {
  source := harris2021Source
  domain := .multimodalMRSTMS
  populationReference := "37 children with ADHD and 45 typically developing children aged 8-12 years across two sites"
  regionOrCompartmentReference := "left sensorimotor cortex"
  assayReference := "GABA-edited MRS plus single/paired-pulse TMS at rest and during GO/STOP states"
  directionFinding := .noGroupDifferenceInSelectedRegion
  symptomRelationFinding := .noSignificantClinicalSymptomCorrelation
  scopeBoundary := "GABA+ did not differ overall between groups or correlate with ADHD clinical symptoms; physiology varied by state and measure."
}

def cheng2026ADHDSerumReceipt : ADHDGABAStudyReceipt := {
  source := cheng2026Source
  domain := .peripheralSerum
  populationReference := "145 children with ADHD and 120 healthy controls"
  regionOrCompartmentReference := "peripheral serum"
  assayReference := "UPLC-MS/MS serum GABA, glutamate, and GABA/Glu ratio"
  directionFinding := .higherPeripheralLevel
  symptomRelationFinding := .positiveSymptomCorrelation
  scopeBoundary := "Serum is not brain MRS. Higher serum GABA/GABA-Glu and positive SNAP-IV correlations cannot be collapsed into a central regional GABA law; independent validation remains required."
}

structure ADHDEvidenceHeterogeneityAtlas where
  pooledBrainMRS : ADHDGABAStudyReceipt
  selectedStriatalMRS : ADHDGABAStudyReceipt
  sensorimotorMRSTMS : ADHDGABAStudyReceipt
  serumMeasurement : ADHDGABAStudyReceipt
  regionDependenceRetained : Bool
  assayCompartmentDependenceRetained : Bool
  uniformLowGABADirectionAvailable : Bool
  uniformInverseSeverityRelationAvailable : Bool
  deriving Repr, DecidableEq

def canonicalADHDEvidenceHeterogeneityAtlas : ADHDEvidenceHeterogeneityAtlas := {
  pooledBrainMRS := schur2016ADHDMetaReceipt
  selectedStriatalMRS := puts2020ADHDStriatalReceipt
  sensorimotorMRSTMS := harris2021ADHDSensorimotorReceipt
  serumMeasurement := cheng2026ADHDSerumReceipt
  regionDependenceRetained := true
  assayCompartmentDependenceRetained := true
  uniformLowGABADirectionAvailable := false
  uniformInverseSeverityRelationAvailable := false
}

inductive ADHDGeneralLowGABAPermission : Prop
inductive ADHDHigherGABALowerSeverityPermission : Prop

theorem adhdEvidenceDoesNotPayGeneralLowGABA : ADHDGeneralLowGABAPermission → False := by
  intro h
  cases h

theorem adhdEvidenceDoesNotPayInverseSeverityLaw : ADHDHigherGABALowerSeverityPermission → False := by
  intro h
  cases h

structure GABAEvidenceInstantiationBoundary where
  synchronyAttachmentAssociationInstantiated : Bool
  synchronyDoesNotDefineAttachment : Bool
  neuroimmuneMechanisticBridgeInstantiated : Bool
  neuroimmuneReviewPaysDiagnosisCausation : Bool
  adhdHeterogeneityAtlasInstantiated : Bool
  adhdGeneralLowGABAClaimPaid : Bool
  adhdInverseSeverityLawPaid : Bool
  deriving Repr, DecidableEq

def canonicalGABAEvidenceInstantiationBoundary : GABAEvidenceInstantiationBoundary := {
  synchronyAttachmentAssociationInstantiated := true
  synchronyDoesNotDefineAttachment := false
  neuroimmuneMechanisticBridgeInstantiated := true
  neuroimmuneReviewPaysDiagnosisCausation := false
  adhdHeterogeneityAtlasInstantiated := true
  adhdGeneralLowGABAClaimPaid := false
  adhdInverseSeverityLawPaid := false
}

end Dashi.Biology.GABAPhenotypeEvidenceInstantiationExact
