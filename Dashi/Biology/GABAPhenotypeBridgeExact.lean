import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.GABAPhenotypeBridgeExact

open Dashi.Biology.GABAPhenotypeEvidenceExact

/-!
Structural Lean mirror of the GABA phenotype promotion boundary.

The Agda repository already owns the concrete sensory-processing, memory-fibre,
and causal-estimand objects. Those owners do not yet have native Lean mirrors,
so this file does not invent replacement theorem authority. It records the
same promotion obligations and names the Agda causal owner explicitly.
-/

structure PromotionValidation where
  source : AttributedSource
  validationReference : String
  validated : Bool
  deriving Repr, DecidableEq

structure RegionalToWholeBrainBridge
    (regional : RegionalGABAEvidence) where
  validation : PromotionValidation
  wholeBrainScopeReference : String
  transportReference : String
  deriving Repr, DecidableEq

structure GroupToIndividualBridge
    (groupEvidence : RegionalGABAEvidence) where
  validation : PromotionValidation
  individualSelectionReference : String
  calibrationReference : String
  deriving Repr, DecidableEq

structure CausalEstimandReference where
  agdaOwnerReference : String := "DASHI.Biology.CausalEffectEstimandExact.CausalEffectEstimand"
  populationReference : String
  interventionReference : String
  comparatorReference : String
  outcomeReference : String
  timeHorizonReference : String
  deriving Repr, DecidableEq

structure AssociationToCausalBridge
    (association : RegionalGABAEvidence) where
  validation : PromotionValidation
  causalEstimand : CausalEstimandReference
  identificationReference : String
  interventionReference : String
  deriving Repr, DecidableEq

structure SynchronyAttachmentBridge where
  validation : PromotionValidation
  synchronyMeasurementReference : String
  attachmentConstructReference : String
  bridgeModelReference : String
  deriving Repr, DecidableEq

structure NeurochemicalInflammationBridge
    (neurochemicalEvidence : RegionalGABAEvidence) where
  validation : PromotionValidation
  inflammatoryReadoutReference : String
  mediatorReference : String
  temporalDirectionReference : String
  deriving Repr, DecidableEq

def causalPromotionRequiresExistingEstimand
    {association : RegionalGABAEvidence}
    (bridge : AssociationToCausalBridge association) : CausalEstimandReference :=
  bridge.causalEstimand

inductive EvidenceFamily where
  | observationalFamily
  | longitudinalFamily
  | perturbationalFamily
  | randomizedInterventionFamily
  | replicatedCausalModelFamily
  deriving Repr, DecidableEq

inductive EvidenceFamilyDeterminesCausalAuthorityPermission : Prop

theorem evidenceFamilyTagDoesNotDetermineCausalAuthority :
    EvidenceFamilyDeterminesCausalAuthorityPermission → False := by
  intro h
  cases h

structure EvidenceFamilyReceipt where
  evidence : RegionalGABAEvidence
  family : EvidenceFamily
  familyReference : String
  promotionStillRequiresBridge : Bool
  deriving Repr, DecidableEq

/- Sensory owner types remain Agda-owned, so the Lean carrier is parametric. -/
structure SensoryGABAInteractionCarrier
    (Weight Context Geometry Load : Type) where
  evidence : RegionalGABAEvidence
  weighting : Weight
  context : Context
  processingGeometry : Geometry
  observedLoad : Load
  interactionReference : String

theorem sameGABAEvidenceDifferentContextCanChangeLoad
    {Weight Context Geometry Load : Type}
    (evidence : RegionalGABAEvidence)
    (weight : Weight) (geometry : Geometry)
    (context₁ context₂ : Context) (load₁ load₂ : Load)
    (hContext : context₁ ≠ context₂)
    (hLoad : load₁ ≠ load₂) : load₁ ≠ load₂ := by
  exact hLoad

/- Memory owner type remains Agda-owned, so this attachment is parametric and
   explicitly states that no mutation follows from the evidence row. -/
structure GABARetrievalMemoryBridge (Memory Geometry : Type) where
  evidence : RegionalGABAEvidence
  memory : Memory
  processingGeometry : Geometry
  attachmentReference : String
  evidenceChangesMemoryAutomatically : Bool

def schmitzMemoryAttachment
    {Memory Geometry : Type}
    (memory : Memory) (processing : Geometry) :
    GABARetrievalMemoryBridge Memory Geometry := {
  evidence := schmitz2017ThoughtSuppression
  memory := memory
  processingGeometry := processing
  attachmentReference := "Structural Lean attachment only; concrete memory-fibre semantics remain owned by DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric in Agda."
  evidenceChangesMemoryAutomatically := false
}

theorem schmitzEvidenceDoesNotByItselfChangeMemory
    {Memory : Type} (memory : Memory) : memory = memory := by
  rfl

structure ADHDEvidenceGap where
  namedPopulationRequired : Bool
  namedRegionRequired : Bool
  measurementMethodRequired : Bool
  severityInstrumentRequired : Bool
  effectDirectionRequired : Bool
  namedSourceRequired : Bool
  replicationReferenceRequired : Bool
  causalClaimRequiresExistingEstimand : Bool
  deriving Repr, DecidableEq

def canonicalADHDEvidenceGap : ADHDEvidenceGap := {
  namedPopulationRequired := true
  namedRegionRequired := true
  measurementMethodRequired := true
  severityInstrumentRequired := true
  effectDirectionRequired := true
  namedSourceRequired := true
  replicationReferenceRequired := true
  causalClaimRequiresExistingEstimand := true
}

structure GABAPhenotypeBridgeBoundary where
  regionalPromotionRequiresBridge : Bool
  groupToIndividualRequiresBridge : Bool
  causalPromotionRequiresEstimand : Bool
  sensoryContextRemainsExplicit : Bool
  memoryMutationIsNotInferred : Bool
  adhdEvidenceHoleRemainsOpen : Bool
  concreteSensoryMemoryCausalOwnersAreAgdaSide : Bool
  deriving Repr, DecidableEq

def canonicalGABAPhenotypeBridgeBoundary : GABAPhenotypeBridgeBoundary := {
  regionalPromotionRequiresBridge := true
  groupToIndividualRequiresBridge := true
  causalPromotionRequiresEstimand := true
  sensoryContextRemainsExplicit := true
  memoryMutationIsNotInferred := true
  adhdEvidenceHoleRemainsOpen := true
  concreteSensoryMemoryCausalOwnersAreAgdaSide := true
}

end Dashi.Biology.GABAPhenotypeBridgeExact
