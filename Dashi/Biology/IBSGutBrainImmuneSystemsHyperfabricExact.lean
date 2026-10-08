import Dashi.Biology.QuailEggHistamineGutSnowballExact

namespace Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact

inductive IBSSystemFibre where
  | dietExposureFibre
  | microbiomeMetaboliteFibre
  | epithelialBarrierFibre
  | mucosalImmuneMastCellFibre
  | entericMotilitySecretionFibre
  | visceralSensoryNociceptiveFibre
  | autonomicHPAAllostaticFibre
  | centralPainInteroceptiveFibre
  | neurochemicalMetabolicFibre
  deriving Repr, DecidableEq

inductive CouplingKind where
  | biochemical | immune | neural | endocrine | mechanical | behaviouralContext | transportBarrier
  deriving Repr, DecidableEq

structure IBSSystemEdge where
  from : IBSSystemFibre
  to : IBSSystemFibre
  coupling : CouplingKind
  evidenceReference : String
  reverseOrFeedbackReference : String
  universalCausalityClaimed : Bool
  deriving Repr, DecidableEq

def canonicalIBSFeedbackGraph : List IBSSystemEdge := [
  { from := .microbiomeMetaboliteFibre, to := .mucosalImmuneMastCellFibre, coupling := .immune,
    evidenceReference := "De Palma 2022 microbial histamine/H4; Gao 2026 fecal-LPS/TLR4 mast-cell route",
    reverseOrFeedbackReference := "host immune/barrier state can reshape luminal ecology", universalCausalityClaimed := false },
  { from := .mucosalImmuneMastCellFibre, to := .visceralSensoryNociceptiveFibre, coupling := .neural,
    evidenceReference := "Wouters 2016 and later H1 intervention evidence: histamine/H1/TRPV1-associated sensitization",
    reverseOrFeedbackReference := "neural/autonomic state can modulate immune context", universalCausalityClaimed := false },
  { from := .epithelialBarrierFibre, to := .mucosalImmuneMastCellFibre, coupling := .transportBarrier,
    evidenceReference := "DGBI permeability literature and Gao mechanistic IBS-D trial",
    reverseOrFeedbackReference := "immune mediators and stress/autonomic outputs can alter barrier function", universalCausalityClaimed := false },
  { from := .autonomicHPAAllostaticFibre, to := .entericMotilitySecretionFibre, coupling := .endocrine,
    evidenceReference := "brain-gut literature: autonomic/HPA outputs participate in motility, secretion and permeability",
    reverseOrFeedbackReference := "gut afference/pain/endocrine signals feed back centrally", universalCausalityClaimed := false },
  { from := .visceralSensoryNociceptiveFibre, to := .centralPainInteroceptiveFibre, coupling := .neural,
    evidenceReference := "DGBI literature: visceral afference and central pain processing interact",
    reverseOrFeedbackReference := "descending/autonomic regulation changes gut-state gain", universalCausalityClaimed := false },
  { from := .dietExposureFibre, to := .microbiomeMetaboliteFibre, coupling := .biochemical,
    evidenceReference := "diet/FODMAP and microbiome studies alter substrate availability and downstream physiology",
    reverseOrFeedbackReference := "microbial metabolism changes effective host exposure", universalCausalityClaimed := false },
  { from := .neurochemicalMetabolicFibre, to := .visceralSensoryNociceptiveFibre, coupling := .biochemical,
    evidenceReference := "histamine, serotonin, GABA and bile-acid/metabolic signalling remain compartment/receptor-specific candidates",
    reverseOrFeedbackReference := "symptoms do not identify the generating mediator", universalCausalityClaimed := false }
]

inductive InflammationIsCompleteIBSCausePermission : Prop
inductive HistamineIsCompleteIBSCausePermission : Prop
inductive GutOnlyIBSPermission : Prop
inductive BrainOnlyIBSPermission : Prop
inductive QuailLocalFibreEqualsWholeSystemTherapyPermission : Prop

theorem inflammationDoesNotExhaustIBS : InflammationIsCompleteIBSCausePermission → False := by intro h; cases h
theorem histamineDoesNotExhaustIBS : HistamineIsCompleteIBSCausePermission → False := by intro h; cases h
theorem gutOnlyModelDoesNotExhaustDGBI : GutOnlyIBSPermission → False := by intro h; cases h
theorem brainOnlyModelDoesNotExhaustDGBI : BrainOnlyIBSPermission → False := by intro h; cases h
theorem quailLocalFibreDoesNotEqualWholeSystemTherapy : QuailLocalFibreEqualsWholeSystemTherapyPermission → False := by intro h; cases h

structure IBSWholeSystemBoundary where
  recurrentBidirectionalGraphRetained : Bool
  inflammationMayBeMechanisticallyRelevant : Bool
  inflammationIsUniversalMasterCause : Bool
  histamineMayBeMechanisticallyRelevant : Bool
  histamineIsUniversalMasterCause : Bool
  autonomicHPAStateRetained : Bool
  centralInteroceptivePainStateRetained : Bool
  microbiomeMetaboliteStateRetained : Bool
  barrierStateRetained : Bool
  motilitySecretionStateRetained : Bool
  quailInterventionActsOnLocalCandidateFibre : Bool
  localMechanismDoesNotEqualWholeSystemClosure : Bool
  agdaOwnerReferences : String
  deriving Repr, DecidableEq

def canonicalIBSWholeSystemBoundary : IBSWholeSystemBoundary := {
  recurrentBidirectionalGraphRetained := true
  inflammationMayBeMechanisticallyRelevant := true
  inflammationIsUniversalMasterCause := false
  histamineMayBeMechanisticallyRelevant := true
  histamineIsUniversalMasterCause := false
  autonomicHPAStateRetained := true
  centralInteroceptivePainStateRetained := true
  microbiomeMetaboliteStateRetained := true
  barrierStateRetained := true
  motilitySecretionStateRetained := true
  quailInterventionActsOnLocalCandidateFibre := true
  localMechanismDoesNotEqualWholeSystemClosure := true
  agdaOwnerReferences := "HistamineCompartmentClearanceExact; Levin.MicrobiomeHostAppetiteBoundary; AllostaticBodyStateExact; EmbodiedOptionConeInteroceptionExact; QuailEggHistamineGutSnowballExact"
}

end Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact
