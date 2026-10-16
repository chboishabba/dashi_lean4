import Dashi.Biology.QuailEggHistamineGutSnowballExact
import Dashi.Biology.QuailEggGutTransferRound2Exact

namespace Dashi.Biology.GutMastCellMechanismRouteAtlasExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.QuailEggHistamineGutSnowballExact
open Dashi.Biology.QuailEggGutTransferRound2Exact

inductive RouteInput where
  | quailAlbumenExposure | microbialHistamine | fecalLPS | releasedHistamine
  deriving Repr, DecidableEq
inductive RouteTarget where
  | par2MAPKNFkBCellSignalling | histamineH4Receptor | mastCellTLR4 | histamineH1TRPV1SensoryAxis
  deriving Repr, DecidableEq
inductive RouteEndpoint where
  | degranulationMediatorRelease | visceralHypersensitivityAndMastCellAccumulation
  | colonicBarrierDysfunction | visceralSensoryNeuronSensitization
  deriving Repr, DecidableEq

structure MastCellMechanismRoute where
  source : AttributedSource
  input : RouteInput
  target : RouteTarget
  endpoint : RouteEndpoint
  evidenceSurface : String
  routeReading : String
  exactTargetIdentityPaid : Bool
  humanIBSEfficacyPaid : Bool
  deriving Repr, DecidableEq

def quailAlbumenPAR2Route : MastCellMechanismRoute := {
  source := lianto2018Source
  input := .quailAlbumenExposure
  target := .par2MAPKNFkBCellSignalling
  endpoint := .degranulationMediatorRelease
  evidenceSurface := "HMC-1 cell assays plus mouse PCA"
  routeReading := "Quail albumen suppressed degranulation mediators and altered PAR2-associated MAPK/NF-kB signalling; unique molecular target and human IBS efficacy remain unpaid."
  exactTargetIdentityPaid := false
  humanIBSEfficacyPaid := false
}

def microbialHistamineH4Route : MastCellMechanismRoute := {
  source := dePalma2022Source
  input := .microbialHistamine
  target := .histamineH4Receptor
  endpoint := .visceralHypersensitivityAndMastCellAccumulation
  evidenceSurface := "human IBS microbiome stratification plus mouse transfer mechanism"
  routeReading := "Microbial histamine/H4 is a bounded visceral-hypersensitivity route."
  exactTargetIdentityPaid := true
  humanIBSEfficacyPaid := false
}

def fecalLPSTLR4Route : MastCellMechanismRoute := {
  source := gao2025Source
  input := .fecalLPS
  target := .mastCellTLR4
  endpoint := .colonicBarrierDysfunction
  evidenceSurface := "human IBS-D dietary-mechanism trial plus pharmacologic/knockout/reconstitution mouse experiments"
  routeReading := "LPS/TLR4 mast-cell barrier dysfunction remains distinct from histamine/H4."
  exactTargetIdentityPaid := true
  humanIBSEfficacyPaid := false
}

def histamineH1TRPV1Route : MastCellMechanismRoute := {
  source := wouters2016Source
  input := .releasedHistamine
  target := .histamineH1TRPV1SensoryAxis
  endpoint := .visceralSensoryNeuronSensitization
  evidenceSurface := "human biopsy/sensory-neuron mechanism plus randomized ebastine intervention"
  routeReading := "H1/TRPV1 sensory sensitization remains distinct from H4, TLR4 and quail-cell signalling."
  exactTargetIdentityPaid := true
  humanIBSEfficacyPaid := false
}

inductive SameMastCellWordImpliesSameMechanismPermission : Prop
inductive SuppressingOneRouteTreatsAllHistamineIBSPermission : Prop

theorem sameMastCellWordDoesNotIdentifyMechanism : SameMastCellWordImpliesSameMechanismPermission → False := by intro h; cases h
theorem oneRouteSuppressionDoesNotTreatAllIBS : SuppressingOneRouteTreatsAllHistamineIBSPermission → False := by intro h; cases h

structure GutMastCellMechanismRouteAtlas where
  routes : List MastCellMechanismRoute
  receptorAndTriggerIdentityRetained : Bool
  compartmentAndEndpointIdentityRetained : Bool
  quailRouteDoesNotAutoBridgeToHumanIBS : Bool
  interventionShouldMeasureMultipleRoutesWhenClaimRequiresThem : Bool
  deriving Repr, DecidableEq

def canonicalGutMastCellMechanismRouteAtlas : GutMastCellMechanismRouteAtlas := {
  routes := [quailAlbumenPAR2Route, microbialHistamineH4Route, fecalLPSTLR4Route, histamineH1TRPV1Route]
  receptorAndTriggerIdentityRetained := true
  compartmentAndEndpointIdentityRetained := true
  quailRouteDoesNotAutoBridgeToHumanIBS := true
  interventionShouldMeasureMultipleRoutesWhenClaimRequiresThem := true
}

end Dashi.Biology.GutMastCellMechanismRouteAtlasExact
