import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.QuailEggHumanOralTransferExact
open Dashi.Biology.GABAPhenotypeEvidenceExact

def benichou2014Source : AttributedSource :=
  mkDOISource
    "Annie-Claude Benichou; Marion Armanet; Anthony Bussière; Nathalie Chevreau; Jean-Michel Cardot; Jan Tétard"
    "A proprietary blend of quail egg for the attenuation of nasal provocation with a standardized allergenic challenge: a randomized, double-blind, placebo-controlled study"
    "Food Science & Nutrition 2(6):655-663" "2014"
    "10.1002/fsn3.147" "https://doi.org/10.1002/fsn3.147"
    "Randomized double-blind crossover human oral exposure to a proprietary quail-egg blend in an allergen-provocation/rhinitis paradigm; not IBS efficacy or gut target engagement."

def andaloro2023Source : AttributedSource :=
  mkDOISource
    "Claudio Andaloro; A M Saibene; Ignazio La Mantia"
    "Quail egg homogenate with zinc as adjunctive therapy in seasonal allergic rhinitis: a randomised, controlled trial"
    "Journal of Laryngology & Otology 137(4):432-437" "2023"
    "10.1017/S0022215122001219" "https://doi.org/10.1017/S0022215122001219"
    "Randomized seasonal-rhinitis adjunctive result for mometasone plus oral quail-egg-and-zinc tablets; combination treatment does not isolate quail-only effect."

inductive HumanOralQuailContext where
  | acuteAllergenProvocation | seasonalAllergicRhinitisAdjunctive
  deriving Repr, DecidableEq
inductive ProductIdentity where
  | proprietaryQuailBlend | quailEggPlusZincCombination
  deriving Repr, DecidableEq

structure HumanOralQuailEvidenceReceipt where
  source : AttributedSource
  context : HumanOralQuailContext
  product : ProductIdentity
  randomizedHumanExposure : Bool
  oralExposurePaid : Bool
  gutTargetEngagementPaid : Bool
  ibsEndpointPaid : Bool
  componentIsolationPaid : Bool
  boundary : String
  deriving Repr, DecidableEq

def benichou2014Receipt : HumanOralQuailEvidenceReceipt := {
  source := benichou2014Source
  context := .acuteAllergenProvocation
  product := .proprietaryQuailBlend
  randomizedHumanExposure := true
  oralExposurePaid := true
  gutTargetEngagementPaid := false
  ibsEndpointPaid := false
  componentIsolationPaid := false
  boundary := "Human oral exposure and rhinitis/allergen-challenge outcome are paid; IBS, intestinal histamine/DAO and gut mast-cell target engagement remain unpaid."
}

def andaloro2023Receipt : HumanOralQuailEvidenceReceipt := {
  source := andaloro2023Source
  context := .seasonalAllergicRhinitisAdjunctive
  product := .quailEggPlusZincCombination
  randomizedHumanExposure := true
  oralExposurePaid := true
  gutTargetEngagementPaid := false
  ibsEndpointPaid := false
  componentIsolationPaid := false
  boundary := "Adjunctive human rhinitis evidence is paid, but zinc and mometasone co-treatment block unique quail attribution."
}

inductive RhinitisEvidencePaysIBSPermission : Prop
inductive QuailPlusZincIdentifiesQuailEffectPermission : Prop
inductive OralExposureEqualsGutTargetEngagementPermission : Prop

theorem rhinitisEvidenceDoesNotPayIBS : RhinitisEvidencePaysIBSPermission → False := by intro h; cases h
theorem combinationDoesNotIdentifyQuailEffect : QuailPlusZincIdentifiesQuailEffectPermission → False := by intro h; cases h
theorem oralExposureDoesNotEqualGutTargetEngagement : OralExposureEqualsGutTargetEngagementPermission → False := by intro h; cases h

structure QuailHumanOralTransferBoundary where
  humanOralExposureNowPaid : Bool
  humanRhinitisOutcomeNowPaid : Bool
  humanIBSEfficacyPaid : Bool
  gutMechanisticTargetEngagementPaid : Bool
  combinationTherapyIdentifiesQuailOnlyEffect : Bool
  deriving Repr, DecidableEq

def canonicalQuailHumanOralTransferBoundary : QuailHumanOralTransferBoundary := {
  humanOralExposureNowPaid := true
  humanRhinitisOutcomeNowPaid := true
  humanIBSEfficacyPaid := false
  gutMechanisticTargetEngagementPaid := false
  combinationTherapyIdentifiesQuailOnlyEffect := false
}

end Dashi.Biology.QuailEggHumanOralTransferExact
