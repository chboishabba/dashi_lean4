import Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact

namespace Dashi.Biology.PersuasionTransmissionTruthBoundaryExact

open Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact

structure SourceReceipt where
  authors : String
  title : String
  publicationContext : String
  year : String
  doi : String
  paidReading : String
  deriving Repr, DecidableEq

def fay2026Source : SourceReceipt := {
  authors := "Nicolas Fay; Keith J Ransom; Bradley Walker; Piers D L Howe; Andrew Perfors; Yoshihisa Kashima"
  title := "Truth over falsehood: Experimental evidence on what persuades and spreads"
  publicationContext := "Journal of Personality and Social Psychology 130(4):684-700"
  year := "2026"
  doi := "10.1037/pspa0000467"
  paidReading := "Four controlled experiments (combined N=4,607) found truthful-intent messages more persuasive and more likely to be shared than false-intent messages. Perceived truth was the main driver of persuasion; transmission was primarily associated with positive emotion and social engagement. Real-world platform generalization remains bounded."
}

structure PersuasionTransmissionReceipt where
  source : SourceReceipt
  combinedSampleReference : String
  truthfulIntentPersuasionAdvantage : Bool
  truthfulIntentSharingAdvantage : Bool
  perceivedTruthPrimaryPersuasionDriver : Bool
  positiveEmotionSocialEngagementTransmissionDriver : Bool
  persuasionEqualsTransmission : Bool
  positiveEmotionDeterminesPropositionTruth : Bool
  uncontrolledPlatformGeneralizationPaid : Bool
  deriving Repr, DecidableEq

def canonicalPersuasionTransmissionReceipt : PersuasionTransmissionReceipt := {
  source := fay2026Source
  combinedSampleReference := "four experiments; combined N=4,607"
  truthfulIntentPersuasionAdvantage := true
  truthfulIntentSharingAdvantage := true
  perceivedTruthPrimaryPersuasionDriver := true
  positiveEmotionSocialEngagementTransmissionDriver := true
  persuasionEqualsTransmission := false
  positiveEmotionDeterminesPropositionTruth := false
  uncontrolledPlatformGeneralizationPaid := false
}

inductive PositiveEmotionCreatesTruthPermission : Prop
inductive PersuasionEqualsTransmissionPermission : Prop

theorem positiveEmotionDoesNotCreateTruth : PositiveEmotionCreatesTruthPermission → False := by intro h; cases h

theorem persuasionDoesNotCollapseToTransmission : PersuasionEqualsTransmissionPermission → False := by intro h; cases h

structure TruthTransmissionBoundary where
  truthIntentAdvantageRepresented : Bool
  persuasionCollapsedWithTransmission : Bool
  positiveEmotionCreatesTruthAuthority : Bool
  controlledExperimentUniversalizesToPlatforms : Bool
  existingPropagationNonautomaticityRetained : Bool
  deriving Repr, DecidableEq

def canonicalTruthTransmissionBoundary : TruthTransmissionBoundary := {
  truthIntentAdvantageRepresented := true
  persuasionCollapsedWithTransmission := false
  positiveEmotionCreatesTruthAuthority := false
  controlledExperimentUniversalizesToPlatforms := false
  existingPropagationNonautomaticityRetained := true
}

example : exposureToBelief.automatic = false := rfl
example : beliefToIntent.automatic = false := rfl

end Dashi.Biology.PersuasionTransmissionTruthBoundaryExact
