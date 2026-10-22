import Dashi.Biology.NeuralPredictionDirectionExact

namespace Dashi.Biology.BCICalibrationAgencyBridgeExact

open Dashi.Biology.NeuralPredictionDirectionExact

inductive ParticipationBurdenCoordinate where
  | calibrationTimeBurden
  | setupAndMaintenanceBurden
  | cognitiveTaskBurden
  | failureRecoveryBurden
  | reportingAndStudyBurden
  deriving Repr, DecidableEq

inductive ParticipantOutcomeCoordinate where
  | participantReportedAgency
  | participantReportedSatisfaction
  | functionalIndependence
  | clinicalBenefit
  | qualityOfLife
  deriving Repr, DecidableEq

structure BCICalibrationAgencyBridge where
  provenance : NeuralinkProvenanceSplit
  aliceBrownOwnerReference : String
  calibrationBurden : ParticipationBurdenCoordinate
  externalPerformanceReference : String
  participantExperienceReference : String
  reducedBurdenMayExpandReachability : Bool
  reducedBurdenEqualsAgency : Bool
  companyPerformanceMetricEqualsParticipantExperience : Bool
  participantVoiceRequiredForParticipantExperienceClaim : Bool
  deriving Repr, DecidableEq

def canonicalBCICalibrationAgencyBridge : BCICalibrationAgencyBridge := {
  provenance := canonicalNeuralinkProvenanceSplit
  aliceBrownOwnerReference := "DASHI.Biology.AliceBrownThreadInquirySynthesisExact: accessDoesNotEqualAgency; adultObservationDoesNotEqualChildExperience; capabilityExpansionWithoutDomination"
  calibrationBurden := .calibrationTimeBurden
  externalPerformanceReference := "decoder calibration frequency/time, longitudinal decoder stability and task throughput"
  participantExperienceReference := "participant-reported burden, preference, satisfaction, experienced autonomy and situated use context remain separate evidence coordinates"
  reducedBurdenMayExpandReachability := true
  reducedBurdenEqualsAgency := false
  companyPerformanceMetricEqualsParticipantExperience := false
  participantVoiceRequiredForParticipantExperienceClaim := true
}

inductive ReducedCalibrationCreatesAgencyPermission : Prop
inductive ExternalMetricCreatesParticipantExperiencePermission : Prop

theorem reducedCalibrationDoesNotDefinitionallyCreateAgency :
    ReducedCalibrationCreatesAgencyPermission → False := by
  intro h
  cases h

theorem externalMetricDoesNotCreateParticipantExperience :
    ExternalMetricCreatesParticipantExperiencePermission → False := by
  intro h
  cases h

structure BCICalibrationAgencyBoundary where
  calibrationBurdenRepresented : Bool
  capabilityExpansionReadingAvailable : Bool
  accessAutomaticallyEqualsAgency : Bool
  performanceAutomaticallyEqualsExperience : Bool
  clinicalBenefitAutomaticallyEstablished : Bool
  participantVoiceRemainsIndependentEvidence : Bool
  deriving Repr, DecidableEq

def canonicalBCICalibrationAgencyBoundary : BCICalibrationAgencyBoundary := {
  calibrationBurdenRepresented := true
  capabilityExpansionReadingAvailable := true
  accessAutomaticallyEqualsAgency := false
  performanceAutomaticallyEqualsExperience := false
  clinicalBenefitAutomaticallyEstablished := false
  participantVoiceRemainsIndependentEvidence := true
}

end Dashi.Biology.BCICalibrationAgencyBridgeExact
