namespace Dashi.Biology.SourceCueTruthNoncollapseExact

structure SourceReceipt where
  authors : String
  title : String
  year : String
  doi : String
  paidReading : String
  scopeBoundary : String
  deriving Repr, DecidableEq

def roovers2026Source : SourceReceipt := {
  authors := "Hidde Roovers; Marieke A. Adriaanse; Hedwig M. M. Vos; et al."
  title := "An experimental study of source and engagement cues for susceptibility to dietary supplement misinformation"
  year := "2026"
  doi := "10.1038/s41598-026-74733-8"
  paidReading := "Experimental study in 1,298 Dutch-speaking adults using ten mock dietary-supplement social-media posts. Misleading claims attributed to a fictional health professional were judged more reliable than those attributed to a fictional influencer, largely via perceived source credibility."
  scopeBoundary := "High-versus-low engagement did not change reliability judgements of misleading posts; social-consensus mediation was not supported; source cue effects are judgement effects, not proposition-truth authority."
}

inductive SourceCueOutcomeFamily where
  | rooversMisleadingReliabilityOutcome
  deriving Repr, DecidableEq

inductive AdmittedSourceCueEvidence : SourceCueOutcomeFamily → Type where
  | rooversPaysMisleadingReliabilityOutcome :
      AdmittedSourceCueEvidence .rooversMisleadingReliabilityOutcome
  deriving Repr, DecidableEq

def admittedSourceCueReceipt :
    {family : SourceCueOutcomeFamily} → AdmittedSourceCueEvidence family → SourceReceipt
  | _, .rooversPaysMisleadingReliabilityOutcome => roovers2026Source

structure SourceCueReliabilityReceipt where
  sourceAdmission : AdmittedSourceCueEvidence .rooversMisleadingReliabilityOutcome
  sampleReference : String
  misleadingClaimsAccuracyHeldFixedByStimulusClassification : Bool
  healthProfessionalCueRaisedPerceivedReliability : Bool
  effectLargelyExplainedByPerceivedSourceCredibility : Bool
  highEngagementRaisedMisleadingPostReliability : Bool
  socialConsensusMediationPaid : Bool
  deriving Repr, DecidableEq

namespace SourceCueReliabilityReceipt
def source (r : SourceCueReliabilityReceipt) : SourceReceipt := admittedSourceCueReceipt r.sourceAdmission
end SourceCueReliabilityReceipt

def canonicalSourceCueReliabilityReceipt : SourceCueReliabilityReceipt := {
  sourceAdmission := .rooversPaysMisleadingReliabilityOutcome
  sampleReference := "N=1,298 Dutch-speaking adults; ten mock posts; five misleading and five non-misleading claims"
  misleadingClaimsAccuracyHeldFixedByStimulusClassification := true
  healthProfessionalCueRaisedPerceivedReliability := true
  effectLargelyExplainedByPerceivedSourceCredibility := true
  highEngagementRaisedMisleadingPostReliability := false
  socialConsensusMediationPaid := false
}

inductive SourceCredibilityDeterminesTruthPermission : Prop
inductive PerceivedReliabilityDeterminesTruthPermission : Prop
inductive SourceCueReattributesClaimPermission : Prop

theorem sourceCredibilityDoesNotDetermineTruth :
    SourceCredibilityDeterminesTruthPermission → False := by
  intro h
  cases h

theorem perceivedReliabilityDoesNotDetermineTruth :
    PerceivedReliabilityDeterminesTruthPermission → False := by
  intro h
  cases h

theorem sourceCueDoesNotReattributeClaim :
    SourceCueReattributesClaimPermission → False := by
  intro h
  cases h

structure SourceCueTruthBoundary where
  sourceCueCanAffectPerceivedReliability : Bool
  sourceCueChangesClaimAccuracy : Bool
  perceivedReliabilityCreatesTruthAuthority : Bool
  sourceCredibilityCreatesTruthAuthority : Bool
  sourceCueChangesClaimOwner : Bool
  externalEmpiricalClaimAndDASHISynthesisHaveSeparateOwners : Bool
  deriving Repr, DecidableEq

def canonicalSourceCueTruthBoundary : SourceCueTruthBoundary := {
  sourceCueCanAffectPerceivedReliability := true
  sourceCueChangesClaimAccuracy := false
  perceivedReliabilityCreatesTruthAuthority := false
  sourceCredibilityCreatesTruthAuthority := false
  sourceCueChangesClaimOwner := false
  externalEmpiricalClaimAndDASHISynthesisHaveSeparateOwners := true
}

end Dashi.Biology.SourceCueTruthNoncollapseExact
