namespace DASHI.GenderedNormApproval

/-!
A Lean mirror of the Agda structural result.

This file does not prove an empirical theory of patriarchy or women.
It proves only that several coarse observations fail to determine
downstream answers in finite witnesses.
-/

inductive ProtocolWorld where
  | rewardWithoutRefusalSanction
  | rewardWithRefusalSanction
  deriving DecidableEq

inductive RefusalSanctionAnswer where
  | noRefusalSanction
  | refusalIsSanctioned
  deriving DecidableEq

def relatabilityRewardSurface : ProtocolWorld → Unit := fun _ => ()

def refusalSanctionAnswer : ProtocolWorld → RefusalSanctionAnswer
  | .rewardWithoutRefusalSanction => .noRefusalSanction
  | .rewardWithRefusalSanction => .refusalIsSanctioned

def FactorsThrough {α β γ : Type} (project : α → β) (answer : α → γ) : Prop :=
  ∃ coarse : β → γ, ∀ x, answer x = coarse (project x)

theorem relatabilityRewardDoesNotDetermineRefusalSanction :
    ¬ FactorsThrough relatabilityRewardSurface refusalSanctionAnswer := by
  rintro ⟨coarse, h⟩
  have h₁ := h ProtocolWorld.rewardWithoutRefusalSanction
  have h₂ := h ProtocolWorld.rewardWithRefusalSanction
  have bad :
      RefusalSanctionAnswer.noRefusalSanction =
        RefusalSanctionAnswer.refusalIsSanctioned := by
    exact h₁.trans h₂.symm
  cases bad

inductive LikeRespectWorld where
  | likedLowRespect
  | likedHighRespect
  deriving DecidableEq

inductive RespectAnswer where
  | lowerRespect
  | higherRespect
  deriving DecidableEq

def likabilitySurface : LikeRespectWorld → Unit := fun _ => ()

def respectAnswer : LikeRespectWorld → RespectAnswer
  | .likedLowRespect => .lowerRespect
  | .likedHighRespect => .higherRespect

theorem likabilityDoesNotDetermineRespect :
    ¬ FactorsThrough likabilitySurface respectAnswer := by
  rintro ⟨coarse, h⟩
  have h₁ := h LikeRespectWorld.likedLowRespect
  have h₂ := h LikeRespectWorld.likedHighRespect
  have bad : RespectAnswer.lowerRespect = RespectAnswer.higherRespect := by
    exact h₁.trans h₂.symm
  cases bad

inductive LikeLoyaltyWorld where
  | likedLowLoyalty
  | likedHighLoyalty
  deriving DecidableEq

inductive LoyaltyAnswer where
  | lowerLoyalty
  | higherLoyalty
  deriving DecidableEq

def likabilityLoyaltySurface : LikeLoyaltyWorld → Unit := fun _ => ()

def loyaltyAnswer : LikeLoyaltyWorld → LoyaltyAnswer
  | .likedLowLoyalty => .lowerLoyalty
  | .likedHighLoyalty => .higherLoyalty

theorem likabilityDoesNotDetermineLoyalty :
    ¬ FactorsThrough likabilityLoyaltySurface loyaltyAnswer := by
  rintro ⟨coarse, h⟩
  have h₁ := h LikeLoyaltyWorld.likedLowLoyalty
  have h₂ := h LikeLoyaltyWorld.likedHighLoyalty
  have bad : LoyaltyAnswer.lowerLoyalty = LoyaltyAnswer.higherLoyalty := by
    exact h₁.trans h₂.symm
  cases bad

structure Boundary where
  sourceTranscriptAutomaticallyEstablishesPatriarchyMechanism : Bool
  rewardForRelatabilityAutomaticallyImpliesSanctionForRefusal : Bool
  likabilityAutomaticallyImpliesRespect : Bool
  likabilityAutomaticallyImpliesLoyalty : Bool
  fearAutomaticallyIdenticalToRespect : Bool
  machiavelliAppealAutomaticallyProvesStrategy : Bool
  softwareMetaphorAutomaticallyIdentifiesLiteralBackend : Bool
  structuralCollisionCanRefuteLogicalEntailment : Bool
  empiricalApplicationRequiresExternalEvidence : Bool
  sourceClaimAndRepositoryTheoremRemainDistinct : Bool
  deriving DecidableEq

def canonicalBoundary : Boundary where
  sourceTranscriptAutomaticallyEstablishesPatriarchyMechanism := false
  rewardForRelatabilityAutomaticallyImpliesSanctionForRefusal := false
  likabilityAutomaticallyImpliesRespect := false
  likabilityAutomaticallyImpliesLoyalty := false
  fearAutomaticallyIdenticalToRespect := false
  machiavelliAppealAutomaticallyProvesStrategy := false
  softwareMetaphorAutomaticallyIdentifiesLiteralBackend := false
  structuralCollisionCanRefuteLogicalEntailment := true
  empiricalApplicationRequiresExternalEvidence := true
  sourceClaimAndRepositoryTheoremRemainDistinct := true

inductive SourceClaim where
  | patriarchyAsSoftwareMetaphor
  | relatabilityRewardClaim
  | noRefusalPunishmentClaim
  | likabilityVersusRespectClaim
  | likabilityVersusLoyaltyClaim
  | approvalIndependenceStrategyClaim
  | machiavelliRhetoricalAppeal
  | reprogramSystemMetaphor
  deriving DecidableEq

inductive ClaimStatus where
  | attributedSourceClaim
  | externalEvidenceRequired
  deriving DecidableEq

def claimStatus : SourceClaim → ClaimStatus
  | .patriarchyAsSoftwareMetaphor => .attributedSourceClaim
  | .relatabilityRewardClaim => .externalEvidenceRequired
  | .noRefusalPunishmentClaim => .externalEvidenceRequired
  | .likabilityVersusRespectClaim => .externalEvidenceRequired
  | .likabilityVersusLoyaltyClaim => .externalEvidenceRequired
  | .approvalIndependenceStrategyClaim => .externalEvidenceRequired
  | .machiavelliRhetoricalAppeal => .attributedSourceClaim
  | .reprogramSystemMetaphor => .attributedSourceClaim

theorem fearNotPromotedToRespect :
    canonicalBoundary.fearAutomaticallyIdenticalToRespect = false := rfl

theorem transcriptNotPromotedToEmpiricalProof :
    canonicalBoundary.sourceTranscriptAutomaticallyEstablishesPatriarchyMechanism = false := rfl

theorem empiricalApplicationStillRequiresEvidence :
    canonicalBoundary.empiricalApplicationRequiresExternalEvidence = true := rfl

end DASHI.GenderedNormApproval
