namespace AgdaMirror.Governance.AUKUSEmbeddedAuthorityCommandNoncollapse

inductive DocumentaryAuthorityLevel
  | publicPrimaryDocument
  | secondaryReproductionOfNonPublicPrimary
  | secondaryCharacterisationOnly
  deriving DecidableEq, Repr

structure EmbeddedAuthorityReceipt where
  documentaryLevel : DocumentaryAuthorityLevel
  sourceRef : String
  lawfulReasonableDirectionsAttributed : Bool := true
  disciplinaryConsequenceAttributed : Bool := true
  explicitNoCommandClauseAttributed : Bool := true
  primaryDirectiveAcquired : Bool := false
  primaryMOUAcquired : Bool := false
  appliesToIRISSameEpisodeTask : Bool := false


def canonicalAuthorityReceipt : EmbeddedAuthorityReceipt :=
  ⟨.secondaryReproductionOfNonPublicPrimary,
   "The Nightly 2026-05-04 / Michael West Media 2026-05-12"⟩

structure DirectionCommandBoundary where
  additionalDirectionAuthorityAttributed : Bool := true
  formalCommandDelegationAttributed : Bool := false
  authorityEqualsCommand : Bool := false
  commandStatusSettlesSovereignty : Bool := false
  protocolRuleSettlesActualDuty : Bool := false


def canonicalBoundary : DirectionCommandBoundary := {}

theorem authority_does_not_collapse_to_command :
    canonicalAuthorityReceipt.primaryDirectiveAcquired = false ∧
    canonicalAuthorityReceipt.primaryMOUAcquired = false ∧
    canonicalBoundary.additionalDirectionAuthorityAttributed = true ∧
    canonicalBoundary.formalCommandDelegationAttributed = false ∧
    canonicalBoundary.authorityEqualsCommand = false ∧
    canonicalBoundary.protocolRuleSettlesActualDuty = false := by
  decide

end AgdaMirror.Governance.AUKUSEmbeddedAuthorityCommandNoncollapse
