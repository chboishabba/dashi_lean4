import AgdaMirror.Governance.ExternalThreatRepressionMechanismTransfer

namespace AgdaMirror.Governance.IranThreatRepressionCaseNarrowing

open AgdaMirror.Governance.ExternalThreatRepressionMechanismTransfer

structure CaseNarrowingReceipt where
  generalTransfer : CaseTransferReceipt
  currentSourceRef : String
  preExistingRepressionRetained : Bool := true
  externalThreatSurfacePaid : Bool := true
  intensifiedControlSurfacePaid : Bool := true
  mobilisationShiftPaid : Bool := true
  marginalRepressionIncrementIdentified : Bool := false
  externalThreatNecessaryForRepression : Bool := false

def canonicalIranCaseNarrowing : CaseNarrowingReceipt :=
  ⟨iran2026Transfer, "Reuters 2026-10-01"⟩

structure SameEpisodeResidual where
  residualRef : String
  requiredObject : String
  identificationTarget : String
  retainedCounterHypotheses : String
  mayPromoteGeneralMechanismToCase : Bool := false

def sameEpisodeResidual : SameEpisodeResidual :=
  ⟨"residual:iran-2026:marginal-repression-increment",
   "same-episode policy/order/timing record, subnational exposure design, or other Iran-specific evidence identifying repression change after external-threat exposure",
   "marginal repression attributable to external threat, not total observed repression",
   "pre-existing coercive institutions; protest intensity; economic crisis; regime-security incentives; foreign-agent framing; state-capacity adaptation"⟩

theorem narrowing_remains_open :
    canonicalIranCaseNarrowing.marginalRepressionIncrementIdentified = false ∧
    canonicalIranCaseNarrowing.externalThreatNecessaryForRepression = false := by
  decide

end AgdaMirror.Governance.IranThreatRepressionCaseNarrowing
