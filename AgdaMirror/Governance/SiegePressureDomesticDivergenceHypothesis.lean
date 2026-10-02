namespace AgdaMirror.Governance.SiegePressureDomesticDivergenceHypothesis

inductive PressureAxis
  | externalMilitaryThreat | sanctionsOrBlockade | fiscalResourceConstraint
  | domesticEconomicPolicy | infrastructureFragility | domesticDissent
  | coerciveStateResponse | externalDeterrenceStrategy
  deriving DecidableEq, Repr

inductive MechanismHypothesisKind
  | siegePressureContributes
  | domesticGovernanceContributes
  | securityFramingRoutesDissent
  | foreignPolicyLegitimacySubstitution
  | coercionMaintainsExternalStrategy
  deriving DecidableEq, Repr

structure MechanismHypothesis where
  kind : MechanismHypothesisKind
  caseRef : String
  sourceRefs : List String
  counterHypothesisRef : String
  reviewedAsCausalMechanism : Bool := false

def iranSiegeHypothesis : MechanismHypothesis :=
  ⟨.siegePressureContributes,
   "Iran-2026",
   ["Reuters 2026-09-29 economic strain", "Reuters 2026-10-01 strategic posture"],
   "domestic governance, distributive choices, institutional interests, ideology, and wartime damage may independently or jointly explain outcomes"⟩

def cubaSiegeHypothesis : MechanismHypothesis :=
  ⟨.siegePressureContributes,
   "Cuba-2026",
   ["House of Commons Library 2026-08-17", "Reuters 2026-09-18 grid collapse"],
   "domestic economic structure, aging infrastructure, natural shocks and policy choices remain independent contributors"⟩

structure IranCubaComparisonBoundary where
  externalPressureComparable : Bool := true
  internalInstitutionsComparable : Bool := true
  sameHistoricalMechanism : Bool := false
  sameThreatMagnitude : Bool := false
  sameRepressionPattern : Bool := false
  sanctionsAloneExplainOutcome : Bool := false
  domesticPolicyAloneExplainsOutcome : Bool := false

def canonicalBoundary : IranCubaComparisonBoundary := {}

theorem comparison_preserves_nonidentity :
    canonicalBoundary.sameHistoricalMechanism = false ∧
    canonicalBoundary.sanctionsAloneExplainOutcome = false ∧
    canonicalBoundary.domesticPolicyAloneExplainsOutcome = false := by
  decide

end AgdaMirror.Governance.SiegePressureDomesticDivergenceHypothesis
