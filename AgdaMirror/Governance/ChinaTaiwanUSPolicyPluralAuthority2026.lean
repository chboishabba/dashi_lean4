namespace AgdaMirror.Governance.ChinaTaiwanUSPolicyPluralAuthority2026

inductive USPolicyLayer
  | diplomaticRecognitionLayer | oneChinaPolicyLayer | taiwanRelationsActLayer
  | executiveBargainingLayer | congressionalSecurityLayer | partyCoalitionLayer
  | semiconductorIndustrialLayer
  deriving DecidableEq, Repr

inductive USActor
  | usExecutive | usCongress | republicanSenators | democraticLegislators
  | usStateDepartment | usDefenseDepartment
  deriving DecidableEq, Repr

structure PolicyPosition where
  actor : USActor
  layer : USPolicyLayer
  proposition : String
  sourceReceipt : String
  speaksForWholeUnitedStates : Bool := false
  speaksForWholeParty : Bool := false
  settlesTaiwanSovereignty : Bool := false

def trumpAdministrationUnchangedPolicy : PolicyPosition :=
  ⟨.usExecutive, .oneChinaPolicyLayer,
   "current administration representatives report no change in longstanding U.S. Taiwan policy",
   "Reuters 2026-09-25"⟩

def wickerSecurityPressure : PolicyPosition :=
  ⟨.republicanSenators, .congressionalSecurityLayer,
   "Wicker and other Republican senators press administration over delayed Taiwan security assistance",
   "Reuters 2026-09-30"⟩

theorem current_positions_are_not_total_authority :
    trumpAdministrationUnchangedPolicy.speaksForWholeUnitedStates = false ∧
    wickerSecurityPressure.speaksForWholeParty = false ∧
    trumpAdministrationUnchangedPolicy.settlesTaiwanSovereignty = false ∧
    wickerSecurityPressure.settlesTaiwanSovereignty = false := by
  decide

end AgdaMirror.Governance.ChinaTaiwanUSPolicyPluralAuthority2026
