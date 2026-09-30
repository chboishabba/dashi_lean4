namespace AgdaMirror.Governance.AustraliaUSAllianceSovereigntyGenealogy

inductive SovereigntyCoordinate
  | allianceIntimacy | militaryInteroperability | basingAndOperationalAccess
  | industrialDependence | commandAutonomy | foreignPolicyFreedom | intelligenceInfrastructure
  deriving DecidableEq, Repr

structure SovereigntyClaim where
  coordinate : SovereigntyCoordinate
  claimant : String
  reading : String
  sourceReceipt : String
  establishedAsFinalFact : Bool := false

def holtAllianceIntimacy : SovereigntyClaim :=
  ⟨.allianceIntimacy, "historical Holt government",
   "Vietnam-era Australia publicly embraced unusually close U.S. alliance identification.",
   "National Archives of Australia" , true⟩

def marlesEnhancesSovereignty : SovereigntyClaim :=
  ⟨.industrialDependence, "Richard Marles / Australian government",
   "AUKUS capability cooperation is presented as enhancing sovereignty.",
   "ABC 2023-02-09"⟩

def hastieDiminishesSovereignty : SovereigntyClaim :=
  ⟨.foreignPolicyFreedom, "Andrew Hastie",
   "Deep U.S. reliance from Pine Gap to AUKUS is argued to diminish sovereignty.",
   "ABC RN 2026-09-03"⟩

theorem opposed_sovereignty_claims_remain_attributed :
    marlesEnhancesSovereignty.establishedAsFinalFact = false ∧
    hastieDiminishesSovereignty.establishedAsFinalFact = false := by
  decide

end AgdaMirror.Governance.AustraliaUSAllianceSovereigntyGenealogy
