namespace AgdaMirror.Governance.ChinaTaiwanHistoricalSuccessionIdentity

inductive PoliticalEntity
  | republicOfChina | peoplesRepublicOfChina | rocGovernmentOnTaiwan | democraticTaiwanPolity
  deriving DecidableEq, Repr

inductive SuccessionRelation
  | civilWarRivalGovernmentRelation
  | authoritarianContinuityRelation
  | democratisationTransformationRelation
  | presentContestedSovereigntyRelation
  deriving DecidableEq, Repr

structure HistoricalTransition where
  from : PoliticalEntity
  to : PoliticalEntity
  relation : SuccessionRelation
  sourceReceipt : String
  sameInstitutionalSystem : Bool := false
  settlesPresentSovereignty : Bool := false
  determinesPresentPopulationIdentity : Bool := false

def rocCivilWarRetreat : HistoricalTransition :=
  ⟨.republicOfChina, .rocGovernmentOnTaiwan, .civilWarRivalGovernmentRelation,
   "1949 ROC/KMT retreat to Taiwan after defeat by CCP in Chinese Civil War"⟩

def rocAuthoritarianToDemocraticTaiwan : HistoricalTransition :=
  ⟨.rocGovernmentOnTaiwan, .democraticTaiwanPolity, .democratisationTransformationRelation,
   "martial law lifted 1987; first direct presidential election 1996"⟩

theorem transitions_do_not_settle_present_status :
    rocCivilWarRetreat.settlesPresentSovereignty = false ∧
    rocAuthoritarianToDemocraticTaiwan.settlesPresentSovereignty = false := by
  decide

end AgdaMirror.Governance.ChinaTaiwanHistoricalSuccessionIdentity
