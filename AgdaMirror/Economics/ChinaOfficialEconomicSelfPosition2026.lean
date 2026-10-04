namespace AgdaMirror.Economics.ChinaOfficialEconomicSelfPosition2026

inductive OfficialLeadershipClaim
  | secondLargestEconomy | largestManufacturingPower | largestGoodsTrader
  | secondLargestConsumerMarket | globalGrowthEngineClaim | comprehensiveEconomicVictoryClaim
  deriving DecidableEq, Repr

structure SelfPositionReceipt where
  claim : OfficialLeadershipClaim
  reading : String
  sourceReceipt : String
  officialSelfAssertion : Bool := true
  independentlyClosesComprehensiveLeadership : Bool := false
  independentlyClosesEconomicVictory : Bool := false

def manufacturingSelfPosition : SelfPositionReceipt :=
  ⟨.largestManufacturingPower,
   "China officially describes itself as the world's largest manufacturing country/power.",
   "State Council / Xi Focus 2026-09-19"⟩

def broadSelfPosition : SelfPositionReceipt :=
  ⟨.largestGoodsTrader,
   "Chinese MFA materials describe China as second-largest economy and largest goods trader/manufacturing power.",
   "PRC MFA 2026-09-18"⟩

theorem official_self_position_does_not_close_victory :
    manufacturingSelfPosition.independentlyClosesEconomicVictory = false ∧
    broadSelfPosition.independentlyClosesComprehensiveLeadership = false := by
  decide

end AgdaMirror.Economics.ChinaOfficialEconomicSelfPosition2026
