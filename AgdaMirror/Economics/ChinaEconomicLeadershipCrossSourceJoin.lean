namespace AgdaMirror.Economics.ChinaEconomicLeadershipCrossSourceJoin

inductive CrossSourceAxis
  | manufacturingAxis | goodsTradeAxis | domesticDemandAxis | highTechUpgradeAxis | financeCurrencyAxis
  deriving DecidableEq, Repr

structure CrossSourceAxisJoin where
  axis : CrossSourceAxis
  officialReading : String
  independentReading : String
  officialSourceRef : String
  independentSourceRef : String
  comparableCoordinate : Bool := true
  agreementOnDimension : Bool
  disagreementOrResidual : String
  createsScalarLeadershipScore : Bool := false
  settlesOverallLeadership : Bool := false

def manufacturingJoin : CrossSourceAxisJoin :=
  ⟨.manufacturingAxis,
   "PRC official materials describe China as the world's largest manufacturing power/country.",
   "Independent IMF evidence describes China as the dominant global manufacturing hub by scale.",
   "ChinaOfficialEconomicSelfPosition2026Exact.manufacturingSelfPosition",
   "AIChinaTSMCGeoEconomicCalibration2026Exact.chinaManufacturingScale",
   true, true,
   "dimension-level convergence does not settle finance, currency, domestic demand or overall leadership"⟩

def domesticDemandJoin : CrossSourceAxisJoin :=
  ⟨.domesticDemandAxis,
   "PRC self-position includes a very large consumer-market claim.",
   "Independent IMF calibration retains weak private domestic demand as a countervailing residual.",
   "ChinaOfficialEconomicSelfPosition2026Exact.broadSelfPosition",
   "AIChinaTSMCGeoEconomicCalibration2026Exact.chinaDomesticDemandResidual",
   true, false,
   "large market scale and strong private domestic demand are different propositions"⟩

structure ChinaEconomicLeadershipJoin where
  axisJoins : List CrossSourceAxisJoin
  officialAndIndependentSourcesSeparated : Bool := true
  positiveAndCountervailingCoordinatesRetained : Bool := true
  scalarWinnerProduced : Bool := false
  comprehensiveVictoryClaimClosed : Bool := false

def canonical : ChinaEconomicLeadershipJoin :=
  ⟨[manufacturingJoin, domesticDemandJoin]⟩

theorem no_scalar_winner :
    canonical.scalarWinnerProduced = false ∧
    canonical.comprehensiveVictoryClaimClosed = false := by
  decide

end AgdaMirror.Economics.ChinaEconomicLeadershipCrossSourceJoin
