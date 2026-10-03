namespace AgdaMirror.Economics.AIChinaTSMCGeoEconomicCalibration2026

inductive GeoEconomicCoordinate
  | manufacturingScale | exportNetworkCentrality | highTechIndustrialUpgrade
  | domesticDemandStrength | reserveCurrencyPower | aiCapitalLockIn
  | semiconductorFoundryConcentration | semiconductorGeographicDiversification
  deriving DecidableEq, Repr

structure GeoEconomicObservation where
  coordinate : GeoEconomicCoordinate
  reading : String
  sourceReceipt : String
  supportsGlobalLeadershipDimension : Bool := false
  provesOverallEconomicLeadership : Bool := false
  provesAIInfrastructureBubble : Bool := false
  provesTaiwanPoliticalStatus : Bool := false

def chinaManufacturingScale : GeoEconomicObservation :=
  ⟨.manufacturingScale,
   "China is the dominant global manufacturing hub by scale.",
   "IMF WP/25/27",
   true⟩

def chinaDomesticDemandResidual : GeoEconomicObservation :=
  ⟨.domesticDemandStrength,
   "Private domestic demand remains weak relative to export strength.",
   "IMF 2026 Article IV"⟩

def anthropicLockIn : GeoEconomicObservation :=
  ⟨.aiCapitalLockIn,
   "Long-horizon non-cancelable compute commitments create capital lock-in exposure.",
   "Reuters 2026-09-29"⟩

def tsmcDiversification : GeoEconomicObservation :=
  ⟨.semiconductorGeographicDiversification,
   "TSMC is considering further U.S. geographic diversification beyond Arizona.",
   "Reuters 2026-09-30"⟩

theorem observations_do_not_promote_global_verdict :
    ∀ o ∈ [chinaManufacturingScale, chinaDomesticDemandResidual, anthropicLockIn, tsmcDiversification],
      o.provesOverallEconomicLeadership = false ∧
      o.provesAIInfrastructureBubble = false ∧
      o.provesTaiwanPoliticalStatus = false := by
  intro o h
  simp at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Economics.AIChinaTSMCGeoEconomicCalibration2026
