namespace AgdaMirror.Governance.IranWartimeConditionsRepressionRouting

structure WartimeRoutingReceipt where
  sourceRef : String
  externalThreatPresent : Bool := true
  preExistingRepressionRetained : Bool := true
  wartimeConditionsUsedAsCover : Bool := true
  intensifiedRepressionAttributed : Bool := true
  marginalEffectSizeIdentified : Bool := false
  externalThreatNecessaryForRepression : Bool := false
  allObservedRepressionCausedByWar : Bool := false

def canonical : WartimeRoutingReceipt :=
  ⟨"Amnesty International 2026 research/campaign material"⟩

theorem qualitative_not_quantitative :
    canonical.wartimeConditionsUsedAsCover = true ∧
    canonical.intensifiedRepressionAttributed = true ∧
    canonical.marginalEffectSizeIdentified = false ∧
    canonical.externalThreatNecessaryForRepression = false ∧
    canonical.allObservedRepressionCausedByWar = false := by
  decide

end AgdaMirror.Governance.IranWartimeConditionsRepressionRouting
