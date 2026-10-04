namespace AgdaMirror.Governance.CubaSanctionsDomesticInstitutionMechanism

structure CubaPressureMechanism where
  sourceRef : String
  embargoCostPaid : Bool := true
  domesticInstitutionCostPaid : Bool := true
  interactionRatherThanSingleCause : Bool := true
  blameExternalisationSupported : Bool := true
  embargoSoleCause : Bool := false
  domesticInstitutionsSoleCause : Bool := false
  repressionNecessityPaid : Bool := false

def canonical : CubaPressureMechanism :=
  ⟨"Geloso and Martinez, Oxford Research Encyclopedia of Military History 2026"⟩

theorem bounded_multi_causal_mechanism :
    canonical.embargoCostPaid = true ∧
    canonical.domesticInstitutionCostPaid = true ∧
    canonical.embargoSoleCause = false ∧
    canonical.domesticInstitutionsSoleCause = false ∧
    canonical.repressionNecessityPaid = false := by
  decide

end AgdaMirror.Governance.CubaSanctionsDomesticInstitutionMechanism
