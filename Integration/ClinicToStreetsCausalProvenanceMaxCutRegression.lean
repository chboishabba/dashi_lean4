import Integration.ClinicToStreetsCausalProvenanceMaxCut

namespace Integration.ClinicToStreetsCausalProvenanceMaxCutRegression

open Integration.ClinicToStreetsCausalProvenanceMaxCut

example : edgeVisible .atomised .structuralToFamily = false := rfl
example : edgeVisible .atomised .familyToPsychic = true := rfl
example : psychicUpstreamSalience .full = 9 := rfl
example : psychicUpstreamSalience .atomised = 3 := rfl
example : fullResponsibility.individualShare = 1 := rfl
example : atomisedResponsibility.individualShare = 7 := rfl
example : actionConeCardinality .full = 3 := rfl
example : actionConeCardinality .atomised = 1 := rfl
example : actionConeCardinality .reskilled = 3 := rfl
example : ¬ ModelWeightImpliesEmpiricalMagnitude := model_weight_does_not_establish_empirical_magnitude
example : ¬ ResponsibilityCoordinateImpliesMoralFault := responsibility_coordinate_does_not_establish_moral_fault
example : ¬ ActionConeContractionImpliesIntent := action_cone_contraction_does_not_establish_intent

end Integration.ClinicToStreetsCausalProvenanceMaxCutRegression
