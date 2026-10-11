import Integration.ClinicToStreetsCausalProvenance

namespace Integration.ClinicToStreetsCausalProvenanceRegression

open Integration.ClinicToStreetsCausalProvenance

example : fullContext.structuralVisible = true := rfl
example : atomisedContext.structuralVisible = false := rfl
example : atomisedContext.intimateVisible = true := rfl
example : atomisedContext.intrapsychicVisible = true := rfl

example : CausalProvenanceErasure fullContext atomisedContext :=
  canonicalAtomisingErasure

example : ¬ PsychicEffectImpliesEstablishedIntent :=
  psychicEffectDoesNotEstablishIntent

example : ¬ EffectSignatureImpliesTherapyEssence :=
  effectSignatureDoesNotEstablishTherapyEssence

example : ¬ ConeDeformationImpliesInfluence :=
  coneDeformationDoesNotEstablishInfluence

example : ¬ ProvenanceImpliesTruth :=
  provenanceDoesNotEstablishTruth

example : canonicalBoundary.psychicEffectImpliesIntent = false := rfl
example : canonicalBoundary.counterinsurgentEffectImpliesTherapyEssence = false := rfl
example : canonicalBoundary.reskillingRestoresProvenanceCoordinate = true := rfl

end Integration.ClinicToStreetsCausalProvenanceRegression
