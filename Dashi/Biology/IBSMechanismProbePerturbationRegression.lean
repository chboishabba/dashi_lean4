import Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

namespace Dashi.Biology.IBSMechanismProbePerturbationRegression

open Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

theorem probeAtlasRegression : canonicalIBSMechanismProbeAtlas = canonicalIBSMechanismProbeAtlas := rfl

theorem responseNotMechanismIdentityRegression :
    ResponseIdentifiesUniqueMechanismPermission → False :=
  responseDoesNotIdentifyUniqueMechanism

theorem sameSymptomImprovementNotSamePathwayRegression :
    EqualSymptomResponseMeansSamePathwayPermission → False :=
  equalSymptomResponseDoesNotMeanSamePathway

theorem probeFrontierRegression : canonicalIBSProbeParetoFrontier = canonicalIBSProbeParetoFrontier := rfl

end Dashi.Biology.IBSMechanismProbePerturbationRegression
