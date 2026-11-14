import Dashi.Biology.IBSTransitionTriggerAtlasExact

namespace Dashi.Biology.IBSTransitionTriggerAtlasRegression

open Dashi.Biology.IBSTransitionTriggerAtlasExact

theorem triggerAtlasRegression :
    canonicalIBSTransitionTriggerAtlas = canonicalIBSTransitionTriggerAtlas := rfl

theorem naturalTriggerNotMechanismRegression :
    NaturalTriggerIdentifiesUniqueMechanismPermission → False :=
  naturalTriggerDoesNotIdentifyUniqueMechanism

theorem wearableNotStateRegression :
    WearableProxyIdentifiesLatentStatePermission → False :=
  wearableProxyDoesNotIdentifyLatentState

theorem postInfectiousNotAttractorRegression :
    PostInfectiousPersistenceValidatesAttractorPermission → False :=
  postInfectiousPersistenceDoesNotValidateAttractor

theorem triggerFrontierRegression :
    canonicalTransitionTriggerParetoFrontier = canonicalTransitionTriggerParetoFrontier := rfl

end Dashi.Biology.IBSTransitionTriggerAtlasRegression
