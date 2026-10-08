import Dashi.Biology.IBSLatentStateTransitionExact

namespace Dashi.Biology.IBSLatentStateTransitionRegression

open Dashi.Biology.IBSLatentStateTransitionExact

theorem stateAtlasRegression :
    canonicalTemporalStateEvidenceAtlas = canonicalTemporalStateEvidenceAtlas := rfl

theorem transitionFrontierRegression :
    canonicalIBSTransitionParetoFrontier = canonicalIBSTransitionParetoFrontier := rfl

theorem sameSymptomsNotSameStateRegression :
    SameSymptomsIdentifySameLatentStatePermission → False :=
  sameSymptomsDoNotIdentifySameLatentState

theorem lagAssociationNotDirectionRegression :
    LagAssociationIdentifiesCausalDirectionPermission → False :=
  lagAssociationDoesNotIdentifyCausalDirection

theorem trajectoryClusterNotAttractorRegression :
    TrajectoryClusterIsValidatedAttractorPermission → False :=
  trajectoryClusterDoesNotValidateAttractor

theorem historyBoundaryRegression :
    canonicalIBSTemporalPathBoundary = canonicalIBSTemporalPathBoundary := rfl

end Dashi.Biology.IBSLatentStateTransitionRegression
