import Dashi.Biology.IBSSystemsIdentificationParetoExact

namespace Dashi.Biology.IBSSystemsIdentificationParetoRegression

open Dashi.Biology.IBSSystemsIdentificationParetoExact

theorem measurementAtlasRegression :
    canonicalIBSMeasurementAtlas = canonicalIBSMeasurementAtlas := rfl

theorem systemsFrontierRegression :
    canonicalIBSSystemsParetoFrontier = canonicalIBSSystemsParetoFrontier := rfl

theorem singleMarkerDoesNotIdentifyStateRegression :
    SingleMarkerIdentifiesWholeSystemStatePermission → False :=
  singleMarkerDoesNotIdentifyWholeSystemState

theorem symptomSubtypeDoesNotIdentifyMechanismRegression :
    BowelHabitSubtypeIdentifiesMechanismPermission → False :=
  bowelHabitSubtypeDoesNotIdentifyMechanism

theorem crossSectionDoesNotIdentifyFeedbackRegression :
    CrossSectionIdentifiesFeedbackDirectionPermission → False :=
  crossSectionDoesNotIdentifyFeedbackDirection

theorem interventionPanelRegression :
    canonicalMinimumDiscriminatingPanel = canonicalMinimumDiscriminatingPanel := rfl

end Dashi.Biology.IBSSystemsIdentificationParetoRegression
