import Dashi.Biology.IBSCausalMaintenanceRegimeExact

namespace Dashi.Biology.IBSCausalMaintenanceRegimeRegression

open Dashi.Biology.IBSCausalMaintenanceRegimeExact

theorem regimeAtlasRegression :
    canonicalCandidateMaintenanceRegimeAtlas = canonicalCandidateMaintenanceRegimeAtlas := rfl

theorem observationPanelRegression :
    canonicalRegimeDiscriminationPanel = canonicalRegimeDiscriminationPanel := rfl

theorem paretoFrontierRegression :
    canonicalCausalMaintenanceParetoFrontier = canonicalCausalMaintenanceParetoFrontier := rfl

theorem symptomPatternDoesNotIdentifyRegimeRegression :
    SymptomPatternIdentifiesMaintenanceRegimePermission → False :=
  symptomPatternDoesNotIdentifyMaintenanceRegime

theorem singleInterventionDoesNotIdentifyUniqueRegimeRegression :
    SingleInterventionResponseIdentifiesUniqueRegimePermission → False :=
  singleInterventionResponseDoesNotIdentifyUniqueRegime

theorem biomarkerPanelDoesNotEqualCausalRegimeRegression :
    BiomarkerPanelEqualsCausalRegimePermission → False :=
  biomarkerPanelDoesNotEqualCausalRegime

end Dashi.Biology.IBSCausalMaintenanceRegimeRegression
