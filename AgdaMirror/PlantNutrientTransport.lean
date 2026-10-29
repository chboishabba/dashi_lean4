/-!
# Plant nutrient transport mirror

Agda remains the golden theorem authority.

This file mirrors the diagnostic boundary from
`DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact`.

The mirror preserves the same non-promotion rule.
A visible plant phenotype does not identify one chemical cause by itself.
-/

namespace AgdaMirror.PlantNutrientTransport

inductive IndicatorPhenotype where
  | interveinalChlorosis
  | paleOrLightVeins
  | reducedVigour
  | abnormalRootArchitecture
  deriving DecidableEq

inductive SoilStressHypothesis where
  | residualHerbicideCarryover
  | heavyMetalOrPaintResidue
  | pHAvailabilityShift
  | moistureLimitedNutrientTransport
  | waterloggingRootStress
  | salinityOrIonImbalance
  deriving DecidableEq

inductive PhenotypeCauseCompatibility :
    IndicatorPhenotype → SoilStressHypothesis → Prop where
  | chlorosisResidualHerbicideCandidate :
      PhenotypeCauseCompatibility
        .interveinalChlorosis
        .residualHerbicideCarryover
  | chlorosisPHCandidate :
      PhenotypeCauseCompatibility
        .interveinalChlorosis
        .pHAvailabilityShift
  | chlorosisMetalCandidate :
      PhenotypeCauseCompatibility
        .interveinalChlorosis
        .heavyMetalOrPaintResidue
  | vigourMoistureCandidate :
      PhenotypeCauseCompatibility
        .reducedVigour
        .moistureLimitedNutrientTransport
  | vigourWaterloggingCandidate :
      PhenotypeCauseCompatibility
        .reducedVigour
        .waterloggingRootStress

structure UniqueCausePromotion (phenotype : IndicatorPhenotype) where
  promotedCause : SoilStressHypothesis
  allCompatibleSame :
    ∀ {candidate},
      PhenotypeCauseCompatibility phenotype candidate →
      candidate = promotedCause

theorem interveinalChlorosisUniqueCausePromotionImpossible :
    UniqueCausePromotion .interveinalChlorosis → False := by
  intro promotion
  have hResidual :=
    promotion.allCompatibleSame
      PhenotypeCauseCompatibility.chlorosisResidualHerbicideCandidate
  have hPH :=
    promotion.allCompatibleSame
      PhenotypeCauseCompatibility.chlorosisPHCandidate
  have impossible :
      SoilStressHypothesis.residualHerbicideCarryover =
        SoilStressHypothesis.pHAvailabilityShift :=
    hResidual.trans hPH.symm
  cases impossible

structure SoilMoistureNutrientTransportBoundary where
  soilWaterParticipatesInDissolvedIonTransport : Bool
  massFlowAndDiffusionRemainDistinctTransportRoutes : Bool
  soilWaterContentCanChangeNutrientAvailability : Bool
  soilMoistureCanChangeResidualHerbicideAvailabilityOrBreakdown : Bool
  waterloggingCanConfoundPlantBioassay : Bool
  moistureAloneDeterminesPlantNutrientStatus : Bool
  phenotypeAloneIdentifiesUniqueChemicalCause : Bool
  spatialReplicationRaisesDiagnosticValue : Bool
  controlledComparisonIsRequiredForCausalPromotion : Bool

def canonicalSoilMoistureNutrientTransportBoundary :
    SoilMoistureNutrientTransportBoundary :=
  {
    soilWaterParticipatesInDissolvedIonTransport := true
    massFlowAndDiffusionRemainDistinctTransportRoutes := true
    soilWaterContentCanChangeNutrientAvailability := true
    soilMoistureCanChangeResidualHerbicideAvailabilityOrBreakdown := true
    waterloggingCanConfoundPlantBioassay := true
    moistureAloneDeterminesPlantNutrientStatus := false
    phenotypeAloneIdentifiesUniqueChemicalCause := false
    spatialReplicationRaisesDiagnosticValue := true
    controlledComparisonIsRequiredForCausalPromotion := true
  }

theorem plantPhenotypeDoesNotIdentifyUniqueChemicalCause :
    canonicalSoilMoistureNutrientTransportBoundary
        .phenotypeAloneIdentifiesUniqueChemicalCause = false := by
  rfl

theorem soilMoistureDoesNotDetermineNutrientStatusAlone :
    canonicalSoilMoistureNutrientTransportBoundary
        .moistureAloneDeterminesPlantNutrientStatus = false := by
  rfl

theorem controlledComparisonRequiredBeforeCausalPromotion :
    canonicalSoilMoistureNutrientTransportBoundary
        .controlledComparisonIsRequiredForCausalPromotion = true := by
  rfl

end AgdaMirror.PlantNutrientTransport
