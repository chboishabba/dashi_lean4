import Mathlib
import Integration.CondensedMatterSqrt3R30ReciprocalFolding

/-!
# Generic ARPES folding / nesting witness gate

A source-reported folded band is not silently promoted to a repository-native
spectral function.  The exact witness type is formalised, while the Fe5GeTe2
instance remains open until raw data or an equivalent theorem-producing
spectral representation is supplied.
-/

namespace Integration.CondensedMatterARPESWitnessGate

structure SpectralObserver (Momentum Energy Intensity : Type) where
  intensity : Momentum → Energy → Intensity

structure VisibilityClassifier (Intensity : Type) where
  visible : Intensity → Bool

structure FoldedSpectralPairWitness
    {Momentum Energy Intensity : Type}
    (spectral : SpectralObserver Momentum Energy Intensity)
    (classifier : VisibilityClassifier Intensity)
    (foldClass : Momentum → ZMod 3) where
  originalMomentum : Momentum
  foldedMomentum : Momentum
  selectedEnergy : Energy
  distinctMomentum : originalMomentum ≠ foldedMomentum
  sameFoldClass : foldClass originalMomentum = foldClass foldedMomentum
  originalVisible :
    classifier.visible (spectral.intensity originalMomentum selectedEnergy) = true
  foldedVisible :
    classifier.visible (spectral.intensity foldedMomentum selectedEnergy) = true

structure FlatBandNestingWitness
    {Momentum Energy Intensity : Type}
    (spectral : SpectralObserver Momentum Energy Intensity)
    (classifier : VisibilityClassifier Intensity) where
  firstMomentum : Momentum
  secondMomentum : Momentum
  fermiEnergy : Energy
  distinctMomentum : firstMomentum ≠ secondMomentum
  firstVisible :
    classifier.visible (spectral.intensity firstMomentum fermiEnergy) = true
  secondVisible :
    classifier.visible (spectral.intensity secondMomentum fermiEnergy) = true

def literalSqrt3R30FoldClass :
    Integration.CondensedMatterSqrt3R30.Torus3x3 → ZMod 3 :=
  Integration.CondensedMatterSqrt3R30.foldClass

structure Fe5GeTe2Status where
  orderedPhaseLabel : String
  originalBrillouinZoneShown : Bool
  reconstructedSqrt3BrillouinZoneShown : Bool
  gammaToKReplicaBandsReported : Bool
  lowTemperatureK : Nat
  highTemperatureK : Nat
  spectralWeightIntegrationLowerBindingMeV : Nat
  spectralWeightIntegrationUpperBindingMeV : Nat
  primaryPaperReportsBandFolding : Bool
  primaryPaperReportsFlatBandNestingVector : Bool
  primaryPaperReportsLindhardSupport : Bool
  exactSqrt3R30FoldGeometryAvailable : Bool
  rawSpectralArrayAvailableInRepository : Bool
  foldedSpectralPairWitnessConstructed : Bool
  flatBandNestingWitnessConstructed : Bool
  lindhardFunctionRecomputedInKernel : Bool
  deriving Repr

def canonicalFe5GeTe2Status : Fe5GeTe2Status where
  orderedPhaseLabel := "UUU phase"
  originalBrillouinZoneShown := true
  reconstructedSqrt3BrillouinZoneShown := true
  gammaToKReplicaBandsReported := true
  lowTemperatureK := 8
  highTemperatureK := 180
  spectralWeightIntegrationLowerBindingMeV := 50
  spectralWeightIntegrationUpperBindingMeV := 0
  primaryPaperReportsBandFolding := true
  primaryPaperReportsFlatBandNestingVector := true
  primaryPaperReportsLindhardSupport := true
  exactSqrt3R30FoldGeometryAvailable := true
  rawSpectralArrayAvailableInRepository := false
  foldedSpectralPairWitnessConstructed := false
  flatBandNestingWitnessConstructed := false
  lindhardFunctionRecomputedInKernel := false

structure PromotionBoundary where
  sourceReportAutomaticallyConstructsSpectralFunction : Bool
  symmetryLabelAutomaticallyConstructsIntensityArray : Bool
  exactGeometryAutomaticallyProvesObservedIntensity : Bool
  rawDataOrEquivalentWitnessStillRequired : Bool
  deriving Repr

def canonicalBoundary : PromotionBoundary where
  sourceReportAutomaticallyConstructsSpectralFunction := false
  symmetryLabelAutomaticallyConstructsIntensityArray := false
  exactGeometryAutomaticallyProvesObservedIntensity := false
  rawDataOrEquivalentWitnessStillRequired := true

end Integration.CondensedMatterARPESWitnessGate
