/-!
# Golden Agda Feynman / TSFV non-promotion mirror

Golden owners:

* `DASHI/Physics/Foundations/TSFVFeynmanDerivationObligationsExact.agda`
* `DASHI/Physics/Closure/FeynmanKelvinTrajectoryCrossPollinationExact.agda`
* `DASHI/Unified/Physics.agda`

This file mirrors status boundaries only.

It does not implement a path integral.
It does not derive a propagator.
It does not promote the cited experiments into validation of TSFV.
-/

namespace AgdaMirror.Physics.FeynmanNonPromotion

/-- Golden status surface for the current Feynman/TSFV derivation lane. -/
structure DerivationBoundary where
  architectureCompatibleWithFeynman : Bool
  structuralActionCandidateConstructed : Bool
  nonseparableTransitionActionDerived : Bool
  justifiedHistoryTransitionRealizationSupplied : Bool
  actionToPhaseCalibrationSupplied : Bool
  tsfvCurrentlyDerivesFeynmanPropagator : Bool
  tsfvCurrentlyHasUniqueEmpiricalPrediction : Bool

/-- Faithful mirror of the golden Agda boundary values. -/
def canonicalDerivationBoundary : DerivationBoundary where
  architectureCompatibleWithFeynman := true
  structuralActionCandidateConstructed := true
  nonseparableTransitionActionDerived := true
  justifiedHistoryTransitionRealizationSupplied := false
  actionToPhaseCalibrationSupplied := false
  tsfvCurrentlyDerivesFeynmanPropagator := false
  tsfvCurrentlyHasUniqueEmpiricalPrediction := false

@[simp] theorem architectureCompatible :
    canonicalDerivationBoundary.architectureCompatibleWithFeynman = true := rfl

@[simp] theorem historyRealizationStillOpen :
    canonicalDerivationBoundary.justifiedHistoryTransitionRealizationSupplied = false := rfl

@[simp] theorem actionPhaseCalibrationStillOpen :
    canonicalDerivationBoundary.actionToPhaseCalibrationSupplied = false := rfl

@[simp] theorem tsfvDoesNotDeriveFeynmanPropagator :
    canonicalDerivationBoundary.tsfvCurrentlyDerivesFeynmanPropagator = false := rfl

/-- Golden experimental non-promotion surface. -/
structure ExperimentBoundary where
  finitePathDecompositionSupported : Bool
  coherentCompositionSupported : Bool
  experimentValidatesTSFV : Bool
  stationaryImpliesMinimum : Bool
  stationaryImpliesMetricShortest : Bool

/-- The finite path-amplitude layer is supported.
The stronger TSFV and shortest-path promotions remain false. -/
def canonicalExperimentBoundary : ExperimentBoundary where
  finitePathDecompositionSupported := true
  coherentCompositionSupported := true
  experimentValidatesTSFV := false
  stationaryImpliesMinimum := false
  stationaryImpliesMetricShortest := false

@[simp] theorem experimentDoesNotValidateTSFV :
    canonicalExperimentBoundary.experimentValidatesTSFV = false := rfl

@[simp] theorem stationaryDoesNotImplyMinimum :
    canonicalExperimentBoundary.stationaryImpliesMinimum = false := rfl

@[simp] theorem stationaryDoesNotImplyMetricShortest :
    canonicalExperimentBoundary.stationaryImpliesMetricShortest = false := rfl

end AgdaMirror.Physics.FeynmanNonPromotion
