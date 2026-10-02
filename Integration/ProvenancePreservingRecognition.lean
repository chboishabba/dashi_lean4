import Integration.ActionOrbitRecognition

/-!
# Provenance-preserving recognition

Lean mirror of the Agda provenance-recognition refinement.  Action/orbit
recognition and provenance preservation are separate obligations: equal
observations or orbit labels do not silently identify source history.
-/

namespace Integration.ProvenancePreservingRecognition

open Integration.ActionOrbitRecognition

structure ProvenancePreservingActionRecognition
    {SS SG TS TG SP TP : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    (sourceProvenance : SS → SP)
    (targetProvenance : TS → TP) where
  actionRecognition : ActionRecognitionFunctor source target
  mapProvenance : SP → TP
  provenanceCommutes :
    ∀ s, targetProvenance (actionRecognition.mapState s) =
      mapProvenance (sourceProvenance s)
  reflectsMappedProvenance :
    ∀ {a b},
      targetProvenance (actionRecognition.mapState a) =
        targetProvenance (actionRecognition.mapState b) →
      sourceProvenance a = sourceProvenance b

structure ProvenancePreservingOrbitRecognition
    {SS SG TS TG SP TP : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {sourceProvenance : SS → SP}
    {targetProvenance : TS → TP}
    (P : ProvenancePreservingActionRecognition
      sourceProvenance targetProvenance)
    (sourceOrbits : OrbitPresentation source)
    (targetOrbits : OrbitPresentation target) where
  fullRecognition :
    FullRecognition P.actionRecognition sourceOrbits targetOrbits

inductive ProvenancePromotionError
  | sharedObservationCreatesSharedProvenance
  | orbitEqualityCreatesSharedProvenance
  | equivarianceTransfersAuthority
  deriving DecidableEq, Repr

structure ProvenanceBoundary where
  actionEquivarianceStillRequired : Bool
  orbitRecognitionStillRequired : Bool
  provenanceCommutationRequired : Bool
  provenanceReflectionRequired : Bool
  sharedObservationFusesProvenance : Bool
  orbitEqualityFusesProvenance : Bool
  equivarianceTransfersAuthority : Bool
  deriving Repr

def canonicalBoundary : ProvenanceBoundary where
  actionEquivarianceStillRequired := true
  orbitRecognitionStillRequired := true
  provenanceCommutationRequired := true
  provenanceReflectionRequired := true
  sharedObservationFusesProvenance := false
  orbitEqualityFusesProvenance := false
  equivarianceTransfersAuthority := false

end Integration.ProvenancePreservingRecognition
