import Integration.JInvariant369ConsolidatedNextStage

namespace AgdaMirror.JInvariant369ConsolidatedNextStage

open Integration.JInvariant369ConsolidatedNextStage
open Integration.StageTwelveGrothendieckRelation
open Integration.JInvariant369JointFibredObserver

structure ParityReceipt where
  agdaOwner : String
  leanOwner : String
  consolidatedStateMirrored : Bool
  levelNonFactorizationMirrored : Bool
  magnitudeNonFactorizationMirrored : Bool
  magnitudeRepairMirrored : Bool
  noFineMagnitudePreservingCycleLiftMirrored : Bool
  pathEqualityCreatesProofEquivalence : Bool
  deriving Repr

def canonicalParityReceipt : ParityReceipt where
  agdaOwner := "DASHI/Moonshine/JInvariant369ConsolidatedNextStageExact.agda"
  leanOwner := "Integration/JInvariant369ConsolidatedNextStage.lean"
  consolidatedStateMirrored := true
  levelNonFactorizationMirrored := true
  magnitudeNonFactorizationMirrored := true
  magnitudeRepairMirrored := true
  noFineMagnitudePreservingCycleLiftMirrored := true
  pathEqualityCreatesProofEquivalence := false

theorem no_fine_cycle_lift_parity :
    ¬ Nonempty MagnitudePreservingSignedCycleLift :=
  noMagnitudePreservingSignedCycleLift

end AgdaMirror.JInvariant369ConsolidatedNextStage
