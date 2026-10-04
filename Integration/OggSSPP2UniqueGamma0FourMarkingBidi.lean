import Mathlib
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2F4AntipodalStratifiedRefinement

/-!
# Unique Gamma_0(4) marking <-> paid p=2 target: bidi contract

Any future arithmetic marking over the unique raw subgroup ker(F^2) must be
equivalent, not merely mapped, to the paid ten-state target presentation.

The contract requires:
* state maps both directions;
* exact round trips;
* preservation of the three F4/F2 coarse strata both directions;
* every target-reconstructed source state still lies over ker(F^2).

No arithmetic inhabitant is constructed here.
-/

namespace Integration.OggSSPP2UniqueGamma0FourMarkingBidi

open Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
open Integration.OggSSPP2F4AntipodalStratifiedRefinement
open Integration.OggSSPP2F4FrobeniusCandidateNoGo

structure Bidi
    (source : MarkingOverUniqueGamma0FourSubgroup) where
  sourceCoarseOrbit :
    source.MarkedState → F4Orbit

  toTarget :
    source.MarkedState → StratifiedTargetState

  fromTarget :
    StratifiedTargetState → source.MarkedState

  sourceRoundTrip :
    ∀ s, fromTarget (toTarget s) = s

  targetRoundTrip :
    ∀ t, toTarget (fromTarget t) = t

  toTargetPreservesCoarseOrbit :
    ∀ s, stratumOf (toTarget s) = sourceCoarseOrbit s

  fromTargetPreservesCoarseOrbit :
    ∀ t, sourceCoarseOrbit (fromTarget t) = stratumOf t

  everyMappedStateStillLiesOverUniqueRawSubgroup :
    ∀ t, source.rawSubgroup (fromTarget t) =
      .kerFrobeniusSquared

theorem toTarget_injective
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    Function.Injective b.toTarget := by
  intro x y h
  calc
    x = b.fromTarget (b.toTarget x) := (b.sourceRoundTrip x).symm
    _ = b.fromTarget (b.toTarget y) := by rw [h]
    _ = y := b.sourceRoundTrip y

theorem fromTarget_injective
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    Function.Injective b.fromTarget := by
  intro x y h
  calc
    x = b.toTarget (b.fromTarget x) := (b.targetRoundTrip x).symm
    _ = b.toTarget (b.fromTarget y) := by rw [h]
    _ = y := b.targetRoundTrip y

structure Boundary where
  twoSidedStateRecoveryRequired : Bool
  coarseF4StratumPreservationRequiredBothWays : Bool
  uniqueRawSubgroupProvenanceRequired : Bool
  sourceTargetCardinalityAloneSufficient : Bool
  arithmeticBidiConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  twoSidedStateRecoveryRequired := true
  coarseF4StratumPreservationRequiredBothWays := true
  uniqueRawSubgroupProvenanceRequired := true
  sourceTargetCardinalityAloneSufficient := false
  arithmeticBidiConstructed := false

end Integration.OggSSPP2UniqueGamma0FourMarkingBidi
