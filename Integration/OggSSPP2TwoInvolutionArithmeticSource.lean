import Mathlib
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo

/-!
# p=2 two-involution arithmetic source

The live p=2 source has two mathematically distinct order-two transports:

* raw Frobenius on the F4/F2 arithmetic coordinate;
* Gal(F4/F2) transport on Banerjee's universal-deformation torsor.

The old Gamma0FourMarkedArithmeticSource has one involution named frobenius and
requires its coarse F4-orbit label to be invariant.  That remains a valid
interface for the RAW Frobenius action.

It must not be reused for Banerjee Galois transport: the latter swaps the two
duplicated centre states while preserving all noncentral coarse strata.

This owner keeps the actions separate and records their compatibility rather
than identifying them.
-/

namespace Integration.OggSSPP2TwoInvolutionArithmeticSource

namespace Gamma :=
  Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
namespace Banerjee :=
  Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace F4 :=
  Integration.OggSSPP2F4FrobeniusCandidateNoGo

structure TwoInvolutionSource where
  datum : Gamma.Gamma0FourFiniteFlatDatum

  MarkedState : Type

  rawFrobenius : MarkedState → MarkedState
  rawFrobeniusInvolutive :
    ∀ s, rawFrobenius (rawFrobenius s) = s

  galoisTransport : MarkedState → MarkedState
  galoisTransportInvolutive :
    ∀ s, galoisTransport (galoisTransport s) = s

  coarseF4Orbit : MarkedState → F4.F4Orbit

  rawFrobeniusPreservesCoarseOrbit :
    ∀ s, coarseF4Orbit (rawFrobenius s) = coarseF4Orbit s

  actionsCommute :
    ∀ s,
      rawFrobenius (galoisTransport s) =
        galoisTransport (rawFrobenius s)

  galoisTransportMayMoveCoarseOrbitAtCentre : Prop
  galoisTransportMayMoveCoarseOrbitAtCentreProof :
    galoisTransportMayMoveCoarseOrbitAtCentre

/-- Forget the extra Galois action and recover the original raw-Frobenius source. -/
def toRawFrobeniusSource
    (source : TwoInvolutionSource) :
    Gamma.Gamma0FourMarkedArithmeticSource where
  datum := source.datum
  MarkedState := source.MarkedState
  frobenius := source.rawFrobenius
  frobeniusInvolutive := source.rawFrobeniusInvolutive
  coarseF4Orbit := source.coarseF4Orbit
  coarseF4OrbitInvariant := source.rawFrobeniusPreservesCoarseOrbit

/--
The Banerjee finite candidate demonstrates why the second action cannot be
folded into the first invariant one.
-/
theorem banerjee_galois_is_not_a_globally_coarse_invariant_raw_action :
    ¬ Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo.GloballyInvariantCoarseOrbit :=
  Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo.natural_galois_cannot_preserve_current_coarse_orbit

structure Boundary where
  rawFrobeniusActionSeparated : Bool
  banerjeeGaloisActionSeparated : Bool
  rawFrobeniusCoarseInvarianceRetained : Bool
  galoisCoarseInvarianceRequiredGlobally : Bool
  actionCommutationRequired : Bool
  oldSingleActionSourceRecoverable : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rawFrobeniusActionSeparated := true
  banerjeeGaloisActionSeparated := true
  rawFrobeniusCoarseInvarianceRetained := true
  galoisCoarseInvarianceRequiredGlobally := false
  actionCommutationRequired := true
  oldSingleActionSourceRecoverable := true

end Integration.OggSSPP2TwoInvolutionArithmeticSource
