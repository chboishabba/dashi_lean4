import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2TwoInvolutionArithmeticSource

/-!
# Banerjee universal curve + proof-bearing Gamma_0(4) attachment

The selected elliptic object is fixed definitionally to Banerjee's explicit
universal curve over W(F4)[[a1]].

A lawful attachment must supply:
* one finite-flat cyclic rank-4 subgroup;
* its rank-2 subflag;
* proof-bearing bad-prime Gamma_0(4) semantics;
* raw Frobenius transport on the reconstructed ten sector states;
* raw-Frobenius coarse-F4 invariance;
* commutation of raw Frobenius with the source-native Galois toggle.

The source-native Galois action itself is not reused as raw Frobenius; the
centre-local no-go proves that would violate coarse-orbit invariance.
-/

namespace Integration.OggSSPP2BanerjeeGamma0FourAttachment

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace GaloisNoGo := Integration.OggSSPP2BanerjeeGaloisVsF4OrbitNoGo
namespace Gamma := Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
namespace Two := Integration.OggSSPP2TwoInvolutionArithmeticSource
namespace F4 := Integration.OggSSPP2F4FrobeniusCandidateNoGo
namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement

structure Attachment where
  OrderFourSubgroup : Type
  OrderTwoSubgroup : Type

  selectedOrderFourSubgroup : OrderFourSubgroup
  selectedOrderTwoSubgroup : OrderTwoSubgroup

  orderTwoSubflagOfOrderFour : Prop
  orderTwoSubflagOfOrderFourProof : orderTwoSubflagOfOrderFour

  finiteFlatAtCharacteristicTwo : Prop
  finiteFlatAtCharacteristicTwoProof : finiteFlatAtCharacteristicTwo

  gammaZeroLevelFourSemantics : Prop
  gammaZeroLevelFourSemanticsProof : gammaZeroLevelFourSemantics

  rawFrobenius :
    Banerjee.GaloisInertiaState → Banerjee.GaloisInertiaState

  rawFrobeniusInvolutive :
    ∀ s, rawFrobenius (rawFrobenius s) = s

  rawFrobeniusPreservesCoarseOrbit :
    ∀ s,
      Target.stratumOf (Banerjee.toTarget (rawFrobenius s)) =
        Target.stratumOf (Banerjee.toTarget s)

  rawFrobeniusCommutesWithGalois :
    ∀ s,
      rawFrobenius (GaloisNoGo.galoisInvolution s) =
        GaloisNoGo.galoisInvolution (rawFrobenius s)

  sourceReference : String

def finiteFlatDatum
    (attachment : Attachment) :
    Gamma.Gamma0FourFiniteFlatDatum where
  EllipticObject := WeierstrassCurve Banerjee.F4DeformationBase
  OrderFourSubgroup := attachment.OrderFourSubgroup
  OrderTwoSubgroup := attachment.OrderTwoSubgroup

  selectedEllipticObject := Banerjee.universalCurve
  selectedOrderFourSubgroup := attachment.selectedOrderFourSubgroup
  selectedOrderTwoSubgroup := attachment.selectedOrderTwoSubgroup

  orderFourRank := 4
  orderFourRankIsFour := rfl
  orderTwoRank := 2
  orderTwoRankIsTwo := rfl

  orderTwoSubflagOfOrderFour := attachment.orderTwoSubflagOfOrderFour
  orderTwoSubflagOfOrderFourProof :=
    attachment.orderTwoSubflagOfOrderFourProof

  finiteFlatAtCharacteristicTwo := attachment.finiteFlatAtCharacteristicTwo
  finiteFlatAtCharacteristicTwoProof :=
    attachment.finiteFlatAtCharacteristicTwoProof

  gammaZeroLevelFourSemantics := attachment.gammaZeroLevelFourSemantics
  gammaZeroLevelFourSemanticsProof :=
    attachment.gammaZeroLevelFourSemanticsProof

  sourceReference := attachment.sourceReference

def coarseOrbit
    (s : Banerjee.GaloisInertiaState) : F4.F4Orbit :=
  Target.stratumOf (Banerjee.toTarget s)

def twoInvolutionSource
    (attachment : Attachment) :
    Two.TwoInvolutionSource where
  datum := finiteFlatDatum attachment
  MarkedState := Banerjee.GaloisInertiaState

  rawFrobenius := attachment.rawFrobenius
  rawFrobeniusInvolutive := attachment.rawFrobeniusInvolutive

  galoisTransport := GaloisNoGo.galoisInvolution
  galoisTransportInvolutive := GaloisNoGo.galois_involution_involutive

  coarseF4Orbit := coarseOrbit
  rawFrobeniusPreservesCoarseOrbit :=
    attachment.rawFrobeniusPreservesCoarseOrbit

  actionsCommute := attachment.rawFrobeniusCommutesWithGalois

  galoisTransportMayMoveCoarseOrbitAtCentre :=
    ∃ s,
      coarseOrbit (GaloisNoGo.galoisInvolution s) ≠ coarseOrbit s
  galoisTransportMayMoveCoarseOrbitAtCentreProof :=
    ⟨(.identity, .identity), GaloisNoGo.centre_orbit_changes_under_galois⟩

def rawFrobeniusSource
    (attachment : Attachment) :
    Gamma.Gamma0FourMarkedArithmeticSource :=
  Two.toRawFrobeniusSource (twoInvolutionSource attachment)

theorem selected_elliptic_object_is_universal_curve
    (attachment : Attachment) :
    (finiteFlatDatum attachment).selectedEllipticObject =
      Banerjee.universalCurve :=
  rfl

theorem natural_galois_is_not_raw_frobenius_candidate :
    ¬ GaloisNoGo.GloballyInvariantCoarseOrbit :=
  GaloisNoGo.natural_galois_cannot_preserve_current_coarse_orbit

inductive Residual
  | missingFiniteFlatOrderFourSubgroup
  | missingOrderTwoSubflag
  | missingRawFrobeniusOnAttachedLevelStructure
  | missingRawGaloisCommutation
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingFiniteFlatOrderFourSubgroup

structure Boundary where
  selectedCurveFixedToBanerjeeUniversalCurve : Bool
  proofBearingFiniteFlatDatumConstructedFromAttachment : Bool
  naturalGaloisTransportFixed : Bool
  naturalGaloisRejectedAsRawFrobenius : Bool
  rawFrobeniusRequiredSeparately : Bool
  rawGaloisCommutationRequired : Bool
  twoInvolutionSourceConstructedAutomatically : Bool
  attachmentInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  selectedCurveFixedToBanerjeeUniversalCurve := true
  proofBearingFiniteFlatDatumConstructedFromAttachment := true
  naturalGaloisTransportFixed := true
  naturalGaloisRejectedAsRawFrobenius := true
  rawFrobeniusRequiredSeparately := true
  rawGaloisCommutationRequired := true
  twoInvolutionSourceConstructedAutomatically := true
  attachmentInhabitedHere := false

end Integration.OggSSPP2BanerjeeGamma0FourAttachment
