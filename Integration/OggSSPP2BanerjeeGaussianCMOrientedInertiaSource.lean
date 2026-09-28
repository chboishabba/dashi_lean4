import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2BanerjeeGaloisClassOrbitFive
import Integration.OggSSPP2OrientedInertiaTenStateRecognition
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2SupersingularUniversalDeformationSource

/-!
# Banerjee + Gaussian-CM oriented inertia same-source candidate

Corrected ten-state source candidate.

The five inertia labels are not an independent factor from the Banerjee Galois
sheet: Gal(F4/F2) acts on the seven G24 conjugacy classes by the same
class-pairing as inversion, so the quotient already has five sectors.

The independent binary marking retained here is instead the classical
orientation doublet of the Gaussian-CM quadratic order.

Thus the finite candidate is

  two Gaussian-CM orientations × five G24/Galois inertia orbits.

Both finite ingredients are classically sourced separately. Their product and
its identification with the paid DASHI ten-state target remain repository
construction.

The source-level wall is now exact:
* realize both Gaussian-CM orientations as normalized optimal embeddings on
  the endomorphism object of Banerjee's SAME supersingular curve;
* attach the unique bad-prime Gamma_0(4) finite-flat subgroup/subflag;
* supply raw Frobenius on that enriched marking.

No Galois sheet is reused as the orientation bit.
-/

namespace Integration.OggSSPP2BanerjeeGaussianCMOrientedInertiaSource

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace GaloisFive := Integration.OggSSPP2BanerjeeGaloisClassOrbitFive
namespace Ten := Integration.OggSSPP2OrientedInertiaTenStateRecognition
namespace Gamma := Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
namespace Bidi := Integration.OggSSPP2UniqueGamma0FourMarkingBidi
namespace Universal := Integration.OggSSPP2SupersingularUniversalDeformationSource
namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement
namespace F4 := Integration.OggSSPP2F4FrobeniusCandidateNoGo

abbrev State := Ten.State

/-- Orientation conjugation is its own marking involution, not Banerjee Gal. -/
def orientationConjugation : State → State
  | (.lower, inertia) => (.upper, inertia)
  | (.upper, inertia) => (.lower, inertia)

theorem orientation_conjugation_involutive
    (s : State) :
    orientationConjugation (orientationConjugation s) = s := by
  rcases s with ⟨orientation, inertia⟩
  cases orientation <;> rfl

def coarseOrbit (s : State) : F4.F4Orbit :=
  Target.stratumOf (Ten.toTarget s)

theorem orientation_conjugation_changes_centre :
    coarseOrbit (orientationConjugation (.lower, .identity)) ≠
      coarseOrbit (.lower, .identity) := by
  decide

theorem orientation_conjugation_preserves_noncentral_coarse
    (orientation : Ten.ClassicalQuadraticOrientation)
    (inertia : Ten.BinaryTetrahedralInversionOrbit)
    (h : inertia ≠ .identity) :
    coarseOrbit (orientationConjugation (orientation, inertia)) =
      coarseOrbit (orientation, inertia) := by
  cases orientation <;> cases inertia <;> simp_all [coarseOrbit, orientationConjugation,
    Ten.toTarget, Target.stratumOf]

/--
One proof-bearing arithmetic attachment over Banerjee's explicit universal
curve.  The CM-orientation and inertia realizability fields are deliberately
proof-bearing: the 2×5 count alone cannot inhabit them.
-/
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

  gaussianCMOrientationRealized :
    Ten.ClassicalQuadraticOrientation → Prop
  gaussianCMOrientationRealizedProof :
    ∀ orientation, gaussianCMOrientationRealized orientation

  g24GaloisOrbitRealized :
    Ten.BinaryTetrahedralInversionOrbit → Prop
  g24GaloisOrbitRealizedProof :
    ∀ orbit, g24GaloisOrbitRealized orbit

  rawFrobenius : State → State
  rawFrobeniusInvolutive :
    ∀ s, rawFrobenius (rawFrobenius s) = s

  rawFrobeniusPreservesCoarseOrbit :
    ∀ s, coarseOrbit (rawFrobenius s) = coarseOrbit s

  rawFrobeniusCommutesWithOrientationConjugation :
    ∀ s,
      rawFrobenius (orientationConjugation s) =
        orientationConjugation (rawFrobenius s)

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

/--
The universal deformation datum is concrete except for the external semantic
universal-property authority.
-/
structure SourceAuthority where
  oneParameterUniversalDeformation : Prop
  oneParameterUniversalDeformationProof : oneParameterUniversalDeformation

  universalProperty : Prop
  universalPropertyProof : universalProperty

  specialFibreSupersingular : Prop
  specialFibreSupersingularProof : specialFibreSupersingular

  banerjeeSourceIdentification : Prop
  banerjeeSourceIdentificationProof : banerjeeSourceIdentification

def sourceDatum
    (authority : SourceAuthority) :
    Universal.SupersingularUniversalDeformationDatum where
  ResidueField := Banerjee.F4
  WittBase := Banerjee.F4WittRing
  FormalParameter := Banerjee.F4DeformationBase
  DeformationBase := Banerjee.F4DeformationBase
  EllipticFamilyState := WeierstrassCurve Banerjee.F4DeformationBase
  characteristic := 2
  characteristicIsTwo := rfl
  oneFormalParameter := authority.oneParameterUniversalDeformation
  completeLocalWittPowerSeriesShape := True
  supersingularSpecialFibre := authority.specialFibreSupersingular
  universalPropertyImportedFromSource := authority.universalProperty
  sourceReference :=
    "Banerjee Def(C,F4)=Spf W(F4)[[a1]] + Deuring/Goren-Love CM orientation marking"

def marking
    (authority : SourceAuthority)
    (attachment : Attachment) :
    Universal.Gamma0FourUniversalDeformationMarking
      (sourceDatum authority) where
  MarkedState := State
  underlyingFamilyState := fun _ => Banerjee.universalCurve
  specializesToRawSubgroup := fun _ => .kerFrobeniusSquared
  specializationIsUniqueKerFrobeniusSquared := fun _ => rfl
  gamma0FourLevelStructurePresent :=
    fun _ => attachment.gammaZeroLevelFourSemantics
  gamma0FourLevelStructurePresentProof :=
    fun _ => attachment.gammaZeroLevelFourSemanticsProof
  deformationProvenanceRetained :=
    fun s =>
      attachment.gaussianCMOrientationRealized s.1 ∧
        attachment.g24GaloisOrbitRealized s.2
  deformationProvenanceRetainedProof :=
    fun s =>
      ⟨attachment.gaussianCMOrientationRealizedProof s.1,
       attachment.g24GaloisOrbitRealizedProof s.2⟩

def markingBidi
    (authority : SourceAuthority)
    (attachment : Attachment) :
    Bidi.Bidi
      (Universal.toUniqueSubgroupMarking (marking authority attachment)) where
  sourceCoarseOrbit := coarseOrbit
  toTarget := Ten.toTarget
  fromTarget := Ten.fromTarget
  sourceRoundTrip := Ten.state_roundtrip
  targetRoundTrip := Ten.target_roundtrip
  toTargetPreservesCoarseOrbit := fun _ => rfl
  fromTargetPreservesCoarseOrbit := by
    intro t
    change
      Target.stratumOf (Ten.toTarget (Ten.fromTarget t)) =
        Target.stratumOf t
    rw [Ten.target_roundtrip]
  everyMappedStateStillLiesOverUniqueRawSubgroup := fun _ => rfl

def tenStateRecognition
    (authority : SourceAuthority)
    (attachment : Attachment) :
    Universal.UniversalDeformationTenStateRecognition
      (sourceDatum authority)
      (marking authority attachment) where
  arithmeticBidi := markingBidi authority attachment

def rawFrobeniusSource
    (attachment : Attachment) :
    Gamma.Gamma0FourMarkedArithmeticSource where
  datum := finiteFlatDatum attachment
  MarkedState := State
  frobenius := attachment.rawFrobenius
  frobeniusInvolutive := attachment.rawFrobeniusInvolutive
  coarseF4Orbit := coarseOrbit
  coarseF4OrbitInvariant := attachment.rawFrobeniusPreservesCoarseOrbit

theorem state_count_is_ten :
    Fintype.card State = 10 :=
  Ten.state_cardinality

theorem five_inertia_labels_are_already_galois_quotient :
    Fintype.card Ten.BinaryTetrahedralInversionOrbit = 5 :=
  GaloisFive.five_orbit_cardinality

inductive Residual
  | missingBanerjeeSourceSemanticAuthority
  | missingGaussianCMOrientationRealizationOnBanerjeeCurve
  | missingFiniteFlatGamma0FourAttachment
  | missingRawFrobeniusCompatibility
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingBanerjeeSourceSemanticAuthority

structure Boundary where
  banerjeeF4UniversalCurveReused : Bool
  fiveInertiaLabelsAlreadyGaloisQuotient : Bool
  independentBinaryFactorIsCMOrientation : Bool
  banerjeeGaloisSheetUsedAsIndependentBinaryFactor : Bool
  proofBearingCMOrientationRealizationRequired : Bool
  proofBearingGamma0FourAttachmentRequired : Bool
  oneAttachmentConstructsTenStateBidi : Bool
  namedClassicalTenStateModuliObjectClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  banerjeeF4UniversalCurveReused := true
  fiveInertiaLabelsAlreadyGaloisQuotient := true
  independentBinaryFactorIsCMOrientation := true
  banerjeeGaloisSheetUsedAsIndependentBinaryFactor := false
  proofBearingCMOrientationRealizationRequired := true
  proofBearingGamma0FourAttachmentRequired := true
  oneAttachmentConstructsTenStateBidi := true
  namedClassicalTenStateModuliObjectClaimed := false

end Integration.OggSSPP2BanerjeeGaussianCMOrientedInertiaSource
