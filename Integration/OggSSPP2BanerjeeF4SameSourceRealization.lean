import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi

/-!
# Banerjee F4 same-source realization capstone

Preferred p=2 source path after the Banerjee correction.

The universal deformation is based on W(F4)[[a1]], not on the earlier
F2-specialized Witt carrier.  The source theorem places G24 and
Gal(F4/F2) on the same deformation torsor.

The only state-level realization obligation in this module is to attach the
repository's reconstructed
  Gal(F4/F2) × (G24 conjugacy classes / inversion)
sector labels to genuine marked states of that universal deformation.

Once supplied, the existing Gamma_0(4)-over-unique-ker(F²) marking and ten-state
bidi are generated automatically.
-/

namespace Integration.OggSSPP2BanerjeeF4SameSourceRealization

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Universal := Integration.OggSSPP2SupersingularUniversalDeformationSource
namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Bidi := Integration.OggSSPP2UniqueGamma0FourMarkingBidi
namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement

structure SourceAuthority where
  specialFibreSupersingular : Prop
  specialFibreSupersingularProof : specialFibreSupersingular

  oneParameterUniversalDeformation : Prop
  oneParameterUniversalDeformationProof : oneParameterUniversalDeformation

  completeLocalWittF4PowerSeriesShape : Prop
  completeLocalWittF4PowerSeriesShapeProof :
    completeLocalWittF4PowerSeriesShape

  universalProperty : Prop
  universalPropertyProof : universalProperty

  sourceReceiptMatchesBanerjee : Prop
  sourceReceiptMatchesBanerjeeProof : sourceReceiptMatchesBanerjee

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
  completeLocalWittPowerSeriesShape :=
    authority.completeLocalWittF4PowerSeriesShape
  supersingularSpecialFibre := authority.specialFibreSupersingular
  universalPropertyImportedFromSource := authority.universalProperty
  sourceReference :=
    "Romie Banerjee, A modular description of ER(2), NYJM 20 (2014), Section 3.1"

theorem source_residue_field_is_F4
    (authority : SourceAuthority) :
    (sourceDatum authority).ResidueField = Banerjee.F4 := rfl

theorem source_witt_base_is_WF4
    (authority : SourceAuthority) :
    (sourceDatum authority).WittBase = Banerjee.F4WittRing := rfl

theorem source_deformation_base_is_WF4_power_series
    (authority : SourceAuthority) :
    (sourceDatum authority).DeformationBase =
      Banerjee.F4DeformationBase := rfl

structure SectorRealization
    (authority : SourceAuthority) where
  gamma0FourLevelStructurePresent :
    Banerjee.GaloisInertiaState → Prop

  gamma0FourLevelStructurePresentProof :
    ∀ state, gamma0FourLevelStructurePresent state

  deformationProvenanceRetained :
    Banerjee.GaloisInertiaState → Prop

  deformationProvenanceRetainedProof :
    ∀ state, deformationProvenanceRetained state

def marking
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Universal.Gamma0FourUniversalDeformationMarking
      (sourceDatum authority) where
  MarkedState := Banerjee.GaloisInertiaState
  underlyingFamilyState := fun _ => Banerjee.universalCurve
  specializesToRawSubgroup := fun _ => .kerFrobeniusSquared
  specializationIsUniqueKerFrobeniusSquared := fun _ => rfl
  gamma0FourLevelStructurePresent :=
    realization.gamma0FourLevelStructurePresent
  gamma0FourLevelStructurePresentProof :=
    realization.gamma0FourLevelStructurePresentProof
  deformationProvenanceRetained :=
    realization.deformationProvenanceRetained
  deformationProvenanceRetainedProof :=
    realization.deformationProvenanceRetainedProof

def sourceCoarseOrbit :
    Banerjee.GaloisInertiaState →
      Integration.OggSSPP2F4FrobeniusCandidateNoGo.F4Orbit :=
  Target.stratumOf ∘ Banerjee.toTarget

theorem all_sector_states_share_universal_curve
    {authority : SourceAuthority}
    (realization : SectorRealization authority)
    (state : Banerjee.GaloisInertiaState) :
    (marking realization).underlyingFamilyState state =
      Banerjee.universalCurve := rfl

def markingBidi
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Bidi.Bidi
      (Universal.toUniqueSubgroupMarking (marking realization)) where
  sourceCoarseOrbit := sourceCoarseOrbit
  toTarget := Banerjee.toTarget
  fromTarget := Banerjee.fromTarget
  sourceRoundTrip := Banerjee.source_roundtrip
  targetRoundTrip := Banerjee.target_roundtrip
  toTargetPreservesCoarseOrbit := fun _ => rfl
  fromTargetPreservesCoarseOrbit := by
    intro t
    change
      Target.stratumOf
          (Banerjee.toTarget (Banerjee.fromTarget t)) =
        Target.stratumOf t
    rw [Banerjee.target_roundtrip]
  everyMappedStateStillLiesOverUniqueRawSubgroup := fun _ => rfl

def tenStateRecognition
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Universal.UniversalDeformationTenStateRecognition
      (sourceDatum authority)
      (marking realization) where
  arithmeticBidi := markingBidi realization

theorem realized_state_count_is_ten
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Fintype.card (marking realization).MarkedState = 10 := by
  exact Banerjee.galois_inertia_state_cardinality

inductive Residual
  | missingBanerjeeF4SourceAuthority
  | missingGaloisInertiaSectorRealization
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingBanerjeeF4SourceAuthority

structure Boundary where
  sourceBaseCorrectedFromF2ToF4 : Bool
  explicitUniversalFamilyCarrierPaid : Bool
  allTenSectorsShareOneUniversalFamily : Bool
  g24AndGaloisComeFromSameSourceDeformation : Bool
  galoisSheetKeptDistinctFromQuadraticOrientation : Bool
  sectorRealizationConstructsMarkedSource : Bool
  sectorRealizationConstructsTenStateBidi : Bool
  separateTenStateClassificationProofRequired : Bool
  sectorRealizationInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sourceBaseCorrectedFromF2ToF4 := true
  explicitUniversalFamilyCarrierPaid := true
  allTenSectorsShareOneUniversalFamily := true
  g24AndGaloisComeFromSameSourceDeformation := true
  galoisSheetKeptDistinctFromQuadraticOrientation := true
  sectorRealizationConstructsMarkedSource := true
  sectorRealizationConstructsTenStateBidi := true
  separateTenStateClassificationProofRequired := false
  sectorRealizationInhabitedHere := false

end Integration.OggSSPP2BanerjeeF4SameSourceRealization
