import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2BanerjeeF4Gamma0FourEnhancement

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
namespace Enhancement := Integration.OggSSPP2BanerjeeF4Gamma0FourEnhancement

/--
Attributed Banerjee source authority.

This is deliberately NOT an internal proof of the source mathematics.
Each field says that the corresponding statement is present in the canonical
source receipt, whose locator points to Banerjee §3.1 / Proposition 3.1.
-/
structure SourceAuthority where
  receipt : Banerjee.SourceReceipt

  curveOverF4ClaimRecorded :
    receipt.curveOverF4IsY2PlusYEqX3 = true

  specialCurveSupersingularClaimRecorded :
    receipt.specialCurveIsSupersingular = true

  automorphismG24ClaimRecorded :
    receipt.automorphismGroupIsG24 = true

  sameSourceTorsorClaimRecorded :
    receipt.universalDeformationIsG24SemidirectGaloisTorsor = true

  serreTateWittF4PowerSeriesClaimRecorded :
    receipt.serreTateDeformationIsWittF4PowerSeries = true

  oneParameterUniversalDeformationClaimRecorded :
    receipt.oneParameterUniversalDeformationRecorded = true

  universalLiftEquationClaimRecorded :
    receipt.universalLiftEquationRecorded = true

  sourceTitleMatches :
    receipt.sourceTitle =
      "Romie Banerjee, A modular description of ER(2), NYJM 20 (2014) 743-758"

  sourceLocatorMatches :
    receipt.sourceLocator =
      "Section 3.1, Proposition 3.1; arXiv:1212.2069"

/-- Canonical attribution authority from the already-pinned Banerjee receipt. -/
def canonicalSourceAuthority : SourceAuthority where
  receipt := Banerjee.canonicalSourceReceipt
  curveOverF4ClaimRecorded := rfl
  specialCurveSupersingularClaimRecorded := rfl
  automorphismG24ClaimRecorded := rfl
  sameSourceTorsorClaimRecorded := rfl
  serreTateWittF4PowerSeriesClaimRecorded := rfl
  oneParameterUniversalDeformationClaimRecorded := rfl
  universalLiftEquationClaimRecorded := rfl
  sourceTitleMatches := rfl
  sourceLocatorMatches := rfl

/--
Source-claim propositions used by the generic deformation socket.

They are receipt-backed attribution propositions, not Lean reconstructions of
Banerjee's proofs.
-/
def sourceSpecialFibreSupersingular (authority : SourceAuthority) : Prop :=
  authority.receipt.specialCurveIsSupersingular = true

def sourceOneParameterUniversalDeformation (authority : SourceAuthority) : Prop :=
  authority.receipt.oneParameterUniversalDeformationRecorded = true

def sourceCompleteLocalWittF4PowerSeriesShape (authority : SourceAuthority) : Prop :=
  authority.receipt.serreTateDeformationIsWittF4PowerSeries = true

def sourceUniversalProperty (authority : SourceAuthority) : Prop :=
  authority.receipt.universalDeformationIsG24SemidirectGaloisTorsor = true


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
  oneFormalParameter := sourceOneParameterUniversalDeformation authority
  completeLocalWittPowerSeriesShape :=
    sourceCompleteLocalWittF4PowerSeriesShape authority
  supersingularSpecialFibre := sourceSpecialFibreSupersingular authority
  universalPropertyImportedFromSource := sourceUniversalProperty authority
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

theorem canonical_authority_source_claims_paid :
    sourceSpecialFibreSupersingular canonicalSourceAuthority ∧
    sourceOneParameterUniversalDeformation canonicalSourceAuthority ∧
    sourceCompleteLocalWittF4PowerSeriesShape canonicalSourceAuthority ∧
    sourceUniversalProperty canonicalSourceAuthority := by
  exact ⟨rfl, rfl, rfl, rfl⟩


structure SectorRealization
    (authority : SourceAuthority) where
  enhancementFamily :
    Enhancement.EnhancementFamily

/--
Canonical realization constructor once a genuine Gamma_0(4) enhancement family
has been constructed.  No additional free propositions are required.
-/
def realizationFromEnhancement
    (authority : SourceAuthority)
    (family : Enhancement.EnhancementFamily) :
    SectorRealization authority where
  enhancementFamily := family

/-- Preferred realization over the canonically attributed Banerjee source. -/
def canonicalRealizationFromEnhancement
    (family : Enhancement.EnhancementFamily) :
    SectorRealization canonicalSourceAuthority :=
  realizationFromEnhancement canonicalSourceAuthority family



def marking
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Universal.Gamma0FourUniversalDeformationMarking
      (sourceDatum authority) where
  MarkedState := Banerjee.GaloisInertiaState
  underlyingFamilyState := fun _ => Banerjee.universalCurve
  specializesToRawSubgroup := fun _ => .kerFrobeniusSquared
  specializationIsUniqueKerFrobeniusSquared := fun _ => rfl
  gamma0FourLevelStructurePresent := fun state =>
    Nonempty (Enhancement.SectorGamma0FourEnhancement state)
  gamma0FourLevelStructurePresentProof := fun state =>
    ⟨realization.enhancementFamily.enhance state⟩
  deformationProvenanceRetained := fun state =>
    (realization.enhancementFamily.enhance state).sourceSectorRetained = state
  deformationProvenanceRetainedProof := fun state =>
    (realization.enhancementFamily.enhance state).sourceSectorRetainedExact

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

theorem realized_state_has_gamma0_four_enhancement
    {authority : SourceAuthority}
    (realization : SectorRealization authority)
    (state : Banerjee.GaloisInertiaState) :
    Nonempty (Enhancement.SectorGamma0FourEnhancement state) :=
  ⟨realization.enhancementFamily.enhance state⟩


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

/--
Once the finite-flat Gamma_0(4) enhancement family exists, the preferred
Banerjee source marking and ten-state bidi are compiled automatically.
-/
def canonicalSameSourceRecognitionFromEnhancement
    (family : Enhancement.EnhancementFamily) :
    Universal.UniversalDeformationTenStateRecognition
      (sourceDatum canonicalSourceAuthority)
      (marking (canonicalRealizationFromEnhancement family)) :=
  tenStateRecognition (canonicalRealizationFromEnhancement family)


theorem realized_state_count_is_ten
    {authority : SourceAuthority}
    (realization : SectorRealization authority) :
    Fintype.card (marking realization).MarkedState = 10 := by
  exact Banerjee.galois_inertia_state_cardinality

inductive Residual
  | missingFiniteFlatGamma0FourEnhancementFamily
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingFiniteFlatGamma0FourEnhancementFamily

structure Boundary where
  canonicalBanerjeeSourceAuthorityInhabited : Bool
  sourceAuthorityIsAttributionNotInternalProof : Bool
  sourceBaseCorrectedFromF2ToF4 : Bool
  explicitUniversalFamilyCarrierPaid : Bool
  allTenSectorsShareOneUniversalFamily : Bool
  g24AndGaloisComeFromSameSourceDeformation : Bool
  galoisSheetKeptDistinctFromQuadraticOrientation : Bool
  sectorRealizationRequiresFiniteFlatGamma0FourEnhancement : Bool
  sectorRealizationConstructsMarkedSource : Bool
  sectorRealizationConstructsTenStateBidi : Bool
  separateTenStateClassificationProofRequired : Bool
  sectorRealizationInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  canonicalBanerjeeSourceAuthorityInhabited := true
  sourceAuthorityIsAttributionNotInternalProof := true
  sourceBaseCorrectedFromF2ToF4 := true
  explicitUniversalFamilyCarrierPaid := true
  allTenSectorsShareOneUniversalFamily := true
  g24AndGaloisComeFromSameSourceDeformation := true
  galoisSheetKeptDistinctFromQuadraticOrientation := true
  sectorRealizationRequiresFiniteFlatGamma0FourEnhancement := true
  sectorRealizationConstructsMarkedSource := true
  sectorRealizationConstructsTenStateBidi := true
  separateTenStateClassificationProofRequired := false
  sectorRealizationInhabitedHere := false

end Integration.OggSSPP2BanerjeeF4SameSourceRealization
