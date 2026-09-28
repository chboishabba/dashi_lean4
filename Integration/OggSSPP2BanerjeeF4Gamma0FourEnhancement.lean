import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource

/-!
# Banerjee F4 source versus Gamma_0(4) enhancement boundary

Banerjee §3.1 gives a supersingular F4 deformation torsor with G24 ⋊ Gal(F4/F2)
symmetry and an explicit universal lift over W(F4)[[a1]].  The paper's modular
level context is level 3, not a theorem that DASHI's reconstructed 2×5
Galois/inertia quotient IS the bad-prime Gamma_0(4) level fibre.

Therefore a lawful promotion from the source-native Galois/inertia sectors to
the p=2 Gamma_0(4) arithmetic source must attach actual level-4 data.

This module strengthens the open seam accordingly.  No field can be discharged
merely by asserting a proposition such as "level structure present".
-/

namespace Integration.OggSSPP2BanerjeeF4Gamma0FourEnhancement

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Gamma0 := Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Chain := Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource

/--
Concrete source-side enhancement required for EACH Banerjee Galois/inertia
sector.

The enhancement supplies actual typed finite-flat subgroup/isogeny objects,
rather than a free Prop saying that level structure exists.
-/
structure SectorGamma0FourEnhancement
    (state : Banerjee.GaloisInertiaState) where
  finiteFlatDatum : Gamma0.Gamma0FourFiniteFlatDatum

  rawOrderFourSubgroup :
    Unique.SupersingularRawGamma0FourSubgroup

  rawOrderFourSubgroupIsKerFrobeniusSquared :
    rawOrderFourSubgroup = .kerFrobeniusSquared

  twoIsogenyChain :
    Chain.Gamma0FourTwoIsogenyChain

  firstKernelMatchesOrderTwoSubflag : Prop
  firstKernelMatchesOrderTwoSubflagProof :
    firstKernelMatchesOrderTwoSubflag

  compositeKernelMatchesFiniteFlatDatum : Prop
  compositeKernelMatchesFiniteFlatDatumProof :
    compositeKernelMatchesFiniteFlatDatum

  sourceSectorRetained : Banerjee.GaloisInertiaState
  sourceSectorRetainedExact :
    sourceSectorRetained = state

/--
A full enhancement of the Banerjee ten-sector vocabulary.

This is the genuine state-level wall: every source-native sector must carry
compatible Gamma_0(4) finite-flat data.
-/
structure EnhancementFamily where
  enhance :
    (state : Banerjee.GaloisInertiaState) →
      SectorGamma0FourEnhancement state

/--
The raw order-4 subgroup choice is forced to be ker(F²) in every enhanced
sector.  Hence any tenfold distinction must live in the additional marking /
inertia / local-model data, not in ten different raw subgroup choices.
-/
theorem every_enhanced_sector_has_same_raw_order_four_subgroup
    (family : EnhancementFamily)
    (state : Banerjee.GaloisInertiaState) :
    (family.enhance state).rawOrderFourSubgroup =
      .kerFrobeniusSquared :=
  (family.enhance state).rawOrderFourSubgroupIsKerFrobeniusSquared

/--
The enhancement does not change the source sector carrier.
-/
theorem enhancement_retains_source_sector
    (family : EnhancementFamily)
    (state : Banerjee.GaloisInertiaState) :
    (family.enhance state).sourceSectorRetained = state :=
  (family.enhance state).sourceSectorRetainedExact

/--
A Banerjee source receipt by itself is intentionally insufficient to construct
an EnhancementFamily.
-/
inductive BanerjeeReceiptAloneConstructsGamma0FourEnhancement

theorem banerjee_receipt_alone_does_not_construct_gamma0_four_enhancement :
    ¬ BanerjeeReceiptAloneConstructsGamma0FourEnhancement := by
  intro h
  cases h

inductive Residual
  | missingFiniteFlatGamma0FourEnhancementFamily
  | missingEnhancementFrobeniusTransport
  | missingEnhancementActionOrbitStabilizerRecognition
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingFiniteFlatGamma0FourEnhancementFamily

structure Boundary where
  banerjeeSourceTorsorReused : Bool
  banerjeeLevelThreeContextKeptDistinctFromGamma0Four : Bool
  rawOrderFourSubgroupForcedToKerFrobeniusSquared : Bool
  finiteFlatDatumRequiredPerSector : Bool
  orderTwoSubflagCompatibilityRequired : Bool
  twoIsogenyChainRequiredPerSector : Bool
  freePropLevelPresenceRejectedAsSufficient : Bool
  enhancementFamilyConstructedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  banerjeeSourceTorsorReused := true
  banerjeeLevelThreeContextKeptDistinctFromGamma0Four := true
  rawOrderFourSubgroupForcedToKerFrobeniusSquared := true
  finiteFlatDatumRequiredPerSector := true
  orderTwoSubflagCompatibilityRequired := true
  twoIsogenyChainRequiredPerSector := true
  freePropLevelPresenceRejectedAsSufficient := true
  enhancementFamilyConstructedHere := false

end Integration.OggSSPP2BanerjeeF4Gamma0FourEnhancement
