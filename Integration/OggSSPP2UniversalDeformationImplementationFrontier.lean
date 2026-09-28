import Mathlib
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesCompleteness
import Integration.OggSSPP2WittPowerSeriesMaximalIdeal
import Integration.OggSSPP2WittPowerSeriesMixedAdicControl
import Integration.OggSSPP2ExplicitF2CurveCandidate
import Integration.OggSSPP2ResidueFieldDescentBoundary
import Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2BanerjeeF4SameSourceRealization
import Integration.OggSSPP2Gamma0FourSchemeLevelRealizationFrontier
import Integration.OggSSPP2BanerjeeF4Gamma0FourEnhancement

/-!
# p=2 universal-deformation implementation frontier

The preferred source path is now Banerjee's same-source supersingular
deformation over W(F4)[[a1]].  The attributed source authority, explicit
computational universal Weierstrass family, G24 ⋊ Gal source torsor, and the
finite ten-sector vocabulary are paid.

The live implementation dependency chain is therefore:

  Banerjee W(F4)[[a1]] universal family                  [paid]
    -> scheme realization of that elliptic family
    -> finite-flat subgroup schemes ker(F) <= ker(F²)
    -> Gamma_0(4) local-model / sector enhancement
    -> marked source + ten-state bidi                    [automatic afterward].

The older F2-specialized Witt path remains only as an independently checked
control/specialization and is not promoted to the preferred source.
-/

namespace Integration.OggSSPP2UniversalDeformationImplementationFrontier

inductive Residual
  | missingFiniteFlatGamma0FourEnhancementFamily
  deriving DecidableEq, Repr

def firstImplementationResidual : Residual :=
  .missingFiniteFlatGamma0FourEnhancementFamily

structure WittPowerSeriesBaseImplementation where
  ResidueField : Type
  WittRing : Type
  FormalParameter : Type
  PowerSeriesBase : Type

  wittRingConstructed : Prop
  powerSeriesBaseConstructed : Prop
  completeLocalStructureConstructed : Prop

structure UniversalDeformationImplementation
    (base : WittPowerSeriesBaseImplementation) where
  sourceDatum :
    Integration.OggSSPP2SupersingularUniversalDeformationSource.SupersingularUniversalDeformationDatum

  sourceUsesImplementedBase : Prop

structure Boundary where
  mathlibWittVectorCarrierReused : Bool
  mathlibPowerSeriesCarrierReused : Bool
  f2SpecializationNotPromotedToUniversalSource : Bool
  preferredUniversalSourceBaseIsWittF4PowerSeries : Bool
  banerjeeF4SourceDonorOwned : Bool
  explicitBanerjeeUniversalFamilyOwned : Bool
  banerjeeSourceAuthorityAttributedAndInhabited : Bool
  gamma0FourEnhancementContractOwned : Bool
  schemeLevelFiniteFlatGamma0FourFrontierOwned : Bool
  galoisInertiaSectorRealizationContractOwned : Bool
  explicitF2CurveCandidateOwned : Bool
  explicitF2CurveDiscriminantAndTracePaid : Bool
  concreteF2SourceRecognitionContractOwned : Bool
  geometricSupersingularityAndResidueFieldCollapsedToOneAuthority : Bool
  wittEquivTwoAdicsReused : Bool
  algebraicLocalRingBasePaid : Bool
  coefficientMaximalIdealAdicCompletenessPaid : Bool
  coefficientwiseCompletenessPaid : Bool
  xAdicCompletenessPaid : Bool
  actualPowerSeriesMaximalIdealIdentified : Bool
  powerSeriesMaximalIdealEqualsCoefficientMaxPlusX : Bool
  mixedPowerCoefficientControlPaid : Bool
  mixedAdicHausdorffPaid : Bool
  mixedAdicPrecompletePaid : Bool
  maximalIdealAdicCompletenessPaid : Bool
  universalEllipticFamilyRequiredAfterBase : Bool
  separateMarkedStateConstructionRequiredAfterSectorRealization : Bool
  separateTenStateBidiRequiredAfterSectorRealization : Bool
  firstResidualIsFiniteFlatGamma0FourEnhancementFamily : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mathlibWittVectorCarrierReused := true
  mathlibPowerSeriesCarrierReused := true
  f2SpecializationNotPromotedToUniversalSource := true
  preferredUniversalSourceBaseIsWittF4PowerSeries := true
  banerjeeF4SourceDonorOwned := true
  explicitBanerjeeUniversalFamilyOwned := true
  banerjeeSourceAuthorityAttributedAndInhabited := true
  gamma0FourEnhancementContractOwned := true
  schemeLevelFiniteFlatGamma0FourFrontierOwned := true
  galoisInertiaSectorRealizationContractOwned := true
  explicitF2CurveCandidateOwned := true
  explicitF2CurveDiscriminantAndTracePaid := true
  concreteF2SourceRecognitionContractOwned := true
  geometricSupersingularityAndResidueFieldCollapsedToOneAuthority := true
  wittEquivTwoAdicsReused := true
  algebraicLocalRingBasePaid := true
  coefficientMaximalIdealAdicCompletenessPaid := true
  coefficientwiseCompletenessPaid := true
  xAdicCompletenessPaid := true
  actualPowerSeriesMaximalIdealIdentified := true
  powerSeriesMaximalIdealEqualsCoefficientMaxPlusX := true
  mixedPowerCoefficientControlPaid := true
  mixedAdicHausdorffPaid := true
  mixedAdicPrecompletePaid := true
  maximalIdealAdicCompletenessPaid := true
  universalEllipticFamilyRequiredAfterBase := false
  separateMarkedStateConstructionRequiredAfterSectorRealization := false
  separateTenStateBidiRequiredAfterSectorRealization := false
  firstResidualIsFiniteFlatGamma0FourEnhancementFamily := true

end Integration.OggSSPP2UniversalDeformationImplementationFrontier
