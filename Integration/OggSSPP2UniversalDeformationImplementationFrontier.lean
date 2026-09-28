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

/-!
# p=2 universal-deformation implementation frontier

Mathlib supplies the p=2 Witt-vector carrier, the one-variable power-series
carrier, and enough local-ring algebra to make W(F_2)[[t]] a local ring.
What remains is the complete topological/universal-deformation structure.

The implementation dependency chain is therefore:

  algebraic local base W(F_2)[[t]]   [paid]
    -> complete topological universal-deformation structure
    -> supersingular universal elliptic family
    -> Gamma_0(4) marked deformation states
    -> ten-state arithmetic bidi.

This file is an implementation frontier only.
-/

namespace Integration.OggSSPP2UniversalDeformationImplementationFrontier

inductive Residual
  | missingBanerjeeF4SourceAuthority
  | missingGaloisInertiaSectorRealization
  deriving DecidableEq, Repr

def firstImplementationResidual : Residual :=
  .missingBanerjeeF4SourceAuthority

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
  firstResidualIsBanerjeeF4SourceAuthority : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mathlibWittVectorCarrierReused := true
  mathlibPowerSeriesCarrierReused := true
  f2SpecializationNotPromotedToUniversalSource := true
  preferredUniversalSourceBaseIsWittF4PowerSeries := true
  banerjeeF4SourceDonorOwned := true
  explicitBanerjeeUniversalFamilyOwned := true
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
  firstResidualIsBanerjeeF4SourceAuthority := true

end Integration.OggSSPP2UniversalDeformationImplementationFrontier
