import Mathlib
import Integration.OggSSPP2SupersingularUniversalDeformationSource

/-!
# p=2 universal-deformation implementation frontier

The Lean branch audit found no existing Witt-vector, complete-local-ring, or
formal-power-series implementation to instantiate the universal deformation
base W(k)[[t]].

So the implementation dependency chain is recorded explicitly:

  Witt vector ring
    -> complete local power-series base
    -> supersingular universal elliptic family
    -> Gamma_0(4) marked deformation states
    -> ten-state arithmetic bidi.

This file is an implementation frontier only.
-/

namespace Integration.OggSSPP2UniversalDeformationImplementationFrontier

inductive Residual
  | missingWittVectorRingCarrier
  | missingCompleteLocalPowerSeriesBase
  | missingSupersingularUniversalEllipticFamily
  | missingGamma0FourMarkedDeformationStates
  | missingTenStateClassificationBidi
  deriving DecidableEq, Repr

def firstImplementationResidual : Residual :=
  .missingWittVectorRingCarrier

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
  leanWittVectorCarrierFoundInRepo : Bool
  leanCompleteLocalPowerSeriesCarrierFoundInRepo : Bool
  wittVectorRingCarrierRequired : Bool
  completeLocalPowerSeriesBaseRequired : Bool
  universalEllipticFamilyRequiredAfterBase : Bool
  gamma0FourMarkedStatesRequiredAfterFamily : Bool
  tenStateBidiRequiredAfterMarkedStates : Bool
  firstResidualIsWittVectorRingCarrier : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  leanWittVectorCarrierFoundInRepo := false
  leanCompleteLocalPowerSeriesCarrierFoundInRepo := false
  wittVectorRingCarrierRequired := true
  completeLocalPowerSeriesBaseRequired := true
  universalEllipticFamilyRequiredAfterBase := true
  gamma0FourMarkedStatesRequiredAfterFamily := true
  tenStateBidiRequiredAfterMarkedStates := true
  firstResidualIsWittVectorRingCarrier := true

end Integration.OggSSPP2UniversalDeformationImplementationFrontier
