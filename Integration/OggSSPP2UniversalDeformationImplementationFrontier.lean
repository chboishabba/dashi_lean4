import Mathlib
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2WittPowerSeriesBase

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
  | missingCompleteTopologicalUniversalDeformationStructure
  | missingSupersingularUniversalEllipticFamily
  | missingGamma0FourMarkedDeformationStates
  | missingTenStateClassificationBidi
  deriving DecidableEq, Repr

def firstImplementationResidual : Residual :=
  .missingCompleteTopologicalUniversalDeformationStructure

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
  wittEquivTwoAdicsReused : Bool
  algebraicLocalRingBasePaid : Bool
  completeTopologicalUniversalDeformationStructureRequired : Bool
  universalEllipticFamilyRequiredAfterBase : Bool
  gamma0FourMarkedStatesRequiredAfterFamily : Bool
  tenStateBidiRequiredAfterMarkedStates : Bool
  firstResidualIsCompleteTopologicalUniversalStructure : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mathlibWittVectorCarrierReused := true
  mathlibPowerSeriesCarrierReused := true
  wittEquivTwoAdicsReused := true
  algebraicLocalRingBasePaid := true
  completeTopologicalUniversalDeformationStructureRequired := true
  universalEllipticFamilyRequiredAfterBase := true
  gamma0FourMarkedStatesRequiredAfterFamily := true
  tenStateBidiRequiredAfterMarkedStates := true
  firstResidualIsCompleteTopologicalUniversalStructure := true

end Integration.OggSSPP2UniversalDeformationImplementationFrontier
