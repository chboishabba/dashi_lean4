import Mathlib
import Integration.DependentRecoverableProjection
import Integration.OggSSPP2F4FrobeniusCandidateNoGo
import Integration.OggSSPP2F4DependentMarkedCover
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2BadPrimeLevelStructureBoundary

/-!
# p=2 Gamma_0(4) finite-flat marked subgroup-scheme source socket

At the bad prime p=2, the intended X_0(4) source must be represented as
finite-flat cyclic subgroup / isogeny data, not as a naive E[4] point set.

This module packages the exact missing source-side contract:

* supersingular elliptic object in characteristic 2;
* cyclic finite-flat subgroup of order/rank 4;
* its order/rank 2 subflag;
* Frobenius transport;
* coarse projection to the three F4/F2 Frobenius strata;
* dependent arithmetic marking over those strata;
* equivalence with the paid target fibres Unit, Unit, punctured T^2.

No arithmetic source is constructed here.
-/

namespace Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

open Integration.DependentRecoverableProjection
open Integration.OggSSPP2F4FrobeniusCandidateNoGo
open Integration.OggSSPP2F4DependentMarkedCover
open Integration.OggSSPP2BalancedTernaryPuncturedPlane
open Integration.OggSSPP2BadPrimeLevelStructureBoundary

structure Gamma0FourFiniteFlatDatum where
  EllipticObject : Type
  OrderFourSubgroup : Type
  OrderTwoSubgroup : Type

  selectedEllipticObject : EllipticObject
  selectedOrderFourSubgroup : OrderFourSubgroup
  selectedOrderTwoSubgroup : OrderTwoSubgroup

  orderFourRank : Nat
  orderFourRankIsFour : orderFourRank = 4

  orderTwoRank : Nat
  orderTwoRankIsTwo : orderTwoRank = 2

  orderTwoSubflagOfOrderFour : Prop
  finiteFlatAtCharacteristicTwo : Prop
  gammaZeroLevelFourSemantics : Prop

  sourceReference : String

structure Gamma0FourMarkedArithmeticSource where
  datum : Gamma0FourFiniteFlatDatum
  MarkedState : Type
  frobenius : MarkedState → MarkedState
  frobeniusInvolutive : ∀ s, frobenius (frobenius s) = s
  coarseF4Orbit : MarkedState → F4Orbit
  coarseF4OrbitInvariant :
    ∀ s, coarseF4Orbit (frobenius s) = coarseF4Orbit s

structure Gamma0FourOneOneEightRecognition
    (source : Gamma0FourMarkedArithmeticSource) where
  ArithmeticMark : F4Orbit → Type

  projection :
    Projection source.MarkedState F4Orbit

  projectionUsesArithmeticMark :
    ∀ orbit, Nonempty (projection.Residual orbit ≃ ArithmeticMark orbit)

  zeroFixedMarkEquivalent :
    Nonempty (ArithmeticMark .zeroFixed ≃ F4OrbitMark .zeroFixed)

  oneFixedMarkEquivalent :
    Nonempty (ArithmeticMark .oneFixed ≃ F4OrbitMark .oneFixed)

  conjugateMarkEquivalent :
    Nonempty (ArithmeticMark .conjugatePair ≃ PuncturedNineSheet)

  frobeniusCompatibility : Prop

def targetZeroFixedMarkCount : Nat := 1
def targetOneFixedMarkCount : Nat := 1
def targetConjugateMarkCount : Nat := Fintype.card PuncturedNineSheet

theorem target_conjugate_mark_count_is_eight :
    targetConjugateMarkCount = 8 := by decide

theorem target_total_mark_count_is_ten :
    targetZeroFixedMarkCount +
      targetOneFixedMarkCount +
      targetConjugateMarkCount = 10 := by
  decide

inductive SourceResidual
  | missingFiniteFlatCyclicOrderFourSubgroup
  | missingOrderTwoSubflag
  | missingArithmeticFrobeniusTransport
  | missingArithmeticOneOneEightFibreEquivalence
  | missingActionOrbitStabilizerRecognition
  deriving DecidableEq, Repr

inductive ClaimOrigin
  | externalSourceContext
  | repositoryNewExtension
  | openArithmeticRecognition
  deriving DecidableEq, Repr

structure Boundary where
  badPrimeModuliBoundaryConsumed : Bool
  gamma0TypedAsSubgroupSchemeDatum : Bool
  orderTwoSubflagRequired : Bool
  fullDrinfeldBasisRejectedAsAutomaticSubstitute : Bool
  gamma1PointRejectedAsAutomaticSubstitute : Bool
  naiveE4PointSetRejectedAsAutomaticSubstitute : Bool
  oneOneEightTargetFibreTyped : Bool
  arithmeticGamma0FourSourceConstructed : Bool
  arithmeticFibreEquivalenceConstructed : Bool
  fullRecognitionConstructed : Bool
  firstResidual : SourceResidual
  deriving Repr

def canonicalBoundary : Boundary where
  badPrimeModuliBoundaryConsumed := true
  gamma0TypedAsSubgroupSchemeDatum := true
  orderTwoSubflagRequired := true
  fullDrinfeldBasisRejectedAsAutomaticSubstitute := true
  gamma1PointRejectedAsAutomaticSubstitute := true
  naiveE4PointSetRejectedAsAutomaticSubstitute := true
  oneOneEightTargetFibreTyped := true
  arithmeticGamma0FourSourceConstructed := false
  arithmeticFibreEquivalenceConstructed := false
  fullRecognitionConstructed := false
  firstResidual := .missingFiniteFlatCyclicOrderFourSubgroup

end Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
