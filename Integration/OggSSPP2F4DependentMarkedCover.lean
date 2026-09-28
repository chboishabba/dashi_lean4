import Mathlib
import Integration.DependentRecoverableProjection
import Integration.OggSSPP2F4AntipodalStratifiedRefinement

/-!
# p=2 F4/F2 dependent marked cover

The exact 1+1+8 target stratification is represented as a state-dependent
residual over the three raw F4 Frobenius orbit labels:

  zeroFixed      -> PUnit
  oneFixed       -> PUnit
  conjugatePair  -> StrictSide × NoncentralNineOrbit

This is an exact target-side normal form. It does not construct the arithmetic
Gaussian-CM / X0(4) marking.
-/

namespace Integration.OggSSPP2F4DependentMarkedCover

open Integration.DependentRecoverableProjection
open Integration.OggSSPP2F4AntipodalStratifiedRefinement
open Integration.OggSSPP2F4FrobeniusCandidateNoGo
open Integration.OggSSPSmallCharacteristicRecognition

def F4OrbitMark : F4Orbit → Type
  | .zeroFixed => PUnit
  | .oneFixed => PUnit
  | .conjugatePair => StrictSide × NoncentralNineOrbit

def markOf :
    (s : StratifiedTargetState) → F4OrbitMark (stratumOf s)
  | .fixedZero => PUnit.unit
  | .fixedOne => PUnit.unit
  | .conjugate side orbit => (side, orbit)

def reopenMarked :
    (o : F4Orbit) → F4OrbitMark o → StratifiedTargetState
  | .zeroFixed, _ => .fixedZero
  | .oneFixed, _ => .fixedOne
  | .conjugatePair, (side, orbit) => .conjugate side orbit

theorem reopen_marked_exact (s : StratifiedTargetState) :
    reopenMarked (stratumOf s) (markOf s) = s := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit => rfl

def p2F4DependentMarkedProjection :
    Projection StratifiedTargetState F4Orbit where
  Residual := F4OrbitMark
  project := stratumOf
  residual := markOf
  reopen := reopenMarked
  reopen_exact := reopen_marked_exact

def encodeMarked :
    StratifiedTargetState → Code p2F4DependentMarkedProjection :=
  encode p2F4DependentMarkedProjection

def decodeMarked :
    Code p2F4DependentMarkedProjection → StratifiedTargetState :=
  decode p2F4DependentMarkedProjection

theorem decode_encode_marked (s : StratifiedTargetState) :
    decodeMarked (encodeMarked s) = s :=
  decode_encode p2F4DependentMarkedProjection s

theorem encode_marked_injective :
    Function.Injective encodeMarked :=
  encode_injective p2F4DependentMarkedProjection

def markFibreSize : F4Orbit → Nat
  | .zeroFixed => 1
  | .oneFixed => 1
  | .conjugatePair => 8

theorem mark_fibre_profile :
    markFibreSize .zeroFixed = 1 ∧
    markFibreSize .oneFixed = 1 ∧
    markFibreSize .conjugatePair = 8 := by
  decide

theorem total_marked_component_count :
    markFibreSize .zeroFixed +
      markFibreSize .oneFixed +
      markFibreSize .conjugatePair = 10 := by
  decide

theorem marking_is_nonuniform :
    markFibreSize .zeroFixed ≠ markFibreSize .conjugatePair := by
  decide

structure ArithmeticGaussianCMMarking where
  FineState : Type
  projection : Projection FineState F4Orbit
  arithmeticLevelFourMarking : Prop
  zeroFixedResidualEquivalent :
    Nonempty (projection.Residual .zeroFixed ≃ F4OrbitMark .zeroFixed)
  oneFixedResidualEquivalent :
    Nonempty (projection.Residual .oneFixed ≃ F4OrbitMark .oneFixed)
  conjugateResidualEquivalent :
    Nonempty (projection.Residual .conjugatePair ≃ F4OrbitMark .conjugatePair)

inductive ClaimOrigin
  | repositoryNewExtension
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def markedCoverOrigin : ClaimOrigin := .repositoryNewExtension
def arithmeticMarkingOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  dependentResidualCoreReused : Bool
  exactOneOneEightMarkFamilyConstructed : Bool
  exactReopenConstructed : Bool
  dependentCodeSeparating : Bool
  uniformMarkingRejected : Bool
  targetNormalFormHasTenComponents : Bool
  arithmeticGaussianCMMarkingConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  dependentResidualCoreReused := true
  exactOneOneEightMarkFamilyConstructed := true
  exactReopenConstructed := true
  dependentCodeSeparating := true
  uniformMarkingRejected := true
  targetNormalFormHasTenComponents := true
  arithmeticGaussianCMMarkingConstructed := false

end Integration.OggSSPP2F4DependentMarkedCover
