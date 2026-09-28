import Mathlib
import Integration.ActionOrbitRecognition
import Integration.BalancedTernaryHypercubeAntipodalOrbitCount
import Integration.OggSSPSmallCharacteristicRecognition
import Integration.MarkedArithmeticResidualCover
import Integration.OggSSPSmallCharacteristicAcquisitionDirection

/-!
# Exponent-residual arithmetic source acquisition interface

Lean mirror of the live Agda acquisition wall.

This file does not construct the missing arithmetic source groupoids.  It
requires a future arithmetic source to provide an actual action, orbit
presentation, an exact pi0 count matching the exceptional residual target,
and provenance/construction references.

The target side is concrete:

* p=3: the two-orbit C2 action on three ternary states;
* p=2: the retained-orientation discrete ten-state carrier.

The generic ternary antipodal count family is used only as a target-count
decomposition:
  p=3 -> A1 with 2 components,
  p=2 -> retained binary sheet x A2 with 2 * 5 = 10 components.
-/

namespace Integration.OggSSPExponentResidualArithmeticSource

open Integration.ActionOrbitRecognition
open Integration.OggSSPSmallCharacteristicRecognition
open Integration.BalancedTernaryHypercubeAntipodalOrbitCount

inductive ExceptionalResidualPrime
  | p2
  | p3
  deriving DecidableEq, Repr

def expectedResidualCount : ExceptionalResidualPrime → Nat
  | .p2 => 10
  | .p3 => 2

theorem p2_expected_residual_is_ten :
    expectedResidualCount .p2 = 10 := rfl

theorem p3_expected_residual_is_two :
    expectedResidualCount .p3 = 2 := rfl

def TargetState : ExceptionalResidualPrime → Type
  | .p2 => P2State
  | .p3 => P3State

def TargetSymmetry : ExceptionalResidualPrime → Type
  | .p2 => PUnit
  | .p3 => C2

def targetAction :
    (p : ExceptionalResidualPrime) →
    InvertibleAction (TargetState p) (TargetSymmetry p)
  | .p2 => p2DiscreteAction
  | .p3 => p3Action

def targetOrbits :
    (p : ExceptionalResidualPrime) →
    OrbitPresentation (targetAction p)
  | .p2 => p2DiscreteOrbitPresentation
  | .p3 => p3OrbitPresentation

def targetPi0Count : ExceptionalResidualPrime → Nat
  | .p2 => 10
  | .p3 => 2

theorem target_pi0_matches_expected :
    ∀ p, targetPi0Count p = expectedResidualCount p := by
  intro p
  cases p <;> rfl

/-! ## Target-side ternary antipodal decomposition -/

theorem p3_target_count_is_A1 :
    targetPi0Count .p3 = antipodalOrbitCount 1 := by
  rfl

theorem p2_five_orbit_base_is_A2 :
    5 = antipodalOrbitCount 2 := by
  rfl

theorem p2_target_count_is_binary_times_A2 :
    targetPi0Count .p2 = 2 * antipodalOrbitCount 2 := by
  rfl

theorem p3_hypercube_count_closes_residual :
    antipodalOrbitCount 1 = expectedResidualCount .p3 := by
  rfl

theorem p2_hypercube_count_closes_residual :
    2 * antipodalOrbitCount 2 = expectedResidualCount .p2 := by
  rfl

/-! ## Missing arithmetic source socket -/

structure ArithmeticResidualSource
    (p : ExceptionalResidualPrime) where
  State : Type
  Symmetry : Type
  action : InvertibleAction State Symmetry
  orbits : OrbitPresentation action
  pi0Count : Nat
  pi0CountExact : pi0Count = expectedResidualCount p
  provenance : String
  arithmeticConstructionReference : String
  actionGroupoidExternallySourcedClaim : Bool

def toMarkedCoverPrime :
    ExceptionalResidualPrime →
    Integration.MarkedArithmeticResidualCover.ExceptionalResidualPrime
  | .p2 => .p2
  | .p3 => .p3

structure MarkedCoverArithmeticResidualSourceCandidate
    (p : ExceptionalResidualPrime) where
  markedCoverCandidate :
    Integration.MarkedArithmeticResidualCover.MarkedResidualSourceCandidate
      (toMarkedCoverPrime p)
  source : ArithmeticResidualSource p
  sourceStateEquivMarkedCoverFine :
    Nonempty (source.State ≃ markedCoverCandidate.cover.Fine)
  sourceConstructionUsesMarkedCoverPattern : Prop

def preferredAcquisitionDirection :
    ExceptionalResidualPrime →
    Integration.OggSSPSmallCharacteristicAcquisitionDirection.AcquisitionDirection
  | .p2 =>
      .markedEnrichmentOrCover
  | .p3 =>
      .quotientOrCompression

theorem p2_acquisition_direction_is_marked_enrichment :
    preferredAcquisitionDirection .p2 = .markedEnrichmentOrCover := rfl

theorem p3_acquisition_direction_is_quotient :
    preferredAcquisitionDirection .p3 = .quotientOrCompression := rfl

structure FullResidualRecognition
    (p : ExceptionalResidualPrime)
    (source : ArithmeticResidualSource p) where
  functor :
    ActionRecognitionFunctor source.action (targetAction p)
  recognition :
    FullRecognition functor source.orbits (targetOrbits p)
  pi0CountPreserved :
    source.pi0Count = targetPi0Count p

theorem recognition_count_closes_against_expected
    {p : ExceptionalResidualPrime}
    {source : ArithmeticResidualSource p}
    (R : FullResidualRecognition p source) :
    source.pi0Count = expectedResidualCount p :=
  R.pi0CountPreserved.trans (target_pi0_matches_expected p)

/-! ## Strong same-presentation gate -/

structure ResidualPresentationSameObject
    (p : ExceptionalResidualPrime)
    (source : ArithmeticResidualSource p) where
  functor :
    ActionRecognitionFunctor source.action (targetAction p)
  presentationIsomorphism :
    ActionGroupoidPresentationIsomorphism
      functor source.orbits (targetOrbits p)

/-! ## Firewalls -/

inductive PromotionError
  | residualCountAloneConstructsArithmeticSource
  | hypercubeTargetCountConstructsArithmeticSource
  | targetGroupoidAloneConstructsRecognition
  | fullRecognitionCreatesPresentationIsomorphism
  deriving DecidableEq, Repr

inductive ClaimOrigin
  | externalArithmeticAuthority
  | repositoryFormalReconstruction
  | repositoryNewExtension
  deriving DecidableEq, Repr

def sourceInterfaceOrigin : ClaimOrigin := .repositoryNewExtension

structure Boundary where
  p2TargetActionGroupoidConcrete : Bool
  p3TargetActionGroupoidConcrete : Bool
  p2TargetPi0MatchesResidual : Bool
  p3TargetPi0MatchesResidual : Bool
  p3TargetCountFactorsThroughA1 : Bool
  p2TargetCountFactorsThroughRetainedBinaryTimesA2 : Bool
  sourceRequiresActionAndOrbitPresentation : Bool
  sourceRequiresIndependentPi0Receipt : Bool
  markedCoverAcquisitionPatternAvailable : Bool
  p11MarkedCoverPrecedentRecorded : Bool
  p2SearchDirectionMarkedEnrichment : Bool
  p3SearchDirectionQuotientCompression : Bool
  acquisitionDirectionPromotedToArithmeticAuthority : Bool
  fullRecognitionUsesActionOrbitStabilizerCore : Bool
  samePresentationRequiresStateAndSymmetryBijections : Bool
  p2ArithmeticSourceConstructed : Bool
  p3ArithmeticSourceConstructed : Bool
  countAloneConstructsSource : Bool
  hypercubeTargetCountConstructsSource : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  p2TargetActionGroupoidConcrete := true
  p3TargetActionGroupoidConcrete := true
  p2TargetPi0MatchesResidual := true
  p3TargetPi0MatchesResidual := true
  p3TargetCountFactorsThroughA1 := true
  p2TargetCountFactorsThroughRetainedBinaryTimesA2 := true
  sourceRequiresActionAndOrbitPresentation := true
  sourceRequiresIndependentPi0Receipt := true
  markedCoverAcquisitionPatternAvailable := true
  p11MarkedCoverPrecedentRecorded := true
  p2SearchDirectionMarkedEnrichment := true
  p3SearchDirectionQuotientCompression := true
  acquisitionDirectionPromotedToArithmeticAuthority := false
  fullRecognitionUsesActionOrbitStabilizerCore := true
  samePresentationRequiresStateAndSymmetryBijections := true
  p2ArithmeticSourceConstructed := false
  p3ArithmeticSourceConstructed := false
  countAloneConstructsSource := false
  hypercubeTargetCountConstructsSource := false

end Integration.OggSSPExponentResidualArithmeticSource
