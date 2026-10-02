import Mathlib
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2F4AntipodalStratifiedRefinement
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2TrialecticNineObserverReconciliation

/-!
# Arithmetic bidi -> shared trialectic nine observer is necessarily lossy

Assume a future arithmetic source inhabits the strong bidi contract with the
ten-state p=2 target.  Composing with the shared PhaseNine observer necessarily
identifies the two fixed target branches.

Thus the shared two-trit observer is a lawful finite observation surface, but
cannot itself be injective/full arithmetic recognition.
-/

namespace Integration.OggSSPP2TrialecticNineObserverArithmeticLoss

open Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
open Integration.OggSSPP2UniqueGamma0FourMarkingBidi
open Integration.OggSSPP2F4AntipodalStratifiedRefinement
open Integration.OggSSPP2BalancedTernaryPuncturedPlane
open Integration.OggSSPP2TrialecticNineObserverReconciliation

def arithmeticToPhaseNine
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source)
    (s : source.MarkedState) :
    PhaseNine :=
  duplicatedCentreToPhaseNine
    (stratifiedToDuplicatedCentre (b.toTarget s))

def sourceFixedZero
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    source.MarkedState :=
  b.fromTarget .fixedZero

def sourceFixedOne
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    source.MarkedState :=
  b.fromTarget .fixedOne

theorem source_fixed_states_distinct
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    sourceFixedZero b ≠ sourceFixedOne b := by
  intro h
  have mapped := congrArg b.toTarget h
  rw [b.targetRoundTrip .fixedZero, b.targetRoundTrip .fixedOne] at mapped
  contradiction

theorem fixed_zero_observation_is_centre
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    arithmeticToPhaseNine b (sourceFixedZero b) = (.zero,.zero) := by
  simp [arithmeticToPhaseNine, sourceFixedZero, b.targetRoundTrip,
    stratifiedToDuplicatedCentre, duplicatedCentreToPhaseNine,
    collapseDuplicatedCentre]

theorem fixed_one_observation_is_centre
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    arithmeticToPhaseNine b (sourceFixedOne b) = (.zero,.zero) := by
  simp [arithmeticToPhaseNine, sourceFixedOne, b.targetRoundTrip,
    stratifiedToDuplicatedCentre, duplicatedCentreToPhaseNine,
    collapseDuplicatedCentre]

theorem fixed_arithmetic_states_collide_in_trialectic_nine
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    arithmeticToPhaseNine b (sourceFixedZero b) =
      arithmeticToPhaseNine b (sourceFixedOne b) := by
  rw [fixed_zero_observation_is_centre b, fixed_one_observation_is_centre b]

structure InjectiveArithmeticRecognition
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) where
  observerInjective :
    Function.Injective (arithmeticToPhaseNine b)

theorem shared_nine_observer_cannot_be_injective_arithmetic_recognition
    {source : MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi source) :
    ¬ InjectiveArithmeticRecognition b := by
  intro h
  apply source_fixed_states_distinct b
  exact h.observerInjective
    (fixed_arithmetic_states_collide_in_trialectic_nine b)

inductive LostDatum
  | duplicatedFixedBranch
  deriving DecidableEq, Repr

structure Boundary where
  conditionalOnFutureArithmeticBidi : Bool
  twoFixedSourceStatesProvablyDistinct : Bool
  bothFixedStatesMapToSharedNineCentre : Bool
  sharedNineObserverProvablyNoninjective : Bool
  fullArithmeticRecognitionThroughNineAlonePossible : Bool
  lostDatumIsDuplicatedFixedBranch : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  conditionalOnFutureArithmeticBidi := true
  twoFixedSourceStatesProvablyDistinct := true
  bothFixedStatesMapToSharedNineCentre := true
  sharedNineObserverProvablyNoninjective := true
  fullArithmeticRecognitionThroughNineAlonePossible := false
  lostDatumIsDuplicatedFixedBranch := true

end Integration.OggSSPP2TrialecticNineObserverArithmeticLoss
