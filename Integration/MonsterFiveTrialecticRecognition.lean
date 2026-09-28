import Integration.TrialecticDyadicNineObserverCandidate
import Mathlib

/-!
# Monster-five source -> trialectic local recognition contract

Lean mirror of the Agda recognition frontier.

The trialectic side already owns:
- ABSection -> ModeNine;
- involutive local sign negation;
- induced involutive ModeNine transport;
- exact observer intertwining.

The remaining payment is source recognition: an independently justified
arithmetic/Monster source state maps to the dyadic local, and one distinguished
source transport becomes the local signed involution.
-/

namespace Integration.MonsterFiveTrialecticRecognition

open Integration.TrialecticDyadicT4
open Integration.TrialecticDyadicNineObserverCandidate

structure MonsterFiveSource where
  State : Type
  Transport : Type
  applyTransport : Transport → State → State
  observeMode : State → ModeNine
  modelTransport : Transport → ModeNine → ModeNine

structure Recognition (source : MonsterFiveSource) where
  sourceToLocal : source.State → ABSection
  distinguishedTransport : source.Transport

  sourceTransportBecomesLocalNegation :
    ∀ state,
      sourceToLocal
        (source.applyTransport distinguishedTransport state)
      =
      negateABLocal (sourceToLocal state)

  sourceObserverAgreesWithLocalObserver :
    ∀ state,
      source.observeMode state =
        observeABModeNine (sourceToLocal state)

theorem source_observer_after_distinguished_transport
    {source : MonsterFiveSource}
    (recognition : Recognition source)
    (state : source.State) :
    source.observeMode
      (source.applyTransport recognition.distinguishedTransport state)
    =
    negateModeNine (source.observeMode state) := by
  calc
    source.observeMode
        (source.applyTransport recognition.distinguishedTransport state)
        =
      observeABModeNine
        (recognition.sourceToLocal
          (source.applyTransport recognition.distinguishedTransport state)) :=
      recognition.sourceObserverAgreesWithLocalObserver _
    _ =
      observeABModeNine
        (negateABLocal (recognition.sourceToLocal state)) := by
      rw [recognition.sourceTransportBecomesLocalNegation]
    _ =
      negateModeNine
        (observeABModeNine (recognition.sourceToLocal state)) :=
      mode_observer_intertwines_negation _
    _ =
      negateModeNine (source.observeMode state) := by
      rw [recognition.sourceObserverAgreesWithLocalObserver]

structure ModelTransportMatch
    {source : MonsterFiveSource}
    (recognition : Recognition source) where
  sourceModelTransportIsCandidateNegation :
    ∀ mode,
      source.modelTransport recognition.distinguishedTransport mode =
        negateModeNine mode

theorem source_intertwiner_factors_through_candidate
    {source : MonsterFiveSource}
    (recognition : Recognition source)
    (match : ModelTransportMatch recognition)
    (state : source.State) :
    source.observeMode
      (source.applyTransport recognition.distinguishedTransport state)
    =
    source.modelTransport recognition.distinguishedTransport
      (source.observeMode state) := by
  rw [source_observer_after_distinguished_transport recognition state]
  symm
  exact match.sourceModelTransportIsCandidateNegation (source.observeMode state)

inductive CandidateAloneConstructsMonsterSource : Prop
inductive FiniteC2AloneIdentifiesAnalyticFricke : Prop

theorem candidate_does_not_construct_monster_source :
    ¬ CandidateAloneConstructsMonsterSource := by
  intro h
  cases h

theorem finite_c2_does_not_identify_analytic_fricke :
    ¬ FiniteC2AloneIdentifiesAnalyticFricke := by
  intro h
  cases h

structure Boundary where
  finiteLocalModeObserverPaid : Bool
  finiteSignedC2IntertwinerPaid : Bool
  sourceToLocalRecognitionRequired : Bool
  distinguishedSourceTransportRequired : Bool
  modelTransportComparisonRequired : Bool
  actualMonsterSourceConstructedHere : Bool
  analyticFrickeIdentifiedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteLocalModeObserverPaid := true
  finiteSignedC2IntertwinerPaid := true
  sourceToLocalRecognitionRequired := true
  distinguishedSourceTransportRequired := true
  modelTransportComparisonRequired := true
  actualMonsterSourceConstructedHere := false
  analyticFrickeIdentifiedHere := false

end Integration.MonsterFiveTrialecticRecognition
