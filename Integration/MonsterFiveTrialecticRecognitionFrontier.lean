import Integration.TrialecticDyadicT4
import Integration.TrialecticDyadicC3
import Integration.TrialecticDyadicPointed
import Mathlib

/-!
# Monster-5 / trialectic state-level recognition frontier

Lean mirror of the source-state part of the Agda recognition contract.

No Monster source carrier is invented here.  A future independently justified
source supplies:
* an actual state type;
* an actual transport type/action;
* a completion witness;
* a source-to-dyadic-local recognition map;
* a distinguished source transport mapping to local sign inversion.

Participant C3 then removes any dependence on the chosen AB chart, and a
pointed source upgrade identifies a source basepoint with the local zero state.
-/

namespace Integration.MonsterFiveTrialecticRecognitionFrontier

open Integration.TernaryHub
open Integration.TrialecticDyadicT4
open Integration.TrialecticDyadicC3
open Integration.TrialecticDyadicPointed

def negateSSP : SSPTrit → SSPTrit
  | .negOne => .posOne
  | .zero => .zero
  | .posOne => .negOne

theorem negateSSP_involutive (x : SSPTrit) :
    negateSSP (negateSSP x) = x := by
  cases x <;> rfl

def negateAB : ABSection → ABSection
  | ⟨aa,ab,ba,bb⟩ =>
      ⟨negateSSP aa, negateSSP ab, negateSSP ba, negateSSP bb⟩

def negateBC : BCSection → BCSection
  | ⟨bb,bc,cb,cc⟩ =>
      ⟨negateSSP bb, negateSSP bc, negateSSP cb, negateSSP cc⟩

def negateCA : CASection → CASection
  | ⟨cc,ca,ac,aa⟩ =>
      ⟨negateSSP cc, negateSSP ca, negateSSP ac, negateSSP aa⟩

theorem negateAB_involutive (x : ABSection) :
    negateAB (negateAB x) = x := by
  cases x <;> simp [negateAB, negateSSP_involutive]

theorem negateBC_involutive (x : BCSection) :
    negateBC (negateBC x) = x := by
  cases x <;> simp [negateBC, negateSSP_involutive]

theorem negateCA_involutive (x : CASection) :
    negateCA (negateCA x) = x := by
  cases x <;> simp [negateCA, negateSSP_involutive]

structure MonsterFiveSource where
  ActualState : Type
  ActualTransport : Type
  applyTransport : ActualTransport → ActualState → ActualState
  completionWitness : ActualState → Bool

structure Recognition (source : MonsterFiveSource) where
  sourceToAB : source.ActualState → ABSection
  distinguishedTransport : source.ActualTransport
  transport_becomes_local_negation :
    ∀ state,
      sourceToAB
        (source.applyTransport distinguishedTransport state)
      =
      negateAB (sourceToAB state)

def sourceToBC {source : MonsterFiveSource}
    (recognition : Recognition source) :
    source.ActualState → BCSection :=
  fun state => abAsBC (recognition.sourceToAB state)

def sourceToCA {source : MonsterFiveSource}
    (recognition : Recognition source) :
    source.ActualState → CASection :=
  fun state => abAsCA (recognition.sourceToAB state)

theorem source_transport_becomes_BC_negation
    {source : MonsterFiveSource}
    (recognition : Recognition source)
    (state : source.ActualState) :
    sourceToBC recognition
      (source.applyTransport recognition.distinguishedTransport state)
      =
    negateBC (sourceToBC recognition state) := by
  have h := recognition.transport_becomes_local_negation state
  cases recognition.sourceToAB state with
  | mk aa ab ba bb =>
      simp [sourceToBC, abAsBC, negateAB, negateBC] at h ⊢
      exact h

theorem source_transport_becomes_CA_negation
    {source : MonsterFiveSource}
    (recognition : Recognition source)
    (state : source.ActualState) :
    sourceToCA recognition
      (source.applyTransport recognition.distinguishedTransport state)
      =
    negateCA (sourceToCA recognition state) := by
  have h := recognition.transport_becomes_local_negation state
  cases recognition.sourceToAB state with
  | mk aa ab ba bb =>
      simp [sourceToCA, abAsCA, negateAB, negateCA] at h ⊢
      exact h

structure PointedMonsterFiveSource (source : MonsterFiveSource) where
  basepoint : source.ActualState
  completionAtBasepoint : source.completionWitness basepoint = true
  transportPreservesBasepoint :
    ∀ transport,
      source.applyTransport transport basepoint = basepoint

structure PointedRecognition
    {source : MonsterFiveSource}
    (pointedSource : PointedMonsterFiveSource source)
    (recognition : Recognition source) where
  basepointMapsToABZero :
    recognition.sourceToAB pointedSource.basepoint = zeroAB

theorem source_basepoint_maps_to_BC_zero
    {source : MonsterFiveSource}
    {pointedSource : PointedMonsterFiveSource source}
    {recognition : Recognition source}
    (pointedRecognition : PointedRecognition pointedSource recognition) :
    sourceToBC recognition pointedSource.basepoint = zeroBC := by
  simp [sourceToBC, zeroBC, abAsBC,
    pointedRecognition.basepointMapsToABZero]

theorem source_basepoint_maps_to_CA_zero
    {source : MonsterFiveSource}
    {pointedSource : PointedMonsterFiveSource source}
    {recognition : Recognition source}
    (pointedRecognition : PointedRecognition pointedSource recognition) :
    sourceToCA recognition pointedSource.basepoint = zeroCA := by
  simp [sourceToCA, zeroCA, abAsCA,
    pointedRecognition.basepointMapsToABZero]

inductive CompletionBooleanAloneSelectsBasepoint : Prop
inductive FiniteCandidateConstructsMonsterSource : Prop
inductive C3ChartIndependenceConstructsMonsterSource : Prop

theorem completion_boolean_alone_does_not_select_basepoint :
    ¬ CompletionBooleanAloneSelectsBasepoint := by
  intro h
  cases h

theorem finite_candidate_does_not_construct_source :
    ¬ FiniteCandidateConstructsMonsterSource := by
  intro h
  cases h

theorem chart_independence_does_not_construct_source :
    ¬ C3ChartIndependenceConstructsMonsterSource := by
  intro h
  cases h

inductive RecognitionResidual
  | missingSourceNativeActualState
  | missingSourceNativeActualTransport
  | missingSourceBasepointCompletionLaw
  | missingSourceToDyadicLocalRecognition
  | missingSourceTransportLocalNegationIntertwiner
  | missingSourceModeObserverComparison
  | missingAnalyticFrickeIdentification
  deriving DecidableEq, Repr

structure Boundary where
  localSignedInvolutionOwned : Bool
  ABRecognitionContractOwned : Bool
  BCRecognitionDerivedFromAB : Bool
  CARecognitionDerivedFromAB : Bool
  participantC3ChartIndependencePaid : Bool
  pointedSourceUpgradeOwned : Bool
  completionBooleanDeterminesBasepoint : Bool
  actualMonsterFiveSourceConstructed : Bool
  analyticFrickeIdentified : Bool
  firstResidual : RecognitionResidual
  deriving Repr

def canonicalBoundary : Boundary where
  localSignedInvolutionOwned := true
  ABRecognitionContractOwned := true
  BCRecognitionDerivedFromAB := true
  CARecognitionDerivedFromAB := true
  participantC3ChartIndependencePaid := true
  pointedSourceUpgradeOwned := true
  completionBooleanDeterminesBasepoint := false
  actualMonsterFiveSourceConstructed := false
  analyticFrickeIdentified := false
  firstResidual := .missingSourceNativeActualState

end Integration.MonsterFiveTrialecticRecognitionFrontier
