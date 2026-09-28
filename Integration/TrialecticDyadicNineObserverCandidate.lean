import Integration.TrialecticDyadicT4
import Integration.TrialecticDyadicC3
import Integration.TernaryHub
import Mathlib

/-!
# Dyadic T4 local -> two-trit nine-observer candidate

Lean mirror of the Agda candidate layer.

A dyadic local has four trits. Project its two self/overlap coordinates to the
two-trit carrier SSPTrit x SSPTrit, which has exactly nine states.

This is intentionally kept distinct from any future D4/five-mode nine-state
recognition. Shared cardinality alone does not identify the carriers.
-/

namespace Integration.TrialecticDyadicNineObserverCandidate

open Integration.TrialecticDyadicT4
open Integration.TrialecticDyadicC3
open Integration.TernaryHub

abbrev NineFace := SSPTrit × SSPTrit

def observeABSelfFace : ABSection → NineFace
  | section => (section.aa, section.bb)

def observeBCSelfFace : BCSection → NineFace
  | section => (section.bb, section.cc)

def observeCASelfFace : CASection → NineFace
  | section => (section.cc, section.aa)

theorem nine_face_count :
    Fintype.card NineFace = 9 := by
  native_decide

def sameFaceLeft : ABSection :=
  ⟨.zero, .negOne, .zero, .zero⟩

def sameFaceRight : ABSection :=
  ⟨.zero, .posOne, .zero, .zero⟩

theorem same_face_observation :
    observeABSelfFace sameFaceLeft = observeABSelfFace sameFaceRight := rfl

theorem same_face_states_distinct :
    sameFaceLeft ≠ sameFaceRight := by
  decide

theorem ab_observer_after_rotate_is_bc (state : T9Carrier) :
    observeABSelfFace (restrictAB (rotateABC state)) =
      observeBCSelfFace (restrictBC state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem ab_observer_after_rotate_twice_is_ca (state : T9Carrier) :
    observeABSelfFace (restrictAB (rotateABC (rotateABC state))) =
      observeCASelfFace (restrictCA state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

structure NineModeRecognition where
  ModeNine : Type
  toMode : NineFace → ModeNine
  toFace : ModeNine → NineFace
  face_after_mode : ∀ x, toFace (toMode x) = x
  mode_after_face : ∀ x, toMode (toFace x) = x

inductive SharedNineCardinalityCreatesRecognition : Prop
inductive TrialecticCandidateIsActualMonsterFiveLocal : Prop

theorem shared_nine_cardinality_does_not_create_recognition :
    ¬ SharedNineCardinalityCreatesRecognition := by
  intro h
  cases h

theorem candidate_not_promoted_to_actual_monster_five_local :
    ¬ TrialecticCandidateIsActualMonsterFiveLocal := by
  intro h
  cases h

structure Boundary where
  localProjectsToTwoTritFace : Bool
  twoTritFaceCountNine : Bool
  observerKnownLossy : Bool
  participantC3NaturalityOwned : Bool
  d4ModeNineRecognitionConstructed : Bool
  actualMonsterFiveLocalIdentified : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  localProjectsToTwoTritFace := true
  twoTritFaceCountNine := true
  observerKnownLossy := true
  participantC3NaturalityOwned := true
  d4ModeNineRecognitionConstructed := false
  actualMonsterFiveLocalIdentified := false

end Integration.TrialecticDyadicNineObserverCandidate
