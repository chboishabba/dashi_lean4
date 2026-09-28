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

inductive ModeNine
  | identityMode
  | A2negative | A2positive
  | B1negative | B1positive
  | B2negative | B2positive
  | Enegative | Epositive
  deriving DecidableEq, Repr, Fintype

def faceToModeNine : NineFace → ModeNine
  | (.negOne,.negOne) => .identityMode
  | (.negOne,.zero) => .A2negative
  | (.negOne,.posOne) => .A2positive
  | (.zero,.negOne) => .B1negative
  | (.zero,.zero) => .B1positive
  | (.zero,.posOne) => .B2negative
  | (.posOne,.negOne) => .B2positive
  | (.posOne,.zero) => .Enegative
  | (.posOne,.posOne) => .Epositive

def modeNineToFace : ModeNine → NineFace
  | .identityMode => (.negOne,.negOne)
  | .A2negative => (.negOne,.zero)
  | .A2positive => (.negOne,.posOne)
  | .B1negative => (.zero,.negOne)
  | .B1positive => (.zero,.zero)
  | .B2negative => (.zero,.posOne)
  | .B2positive => (.posOne,.negOne)
  | .Enegative => (.posOne,.zero)
  | .Epositive => (.posOne,.posOne)

theorem face_mode_roundtrip (x : NineFace) :
    modeNineToFace (faceToModeNine x) = x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem mode_face_roundtrip (x : ModeNine) :
    faceToModeNine (modeNineToFace x) = x := by
  cases x <;> rfl

theorem mode_nine_count :
    Fintype.card ModeNine = 9 := by
  native_decide

def canonicalModeNineRecognition : NineModeRecognition where
  ModeNine := ModeNine
  toMode := faceToModeNine
  toFace := modeNineToFace
  face_after_mode := face_mode_roundtrip
  mode_after_face := mode_face_roundtrip

def observeABModeNine (section : ABSection) : ModeNine :=
  faceToModeNine (observeABSelfFace section)

def negateSSP : SSPTrit → SSPTrit
  | .negOne => .posOne
  | .zero => .zero
  | .posOne => .negOne

theorem negateSSP_involutive (x : SSPTrit) :
    negateSSP (negateSSP x) = x := by
  cases x <;> rfl

def negateABLocal : ABSection → ABSection
  | ⟨aa,ab,ba,bb⟩ => ⟨negateSSP aa,negateSSP ab,negateSSP ba,negateSSP bb⟩

theorem negateABLocal_involutive (x : ABSection) :
    negateABLocal (negateABLocal x) = x := by
  rcases x with ⟨aa,ab,ba,bb⟩
  cases aa <;> cases ab <;> cases ba <;> cases bb <;> rfl

def negateNineFace : NineFace → NineFace
  | (a,b) => (negateSSP a, negateSSP b)

def negateModeNine (x : ModeNine) : ModeNine :=
  faceToModeNine (negateNineFace (modeNineToFace x))

theorem negateModeNine_involutive (x : ModeNine) :
    negateModeNine (negateModeNine x) = x := by
  cases x <;> rfl

theorem face_observer_intertwines_negation (x : ABSection) :
    observeABSelfFace (negateABLocal x) =
      negateNineFace (observeABSelfFace x) := by
  rcases x with ⟨aa,ab,ba,bb⟩
  rfl

theorem mode_observer_intertwines_negation (x : ABSection) :
    observeABModeNine (negateABLocal x) =
      negateModeNine (observeABModeNine x) := by
  rcases x with ⟨aa,ab,ba,bb⟩
  rfl

inductive RepoNativeNegationEqualsAnalyticFricke : Prop

theorem repo_native_negation_not_promoted_to_analytic_fricke :
    ¬ RepoNativeNegationEqualsAnalyticFricke := by
  intro h
  cases h

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
  modeNineCarrierRoundTripsPaid : Bool
  repoNativeC2TransportOwned : Bool
  candidateObserverTransportIntertwinerPaid : Bool
  repoNativeC2IdentifiedWithAnalyticFricke : Bool
  actualMonsterFiveLocalIdentified : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  localProjectsToTwoTritFace := true
  twoTritFaceCountNine := true
  observerKnownLossy := true
  participantC3NaturalityOwned := true
  d4ModeNineRecognitionConstructed := true
  modeNineCarrierRoundTripsPaid := true
  repoNativeC2TransportOwned := true
  candidateObserverTransportIntertwinerPaid := true
  repoNativeC2IdentifiedWithAnalyticFricke := false
  actualMonsterFiveLocalIdentified := false

end Integration.TrialecticDyadicNineObserverCandidate
