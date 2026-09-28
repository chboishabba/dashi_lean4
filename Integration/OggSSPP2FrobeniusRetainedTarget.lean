import Mathlib
import Integration.ActionOrbitRecognition
import Integration.OggSSPSmallCharacteristicRecognition

/-!
# p=2 moving Frobenius versus retained targets

Lean mirror of the Agda p=2 recognition refinement.

Two results are kept distinct:

1. A genuinely moving C2 source cannot fully recognize the current
   identity-only ten-state retained target when stabilizer reflection is part of
   FullRecognition.
2. A target-side positive control with twenty fine states and a free C2 sheet
   action has ten orbit components while retaining genuine Frobenius motion.

No arithmetic supersingular/CM identification is claimed.
-/

namespace Integration.OggSSPP2FrobeniusRetainedTarget

open Integration.ActionOrbitRecognition
open Integration.OggSSPSmallCharacteristicRecognition

/-! ## Moving source obstruction against the identity-only target -/

structure MovingP2FrobeniusSource where
  State : Type
  action : InvertibleAction State C2
  orbits : OrbitPresentation action
  movedOrbit : orbits.Orbit
  frobeniusMovesRepresentative :
    action.act .flip (orbits.representative movedOrbit) ≠
      orbits.representative movedOrbit

theorem moving_frobenius_cannot_fully_recognize_identity_target
    (S : MovingP2FrobeniusSource)
    (F : ActionRecognitionFunctor S.action p2DiscreteAction) :
    ¬ Nonempty (FullRecognition F S.orbits p2DiscreteOrbitPresentation) := by
  rintro ⟨R⟩
  have targetFixed :
      p2DiscreteAction.act
          (F.mapSymmetry C2.flip)
          (p2DiscreteOrbitPresentation.representative
            (R.orbitRecognition.mapOrbit S.movedOrbit))
        =
      p2DiscreteOrbitPresentation.representative
        (R.orbitRecognition.mapOrbit S.movedOrbit) := by
    cases F.mapSymmetry C2.flip
    rfl
  have sourceFixed :=
    R.stabilizerRecognition.reflectsMappedStabilizer
      S.movedOrbit C2.flip targetFixed
  exact S.frobeniusMovesRepresentative sourceFixed

/-! ## Frobenius-compatible positive control -/

inductive FrobeniusSheet
  | direct | conjugate
  deriving DecidableEq, Repr, Fintype

def flipSheet : FrobeniusSheet → FrobeniusSheet
  | .direct => .conjugate
  | .conjugate => .direct

theorem flipSheet_involutive (s : FrobeniusSheet) :
    flipSheet (flipSheet s) = s := by
  cases s <;> rfl

abbrev FrobeniusCoverState := P2State × FrobeniusSheet

def coverAct : C2 → FrobeniusCoverState → FrobeniusCoverState
  | .e, s => s
  | .flip, (base, sheet) => (base, flipSheet sheet)

def p2FrobeniusCoverAction : InvertibleAction FrobeniusCoverState C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := coverAct
  identity_act := by intro s; rfl
  combine_act := by
    intro g h s
    cases g <;> cases h
    · rfl
    · rfl
    · rfl
    · rcases s with ⟨base, sheet⟩
      simp [coverAct, flipSheet_involutive]
  inverse_left := by
    intro g s
    cases g
    · rfl
    · rcases s with ⟨base, sheet⟩
      simp [coverAct, c2Inverse, flipSheet_involutive]
  inverse_right := by
    intro g s
    cases g
    · rfl
    · rcases s with ⟨base, sheet⟩
      simp [coverAct, c2Inverse, flipSheet_involutive]

def coverOrbitOf : FrobeniusCoverState → P2State := Prod.fst

def coverRepresentative (o : P2State) : FrobeniusCoverState := (o, .direct)

def p2FrobeniusCoverOrbitPresentation :
    OrbitPresentation p2FrobeniusCoverAction where
  Orbit := P2State
  orbitOf := coverOrbitOf
  representative := coverRepresentative
  orbit_invariant := by
    intro g s
    cases g <;> rcases s with ⟨base, sheet⟩ <;> rfl
  representative_exact := by
    intro o
    rfl

theorem flip_moves_every_cover_state (s : FrobeniusCoverState) :
    p2FrobeniusCoverAction.act .flip s ≠ s := by
  rcases s with ⟨base, sheet⟩
  cases sheet <;> simp [p2FrobeniusCoverAction, coverAct, flipSheet]

theorem cover_state_cardinality :
    Fintype.card FrobeniusCoverState = 20 := by decide

theorem cover_orbit_cardinality :
    Fintype.card p2FrobeniusCoverOrbitPresentation.Orbit = 10 := by
  change Fintype.card P2State = 10
  decide

theorem cover_state_count_is_two_times_orbits :
    Fintype.card FrobeniusCoverState =
      2 * Fintype.card p2FrobeniusCoverOrbitPresentation.Orbit := by
  decide

def forgetFrobeniusSheet : FrobeniusCoverState → P2State := Prod.fst

theorem forget_sheet_collides (base : P2State) :
    forgetFrobeniusSheet (base, .direct) =
      forgetFrobeniusSheet (base, .conjugate) := rfl

theorem forget_sheet_not_injective :
    ¬ Function.Injective forgetFrobeniusSheet := by
  intro h
  have impossible :
      ((StrictSide.lower, NineOrbit.zero), FrobeniusSheet.direct) =
      ((StrictSide.lower, NineOrbit.zero), FrobeniusSheet.conjugate) :=
    h rfl
  cases impossible

inductive ClaimOrigin
  | repositoryNewExtension
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def positiveControlOrigin : ClaimOrigin := .repositoryNewExtension
def arithmeticRecognitionOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  identityOnlyTargetRejectsMovingFrobenius : Bool
  movingC2PositiveControlConstructed : Bool
  positiveControlFineStateCountTwenty : Bool
  positiveControlPi0CountTen : Bool
  forgetfulMapToOldRetainedTargetExists : Bool
  forgetfulMapIsStateEquivalence : Bool
  arithmeticIdentificationClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  identityOnlyTargetRejectsMovingFrobenius := true
  movingC2PositiveControlConstructed := true
  positiveControlFineStateCountTwenty := true
  positiveControlPi0CountTen := true
  forgetfulMapToOldRetainedTargetExists := true
  forgetfulMapIsStateEquivalence := false
  arithmeticIdentificationClaimed := false

end Integration.OggSSPP2FrobeniusRetainedTarget
