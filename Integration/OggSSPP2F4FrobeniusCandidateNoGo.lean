import Mathlib
import Integration.ActionOrbitRecognition
import Integration.OggSSPSmallCharacteristicRecognition

/-!
# p=2 F4/F2 Frobenius candidate: negative control

Lean mirror of the live Agda finite negative-control lane.

The raw four-point F4-shaped carrier has Frobenius orbit structure

  {0}, {1}, {alpha, alpha+1}

so it has three connected components.  The retained p=2 target has ten
components.  Therefore raw F4 cannot fully recognize that target.

Further, no uniform k-sheet refinement of all three raw orbit classes can have
exactly ten components, since 3*k != 10 for every natural k.  Any refinement
that closes at ten while retaining the F4 orbit stratification must therefore
be nonuniform/stratified (or change the base orbit semantics).
-/

namespace Integration.OggSSPP2F4FrobeniusCandidateNoGo

open Integration.ActionOrbitRecognition
open Integration.OggSSPSmallCharacteristicRecognition

inductive F4Point
  | zero | one | alpha | alphaPlusOne
  deriving DecidableEq, Repr, Fintype

def frobenius2 : F4Point → F4Point
  | .zero => .zero
  | .one => .one
  | .alpha => .alphaPlusOne
  | .alphaPlusOne => .alpha

theorem frobenius2_involutive (x : F4Point) :
    frobenius2 (frobenius2 x) = x := by
  cases x <;> rfl

def f4Act : C2 → F4Point → F4Point
  | .e, x => x
  | .flip, x => frobenius2 x

def f4FrobeniusAction : InvertibleAction F4Point C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := f4Act
  identity_act := by intro x; rfl
  combine_act := by
    intro g h x
    cases g <;> cases h
    · rfl
    · rfl
    · rfl
    · simpa [f4Act] using frobenius2_involutive x
  inverse_left := by
    intro g x
    cases g
    · rfl
    · simpa [f4Act, c2Inverse] using frobenius2_involutive x
  inverse_right := by
    intro g x
    cases g
    · rfl
    · simpa [f4Act, c2Inverse] using frobenius2_involutive x

inductive F4Orbit
  | zeroFixed | oneFixed | conjugatePair
  deriving DecidableEq, Repr, Fintype

def classifyF4 : F4Point → F4Orbit
  | .zero => .zeroFixed
  | .one => .oneFixed
  | .alpha => .conjugatePair
  | .alphaPlusOne => .conjugatePair

def representativeF4 : F4Orbit → F4Point
  | .zeroFixed => .zero
  | .oneFixed => .one
  | .conjugatePair => .alpha

def f4OrbitPresentation : OrbitPresentation f4FrobeniusAction where
  Orbit := F4Orbit
  orbitOf := classifyF4
  representative := representativeF4
  orbit_invariant := by
    intro g x
    cases g <;> cases x <;> rfl
  representative_exact := by
    intro o
    cases o <;> rfl

theorem f4_point_cardinality : Fintype.card F4Point = 4 := by decide
theorem f4_orbit_cardinality : Fintype.card F4Orbit = 3 := by decide

theorem p2_retained_target_cardinality : Fintype.card P2State = 10 := by decide

theorem no_injective_p2_target_into_f4_orbits :
    ¬ ∃ f : P2State → F4Orbit, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle : Fintype.card P2State ≤ Fintype.card F4Orbit :=
    Fintype.card_le_of_injective f hf
  omega

theorem no_full_f4_frobenius_recognition_to_p2
    (F : ActionRecognitionFunctor f4FrobeniusAction p2DiscreteAction) :
    ¬ Nonempty (FullRecognition F f4OrbitPresentation p2DiscreteOrbitPresentation) := by
  rintro ⟨R⟩
  have hinj : Function.Injective
      (R.pi0Surjection.preimageOrbit : P2State → F4Orbit) :=
    R.targetOrbit_to_source_injective
  exact no_injective_p2_target_into_f4_orbits
    ⟨R.pi0Surjection.preimageOrbit, hinj⟩

def uniformMarkedOrbitCount (k : Nat) : Nat := 3 * k

theorem no_uniform_three_orbit_lift_to_ten :
    ¬ ∃ k : Nat, uniformMarkedOrbitCount k = 10 := by
  rintro ⟨k, hk⟩
  simp [uniformMarkedOrbitCount] at hk
  omega

inductive ClaimOrigin
  | externalCalibration
  | repositoryFormalReconstruction
  | leanFormalMirror
  | openMarkedArithmeticRecognition
  deriving DecidableEq, Repr

def thisLaneOrigin : ClaimOrigin := .leanFormalMirror
def markedRecognitionOrigin : ClaimOrigin := .openMarkedArithmeticRecognition

structure Boundary where
  literalFourPointCarrierConstructed : Bool
  literalOrderTwoFrobeniusActionConstructed : Bool
  exactThreeOrbitPresentationConstructed : Bool
  rawF4CannotFullyRecognizeTenStateTarget : Bool
  uniformThreeOrbitLiftRuledOut : Bool
  stratifiedMarkedRefinementRequiredIfRefiningF4Orbits : Bool
  actualMarkedCMCarrierConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalFourPointCarrierConstructed := true
  literalOrderTwoFrobeniusActionConstructed := true
  exactThreeOrbitPresentationConstructed := true
  rawF4CannotFullyRecognizeTenStateTarget := true
  uniformThreeOrbitLiftRuledOut := true
  stratifiedMarkedRefinementRequiredIfRefiningF4Orbits := true
  actualMarkedCMCarrierConstructed := false

end Integration.OggSSPP2F4FrobeniusCandidateNoGo
