import Mathlib

/-!
# Small-characteristic Ogg/SSP recognition mirror

Lean mirror of the live Agda recognition cut:

* p=2 and p=3 each have one coarse supersingular j-class on the authority side;
* the 369 targets carry strictly richer orbit/residual structure;
* coarse-j data alone cannot satisfy full pi0 recognition;
* p=2 retained orientation is exact reopening data, not an optional label;
* a valid arithmetic source must be a marked/enriched cover and must have
  enough orbit capacity to receive the exact target orbit carrier.

This file deliberately does not construct the missing arithmetic p=2/p=3
marked supersingular source.
-/

namespace Integration.OggSSPSmallCharacteristicRecognition

/-! ## Finite 369 target carriers -/

inductive P3Orbit
  | zero
  | nonzero
  deriving DecidableEq, Repr, Fintype

inductive NonzeroOrientation
  | negative
  | positive
  deriving DecidableEq, Repr, Fintype

inductive P3State
  | zero
  | negative
  | positive
  deriving DecidableEq, Repr, Fintype

def p3Project : P3State → P3Orbit
  | .zero => .zero
  | .negative => .nonzero
  | .positive => .nonzero

def P3Residual : P3Orbit → Type
  | .zero => PUnit
  | .nonzero => NonzeroOrientation

def p3Residual : (s : P3State) → P3Residual (p3Project s)
  | .zero => PUnit.unit
  | .negative => .negative
  | .positive => .positive

def p3Reopen : (o : P3Orbit) → P3Residual o → P3State
  | .zero, _ => .zero
  | .nonzero, .negative => .negative
  | .nonzero, .positive => .positive

theorem p3_reopen_exact (s : P3State) :
    p3Reopen (p3Project s) (p3Residual s) = s := by
  cases s <;> rfl

theorem p3_coarse_projection_not_injective :
    ¬ Function.Injective p3Project := by
  intro h
  have := h (show p3Project .negative = p3Project .positive by rfl)
  cases this

theorem p3_coarse_projection_has_no_left_inverse :
    ¬ ∃ recover : P3Orbit → P3State, Function.LeftInverse recover p3Project := by
  rintro ⟨recover, h⟩
  exact p3_coarse_projection_not_injective h.injective

inductive NineOrbit
  | zero
  | firstAxis
  | secondAxis
  | equalSign
  | oppositeSign
  deriving DecidableEq, Repr, Fintype

inductive StrictSide
  | lower
  | upper
  deriving DecidableEq, Repr, Fintype

abbrev P2State := StrictSide × NineOrbit

def p2Project : P2State → NineOrbit := Prod.snd
def p2Residual : P2State → StrictSide := Prod.fst
def p2Reopen (o : NineOrbit) (side : StrictSide) : P2State := (side, o)

theorem p2_reopen_exact (s : P2State) :
    p2Reopen (p2Project s) (p2Residual s) = s := by
  rcases s with ⟨side, orbit⟩
  rfl

theorem p2_coarse_projection_not_injective :
    ¬ Function.Injective p2Project := by
  intro h
  have same :
      p2Project (.lower, NineOrbit.zero) =
      p2Project (.upper, NineOrbit.zero) := rfl
  have impossible := h same
  cases impossible

theorem p2_coarse_projection_has_no_left_inverse :
    ¬ ∃ recover : NineOrbit → P2State, Function.LeftInverse recover p2Project := by
  rintro ⟨recover, h⟩
  exact p2_coarse_projection_not_injective h.injective

theorem p2_target_cardinality : Fintype.card P2State = 10 := by decide
theorem p3_target_orbit_cardinality : Fintype.card P3Orbit = 2 := by decide

/-! ## Exact Ogg lane key surface -/

inductive OggLane
  | p2 | p3 | p5 | p7 | p11 | p13 | p17 | p19 | p23 | p29 | p31 | p41 | p47 | p59 | p71
  deriving DecidableEq, Repr, Fintype

def oggPrime : OggLane → Nat
  | .p2 => 2 | .p3 => 3 | .p5 => 5 | .p7 => 7 | .p11 => 11
  | .p13 => 13 | .p17 => 17 | .p19 => 19 | .p23 => 23 | .p29 => 29
  | .p31 => 31 | .p41 => 41 | .p47 => 47 | .p59 => 59 | .p71 => 71

def oggAddress (lane : OggLane) : Nat × Nat :=
  (oggPrime lane / 9, oggPrime lane % 9)

theorem p2_p3_exact_addresses_distinct :
    oggAddress .p2 ≠ oggAddress .p3 := by decide

/-! ## Coarse supersingular-j no-go -/

/-- The upstream arithmetic authority currently exposes one coarse supersingular
j-class at p=2 and p=3. We mirror only that cardinal fact here. -/
inductive CoarseJ
  | unique
  deriving DecidableEq, Repr, Fintype

theorem coarse_j_cardinality : Fintype.card CoarseJ = 1 := by decide

theorem no_surjection_coarse_j_to_p3_orbits :
    ¬ ∃ f : CoarseJ → P3Orbit, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf P3Orbit.zero
  obtain ⟨b, hb⟩ := hf P3Orbit.nonzero
  cases a
  cases b
  have : P3Orbit.zero = P3Orbit.nonzero := ha.symm.trans hb
  cases this

theorem no_surjection_coarse_j_to_p2_target :
    ¬ ∃ f : CoarseJ → P2State, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf (StrictSide.lower, NineOrbit.zero)
  obtain ⟨b, hb⟩ := hf (StrictSide.upper, NineOrbit.zero)
  cases a
  cases b
  have :
      (StrictSide.lower, NineOrbit.zero) =
      (StrictSide.upper, NineOrbit.zero) := ha.symm.trans hb
  cases this

/-! ## Recognition direction and source-capacity constraint -/

/-- Orbit-level core of the correctly directed arithmetic -> 369 recognition.
Action-equivariance and stabilizer preservation live in the Agda owner; this
Lean surface mirrors the pi0 consequence needed for source-capacity auditing. -/
structure OrbitRecognition (SourceOrbit TargetOrbit : Type) where
  targetToSource : TargetOrbit → SourceOrbit
  sourceToTarget : SourceOrbit → TargetOrbit
  targetRoundTrip : Function.LeftInverse sourceToTarget targetToSource
  sourceRoundTrip : Function.LeftInverse targetToSource sourceToTarget

namespace OrbitRecognition

theorem targetToSource_injective
    {S T : Type} (R : OrbitRecognition S T) :
    Function.Injective R.targetToSource :=
  R.targetRoundTrip.injective

theorem sourceToTarget_surjective
    {S T : Type} (R : OrbitRecognition S T) :
    Function.Surjective R.sourceToTarget :=
  R.targetRoundTrip.surjective

end OrbitRecognition

structure P3MarkedArithmeticSource where
  State : Type
  Orbit : Type
  coarseJ : State → CoarseJ
  coarseJ_constant : ∀ s, coarseJ s = .unique
  frobeniusMovesSomeMarkedState : Prop

structure P2MarkedArithmeticSource where
  State : Type
  Orbit : Type
  coarseJ : State → CoarseJ
  coarseJ_constant : ∀ s, coarseJ s = .unique
  markedResidualStructurePresent : Prop

structure P3ArithmeticTo369Recognition (S : P3MarkedArithmeticSource) where
  orbitRecognition : OrbitRecognition S.Orbit P3Orbit

structure P2ArithmeticTo369Recognition (S : P2MarkedArithmeticSource) where
  orbitRecognition : OrbitRecognition S.Orbit P2State

theorem p3_target_orbits_embed_into_arithmetic_source
    {S : P3MarkedArithmeticSource}
    (R : P3ArithmeticTo369Recognition S) :
    Function.Injective R.orbitRecognition.targetToSource :=
  R.orbitRecognition.targetToSource_injective

theorem p2_ten_target_states_embed_into_arithmetic_source
    {S : P2MarkedArithmeticSource}
    (R : P2ArithmeticTo369Recognition S) :
    Function.Injective R.orbitRecognition.targetToSource :=
  R.orbitRecognition.targetToSource_injective

/-! ## Promotion / attribution firewall -/

inductive ClaimOrigin
  | externalArithmeticAuthority
  | agdaFormalReconstruction
  | leanFormalMirror
  | repositoryCrossModuleInference
  | openRecognitionConjecture
  deriving DecidableEq, Repr

def coarseJFactOrigin : ClaimOrigin := .externalArithmeticAuthority
def codecNoGoOrigin : ClaimOrigin := .agdaFormalReconstruction
def thisMirrorOrigin : ClaimOrigin := .leanFormalMirror
def arithmeticTo369RecognitionOrigin : ClaimOrigin := .openRecognitionConjecture

structure RecognitionBoundary where
  exactCodecTargetsMirrored : Bool
  coarseJNoGoMirrored : Bool
  arithmeticTo369DirectionMirrored : Bool
  targetOrbitEmbeddingConstraintMirrored : Bool
  markedP2ArithmeticSourceInhabited : Bool
  markedP3ArithmeticSourceInhabited : Bool
  p2RecognitionInhabited : Bool
  p3RecognitionInhabited : Bool
  deriving Repr

def canonicalBoundary : RecognitionBoundary where
  exactCodecTargetsMirrored := true
  coarseJNoGoMirrored := true
  arithmeticTo369DirectionMirrored := true
  targetOrbitEmbeddingConstraintMirrored := true
  markedP2ArithmeticSourceInhabited := false
  markedP3ArithmeticSourceInhabited := false
  p2RecognitionInhabited := false
  p3RecognitionInhabited := false

end Integration.OggSSPSmallCharacteristicRecognition
