import Integration.TwistronicsRelativeRegistrationComparator
import Mathlib
import Integration.ActionOrbitRecognition

/-!
# Small-characteristic Ogg/SSP recognition mirror

Lean mirror of the live Agda recognition cut.  The target carriers/codecs and
recognition consequences are proved here.  The missing arithmetic marked
supersingular source remains an explicit structure parameter; no inhabitant is
manufactured from authority metadata.
-/

namespace Integration.OggSSPSmallCharacteristicRecognition

open Integration.ActionOrbitRecognition

/-! ## Exact finite target codecs -/

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
  have impossible : P3State.negative = P3State.positive :=
    h (show p3Project .negative = p3Project .positive by rfl)
  cases impossible

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
  have impossible :
      (StrictSide.lower, NineOrbit.zero) =
      (StrictSide.upper, NineOrbit.zero) :=
    h (show
      p2Project (.lower, NineOrbit.zero) =
      p2Project (.upper, NineOrbit.zero) by rfl)
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

/-! ## Target actions and orbit presentations -/

inductive C2
  | e
  | flip
  deriving DecidableEq, Repr, Fintype

def c2Combine : C2 → C2 → C2
  | .e, g => g
  | g, .e => g
  | .flip, .flip => .e

def c2Inverse : C2 → C2 := id

def p3Act : C2 → P3State → P3State
  | .e, s => s
  | .flip, .zero => .zero
  | .flip, .negative => .positive
  | .flip, .positive => .negative

def p3Action : InvertibleAction P3State C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := p3Act
  identity_act := by intro s; cases s <;> rfl
  combine_act := by intro g h s; cases g <;> cases h <;> cases s <;> rfl
  inverse_left := by intro g s; cases g <;> cases s <;> rfl
  inverse_right := by intro g s; cases g <;> cases s <;> rfl

def p3OrbitPresentation : OrbitPresentation p3Action where
  Orbit := P3Orbit
  orbitOf := p3Project
  representative
    | .zero => .zero
    | .nonzero => .positive
  orbit_invariant := by
    intro g s
    cases g <;> cases s <;> rfl
  representative_exact := by
    intro o
    cases o <;> rfl

theorem p3_flip_fixes_zero :
    p3Action.act .flip P3State.zero = P3State.zero := rfl

theorem p3_flip_moves_nonzero_representative :
    p3Action.act .flip
      (p3OrbitPresentation.representative .nonzero) ≠
      p3OrbitPresentation.representative .nonzero := by
  decide

/-! ## Literal F9/F3 Frobenius candidate: negative control -/

inductive F3
  | z | o | t
  deriving DecidableEq, Repr, Fintype

def neg3 : F3 → F3
  | .z => .z
  | .o => .t
  | .t => .o

theorem neg3_involutive (x : F3) : neg3 (neg3 x) = x := by
  cases x <;> rfl

abbrev F9Point := F3 × F3

def frobenius3 : F9Point → F9Point
  | (a, b) => (a, neg3 b)

theorem frobenius3_involutive (x : F9Point) :
    frobenius3 (frobenius3 x) = x := by
  rcases x with ⟨a, b⟩
  simp [frobenius3, neg3_involutive]

def f9Act : C2 → F9Point → F9Point
  | .e, x => x
  | .flip, x => frobenius3 x

def f9FrobeniusAction : InvertibleAction F9Point C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := f9Act
  identity_act := by intro x; rfl
  combine_act := by
    intro g h x
    cases g <;> cases h
    · rfl
    · rfl
    · rfl
    · simpa [f9Act] using frobenius3_involutive x
  inverse_left := by
    intro g x
    cases g
    · rfl
    · simpa [f9Act, c2Inverse] using frobenius3_involutive x
  inverse_right := by
    intro g x
    cases g
    · rfl
    · simpa [f9Act, c2Inverse] using frobenius3_involutive x

inductive F9Orbit
  | fixed0 | fixed1 | fixed2
  | pair0 | pair1 | pair2
  deriving DecidableEq, Repr, Fintype

def classifyF9 : F9Point → F9Orbit
  | (.z, .z) => .fixed0
  | (.o, .z) => .fixed1
  | (.t, .z) => .fixed2
  | (.z, .o) => .pair0
  | (.z, .t) => .pair0
  | (.o, .o) => .pair1
  | (.o, .t) => .pair1
  | (.t, .o) => .pair2
  | (.t, .t) => .pair2

def representativeF9 : F9Orbit → F9Point
  | .fixed0 => (.z, .z)
  | .fixed1 => (.o, .z)
  | .fixed2 => (.t, .z)
  | .pair0 => (.z, .o)
  | .pair1 => (.o, .o)
  | .pair2 => (.t, .o)

def f9OrbitPresentation : OrbitPresentation f9FrobeniusAction where
  Orbit := F9Orbit
  orbitOf := classifyF9
  representative := representativeF9
  orbit_invariant := by
    intro g x
    cases g <;> rcases x with ⟨a, b⟩ <;>
      cases a <;> cases b <;> rfl
  representative_exact := by
    intro o
    cases o <;> rfl

theorem f9_orbit_cardinality : Fintype.card F9Orbit = 6 := by decide

def extensionCoordinate : F9Point → P3State
  | (_, .z) => .zero
  | (_, .o) => .positive
  | (_, .t) => .negative

def extensionCoordinateSection : P3State → F9Point
  | .zero => (.z, .z)
  | .positive => (.z, .o)
  | .negative => (.z, .t)

theorem extensionCoordinate_surjective :
    Function.Surjective extensionCoordinate := by
  intro s
  refine ⟨extensionCoordinateSection s, ?_⟩
  cases s <;> rfl

theorem extensionCoordinate_equivariant (g : C2) (x : F9Point) :
    extensionCoordinate (f9Act g x) =
      p3Act g (extensionCoordinate x) := by
  cases g <;> rcases x with ⟨a, b⟩ <;>
    cases a <;> cases b <;> rfl

def f9ExtensionCoordinateFunctor :
    ActionRecognitionFunctor f9FrobeniusAction p3Action where
  mapState := extensionCoordinate
  mapSymmetry := id
  preservesIdentity := rfl
  preservesCombine := by intro g h; rfl
  preservesInverse := by intro g; rfl
  actionEquivariant := extensionCoordinate_equivariant

def f9OrbitToP3Orbit : F9Orbit → P3Orbit
  | .fixed0 => .zero
  | .fixed1 => .zero
  | .fixed2 => .zero
  | .pair0 => .nonzero
  | .pair1 => .nonzero
  | .pair2 => .nonzero

theorem f9_orbit_map_exact (x : F9Point) :
    p3OrbitPresentation.orbitOf
      (f9ExtensionCoordinateFunctor.mapState x) =
    f9OrbitToP3Orbit (f9OrbitPresentation.orbitOf x) := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> rfl

def f9ExtensionCoordinateOrbitRecognition :
    OrbitRecognition
      f9ExtensionCoordinateFunctor
      f9OrbitPresentation
      p3OrbitPresentation where
  mapOrbit := f9OrbitToP3Orbit
  orbitMapExact := f9_orbit_map_exact

theorem f9_extension_coordinate_not_pi0_embedding :
    ¬ Nonempty (Pi0Embedding f9ExtensionCoordinateOrbitRecognition) := by
  rintro ⟨h⟩
  have impossible : F9Orbit.fixed0 = F9Orbit.fixed1 :=
    h.reflectsOrbitEquality (show
      f9OrbitToP3Orbit .fixed0 = f9OrbitToP3Orbit .fixed1 by rfl)
  cases impossible

theorem no_injective_f9_orbits_to_p3_target :
    ¬ ∃ f : F9Orbit → P3Orbit, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle :
      Fintype.card F9Orbit ≤ Fintype.card P3Orbit :=
    Fintype.card_le_of_injective f hf
  have h6 : Fintype.card F9Orbit = 6 := by decide
  have h2 : Fintype.card P3Orbit = 2 := by decide
  omega

theorem no_full_f9_frobenius_recognition_to_p3
    (F : ActionRecognitionFunctor f9FrobeniusAction p3Action) :
    ¬ Nonempty (FullRecognition F f9OrbitPresentation p3OrbitPresentation) := by
  rintro ⟨R⟩
  have hinj : Function.Injective R.orbitRecognition.mapOrbit :=
    fun _ _ h => R.pi0Embedding.reflectsOrbitEquality h
  exact no_injective_f9_orbits_to_p3_target
    ⟨R.orbitRecognition.mapOrbit, hinj⟩

def p2DiscreteAction : InvertibleAction P2State PUnit where
  identity := PUnit.unit
  combine := fun _ _ => PUnit.unit
  inverse := fun _ => PUnit.unit
  act := fun _ s => s
  identity_act := by intro s; rfl
  combine_act := by intro _ _ s; rfl
  inverse_left := by intro _ s; rfl
  inverse_right := by intro _ s; rfl

def p2DiscreteOrbitPresentation : OrbitPresentation p2DiscreteAction where
  Orbit := P2State
  orbitOf := id
  representative := id
  orbit_invariant := by intro _ s; rfl
  representative_exact := by intro o; rfl

/-! ## Coarse supersingular-j no-go -/

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
  have impossible : P3Orbit.zero = P3Orbit.nonzero := ha.symm.trans hb
  cases impossible

theorem no_surjection_coarse_j_to_p2_target :
    ¬ ∃ f : CoarseJ → P2State, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf (StrictSide.lower, NineOrbit.zero)
  obtain ⟨b, hb⟩ := hf (StrictSide.upper, NineOrbit.zero)
  cases a
  cases b
  have impossible :
      (StrictSide.lower, NineOrbit.zero) =
      (StrictSide.upper, NineOrbit.zero) := ha.symm.trans hb
  cases impossible

/-! ## Marked arithmetic source sockets -/

structure P3MarkedArithmeticSource where
  State : Type
  action : InvertibleAction State C2
  orbits : OrbitPresentation action
  coarseJ : State → CoarseJ
  coarseJ_constant : ∀ s, coarseJ s = .unique
  markedWitness : State
  frobeniusMovesMarkedWitness :
    action.act C2.flip markedWitness ≠ markedWitness
  flipIsArithmeticFrobenius : Prop

structure P2MarkedArithmeticSource where
  State : Type
  Symmetry : Type
  action : InvertibleAction State Symmetry
  orbits : OrbitPresentation action
  coarseJ : State → CoarseJ
  coarseJ_constant : ∀ s, coarseJ s = .unique
  markedResidualStructurePresent : Prop

/-! ## Correctly directed arithmetic -> 369 recognition -/

structure P3ArithmeticTo369Recognition (S : P3MarkedArithmeticSource) where
  functor : ActionRecognitionFunctor S.action p3Action
  fullRecognition :
    FullRecognition functor S.orbits p3OrbitPresentation

structure P2ArithmeticTo369Recognition (S : P2MarkedArithmeticSource) where
  functor : ActionRecognitionFunctor S.action p2DiscreteAction
  fullRecognition :
    FullRecognition functor S.orbits p2DiscreteOrbitPresentation

def p3TargetOrbitToArithmeticOrbit
    {S : P3MarkedArithmeticSource}
    (R : P3ArithmeticTo369Recognition S) :
    P3Orbit → S.orbits.Orbit :=
  R.fullRecognition.pi0Surjection.preimageOrbit

def p2TargetStateToArithmeticOrbit
    {S : P2MarkedArithmeticSource}
    (R : P2ArithmeticTo369Recognition S) :
    P2State → S.orbits.Orbit :=
  R.fullRecognition.pi0Surjection.preimageOrbit

theorem p3_target_orbits_embed_into_arithmetic_source
    {S : P3MarkedArithmeticSource}
    (R : P3ArithmeticTo369Recognition S) :
    Function.Injective (p3TargetOrbitToArithmeticOrbit R) :=
  R.fullRecognition.targetOrbit_to_source_injective

theorem p2_ten_target_states_embed_into_arithmetic_source
    {S : P2MarkedArithmeticSource}
    (R : P2ArithmeticTo369Recognition S) :
    Function.Injective (p2TargetStateToArithmeticOrbit R) :=
  R.fullRecognition.targetOrbit_to_source_injective

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
  targetActionsMirrored : Bool
  orbitStabilizerRecognitionCoreReused : Bool
  coarseJNoGoMirrored : Bool
  f9FrobeniusSixOrbitNoGoMirrored : Bool
  f9FullRecognitionNoGoMirrored : Bool
  f9ExtensionCoordinateQuotientMirrored : Bool
  f9ExtensionCoordinateFailsPi0EmbeddingMirrored : Bool
  arithmeticTo369DirectionMirrored : Bool
  targetOrbitEmbeddingConstraintMirrored : Bool
  markedP2ArithmeticSourceInhabited : Bool
  markedP3ArithmeticSourceInhabited : Bool
  p2RecognitionInhabited : Bool
  p3RecognitionInhabited : Bool
  deriving Repr

def canonicalBoundary : RecognitionBoundary where
  exactCodecTargetsMirrored := true
  targetActionsMirrored := true
  orbitStabilizerRecognitionCoreReused := true
  coarseJNoGoMirrored := true
  f9FrobeniusSixOrbitNoGoMirrored := true
  f9FullRecognitionNoGoMirrored := true
  f9ExtensionCoordinateQuotientMirrored := true
  f9ExtensionCoordinateFailsPi0EmbeddingMirrored := true
  arithmeticTo369DirectionMirrored := true
  targetOrbitEmbeddingConstraintMirrored := true
  markedP2ArithmeticSourceInhabited := false
  markedP3ArithmeticSourceInhabited := false
  p2RecognitionInhabited := false
  p3RecognitionInhabited := false

end Integration.OggSSPSmallCharacteristicRecognition
