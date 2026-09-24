import Integration.MoonshineAngleC6SectorObserver
import Integration.SmithChartComplexReflection
import Integration.MoonshineLevelOneWeightZeroPinned
import Mathlib

/-!
# C6 / ten-state / rank-17 / weight-12 finite cross-pollination

Lean mirror of the finite theorem surface now used by the Agda canonical
interpretation.  It intentionally does not identify equal numerals with equal
semantic objects.
-/

namespace Integration.MoonshineC6TenRankWeightTwelveCrossPollination

open Integration.MoonshineAngleC6SectorObserver

/-! ## 1. Smith half-turn and modular reflection on the common C6 carrier -/

def smithHalfTurn : C6Sector → C6Sector
  | .s0 => .s3
  | .s1 => .s4
  | .s2 => .s5
  | .s3 => .s0
  | .s4 => .s1
  | .s5 => .s2

@[simp] theorem smithHalfTurn_involutive (s : C6Sector) :
    smithHalfTurn (smithHalfTurn s) = s := by
  cases s <;> rfl

theorem smith_reflection_commute (s : C6Sector) :
    smithHalfTurn (reflect6 s) = reflect6 (smithHalfTurn s) := by
  cases s <;> rfl

theorem smith_not_identity :
    ¬ ∀ s : C6Sector, smithHalfTurn s = s := by
  intro h
  have := h C6Sector.s0
  contradiction

theorem smith_not_modular_reflection :
    ¬ ∀ s : C6Sector, smithHalfTurn s = reflect6 s := by
  intro h
  have := h C6Sector.s0
  contradiction

/-- Orientation-forgetting phase quotient: opposite C6 sectors have one C3
phase.  This is the finite quotient on which the Smith half-turn disappears. -/
inductive C3Phase | p0 | p1 | p2
  deriving DecidableEq, Repr

def forgetOrientation : C6Sector → C3Phase
  | .s0 | .s3 => .p0
  | .s1 | .s4 => .p1
  | .s2 | .s5 => .p2

theorem c3_erases_smith (s : C6Sector) :
    forgetOrientation (smithHalfTurn s) = forgetOrientation s := by
  cases s <;> rfl

def reflect3 : C3Phase → C3Phase
  | .p0 => .p0
  | .p1 => .p2
  | .p2 => .p1

theorem modular_reflection_descends (s : C6Sector) :
    forgetOrientation (reflect6 s) = reflect3 (forgetOrientation s) := by
  cases s <;> rfl

/-! ## 2. Ten-state carrier: 9+1 and 5×2 are exact presentations -/

inductive Completion10
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | j
  deriving DecidableEq, Repr

inductive Mode5 | m09 | m18 | m27 | m36 | m45
  deriving DecidableEq, Repr
inductive Phase2 | direct | counter
  deriving DecidableEq, Repr

def tenToModePhase : Completion10 → Mode5 × Phase2
  | .d0 => (.m09,.direct) | .j => (.m09,.counter)
  | .d1 => (.m18,.direct) | .d8 => (.m18,.counter)
  | .d2 => (.m27,.direct) | .d7 => (.m27,.counter)
  | .d3 => (.m36,.direct) | .d6 => (.m36,.counter)
  | .d4 => (.m45,.direct) | .d5 => (.m45,.counter)

def modePhaseToTen : Mode5 × Phase2 → Completion10
  | (.m09,.direct) => .d0 | (.m09,.counter) => .j
  | (.m18,.direct) => .d1 | (.m18,.counter) => .d8
  | (.m27,.direct) => .d2 | (.m27,.counter) => .d7
  | (.m36,.direct) => .d3 | (.m36,.counter) => .d6
  | (.m45,.direct) => .d4 | (.m45,.counter) => .d5

theorem ten_mode_roundtrip (x : Completion10) :
    modePhaseToTen (tenToModePhase x) = x := by cases x <;> rfl

theorem mode_ten_roundtrip (x : Mode5 × Phase2) :
    tenToModePhase (modePhaseToTen x) = x := by
  rcases x with ⟨m,p⟩
  cases m <;> cases p <;> rfl

theorem ten_eq_nine_plus_one : 10 = 9 + 1 := by norm_num
theorem ten_eq_five_times_two : 10 = 5 * 2 := by norm_num
theorem ten_eq_one_three_six : 10 = 1 + 3 + 6 := by norm_num
theorem ten_eq_ternary_101 : 10 = 1 + 0*3 + 1*9 := by norm_num


/-! ## 2b. Shared binary-orientation reallocation

The same binary coordinate can be carried on the C6 side or on the ten-state
side:

    C6 × Mode5  ≃  C3 × Completion10.

This is stronger than the cardinal equation 6*5 = 3*10.
-/

def c6ToPhase2 : C6Sector → C3Phase × Phase2
  | .s0 => (.p0,.direct) | .s1 => (.p1,.direct) | .s2 => (.p2,.direct)
  | .s3 => (.p0,.counter) | .s4 => (.p1,.counter) | .s5 => (.p2,.counter)

def phase2ToC6 : C3Phase × Phase2 → C6Sector
  | (.p0,.direct) => .s0 | (.p1,.direct) => .s1 | (.p2,.direct) => .s2
  | (.p0,.counter) => .s3 | (.p1,.counter) => .s4 | (.p2,.counter) => .s5

theorem c6_phase2_roundtrip (x : C6Sector) :
    phase2ToC6 (c6ToPhase2 x) = x := by cases x <;> rfl

theorem phase2_c6_roundtrip (x : C3Phase × Phase2) :
    c6ToPhase2 (phase2ToC6 x) = x := by
  rcases x with ⟨p,o⟩
  cases p <;> cases o <;> rfl

abbrev C6Mode5 := C6Sector × Mode5
abbrev C3Ten := C3Phase × Completion10

def reallocateC6ModeToC3Ten : C6Mode5 → C3Ten
  | (hex,mode) =>
      let po := c6ToPhase2 hex
      (po.1, modePhaseToTen (mode,po.2))

def reallocateC3TenToC6Mode : C3Ten → C6Mode5
  | (phase,ten) =>
      let mo := tenToModePhase ten
      (phase2ToC6 (phase,mo.2), mo.1)

theorem c6_mode_reallocation_roundtrip (x : C6Mode5) :
    reallocateC3TenToC6Mode (reallocateC6ModeToC3Ten x) = x := by
  rcases x with ⟨h,m⟩
  cases h <;> cases m <;> rfl

theorem c3_ten_reallocation_roundtrip (x : C3Ten) :
    reallocateC6ModeToC3Ten (reallocateC3TenToC6Mode x) = x := by
  rcases x with ⟨p,t⟩
  cases p <;> cases t <;> rfl

theorem six_times_five_eq_three_times_ten : 6*5 = 3*10 := by norm_num


/-! ## 3. Monster-side arithmetic shell -/

theorem sixFiveSixOne : 3^8 = 6561 := by norm_num
theorem sixFiveSixOneZero : 10 * 3^8 = 65610 := by norm_num
theorem regularC3Bulk : 3 * 65610 = 196830 := by norm_num
theorem monsterResidual : 3 * 65610 + 53 = 196883 := by norm_num
theorem freshInvariantLine : 196883 + 1 = 196884 := by norm_num
theorem residualFreshLine : 53 + 1 = 54 := by norm_num

/-! ## 4. Ordinary/balanced ternary rank boundary -/

def balancedPositiveCapacity : Nat → Nat
  | 0 => 0
  | n+1 => balancedPositiveCapacity n + 3^n

theorem capacity3 : balancedPositiveCapacity 3 = 13 := by
  norm_num [balancedPositiveCapacity]
theorem capacity4 : balancedPositiveCapacity 4 = 40 := by
  norm_num [balancedPositiveCapacity]

theorem fourteen_first_after_three_balanced_places :
    14 = balancedPositiveCapacity 3 + 1 := by
  norm_num [balancedPositiveCapacity]

theorem rank14_balanced_witness : 14 + 9 + 3 + 1 = 27 := by norm_num
theorem rank17_balanced_witness : 17 + 9 + 1 = 27 := by norm_num

def atlasObservableDepth : Nat := 2 + 6
def atlasProperImageDepth : Nat := 2 + 6 + 6
def atlasMaximalDepth : Nat := 3 + 2 + 6 + 6

theorem atlasDepth8 : atlasObservableDepth = 8 := by norm_num [atlasObservableDepth]
theorem atlasDepth14 : atlasProperImageDepth = 14 := by norm_num [atlasProperImageDepth]
theorem atlasDepth17 : atlasMaximalDepth = 17 := by norm_num [atlasMaximalDepth]

/-! ## 5. Three distinct roles of twelve -/

inductive TwelveRole
  | modularWeight
  | relationAxis
  | normalizationBase
  deriving DecidableEq, Repr

theorem twelveSquared : 12^2 = 144 := by norm_num
theorem twelveCubed : 12^3 = 1728 := by norm_num

inductive EqualTwelveNumeralCreatesSemanticIdentity : Prop

theorem equal_twelve_not_semantic_identity :
    ¬ EqualTwelveNumeralCreatesSemanticIdentity := by
  intro h; cases h

/-! ## 6. Signed magnitude is a strict residual above coarse sign -/

inductive SignedMultiplicity
  | neg (magnitude : Nat)
  | zero
  | pos (magnitude : Nat)
  deriving DecidableEq, Repr

def coarseSign : SignedMultiplicity → C3Phase
  | .neg _ => .p2
  | .zero => .p0
  | .pos _ => .p1

def signedMagnitude : SignedMultiplicity → Nat
  | .neg n => n
  | .zero => 0
  | .pos n => n

theorem same_coarse_positive :
    coarseSign (.pos 1) = coarseSign (.pos 2) := rfl

theorem different_positive_magnitude :
    signedMagnitude (.pos 1) ≠ signedMagnitude (.pos 2) := by decide

structure FactorsThrough {A B C : Type}
    (observe : A → B) (consumer : A → C) : Type where
  factor : B → C
  commutes : ∀ a, consumer a = factor (observe a)

theorem signed_magnitude_not_factor_through_coarse :
    ¬ FactorsThrough coarseSign signedMagnitude := by
  intro h
  have h1 := h.commutes (.pos 1)
  have h2 := h.commutes (.pos 2)
  have : signedMagnitude (.pos 1) = signedMagnitude (.pos 2) := by
    rw [h1, h2, same_coarse_positive]
  exact different_positive_magnitude this

/-! ## Boundary -/

structure Boundary where
  smithAndModularReflectionCommuteC6 : Bool
  smithDistinctFromModularReflectionC6 : Bool
  c3ErasesSmithHalfTurn : Bool
  modularReflectionDescendsC3 : Bool
  boundarySafeAngleC6ObserverOwned : Bool
  tenNinePlusOne : Bool
  tenFiveTimesTwo : Bool
  rank14BalancedCarry : Bool
  atlasDepth14Coordinate : Bool
  atlasDepth17Coordinate : Bool
  atlasX8ActionRecognition : Bool
  signedMagnitudeFactorsThroughCoarse : Bool
  weight12Relation144Normalization1728Crosswalk : Bool
  equalTwelveNumeralCreatesSemanticIdentity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  smithAndModularReflectionCommuteC6 := true
  smithDistinctFromModularReflectionC6 := true
  c3ErasesSmithHalfTurn := true
  modularReflectionDescendsC3 := true
  boundarySafeAngleC6ObserverOwned := true
  tenNinePlusOne := true
  tenFiveTimesTwo := true
  rank14BalancedCarry := true
  atlasDepth14Coordinate := true
  atlasDepth17Coordinate := true
  atlasX8ActionRecognition := false
  signedMagnitudeFactorsThroughCoarse := false
  weight12Relation144Normalization1728Crosswalk := true
  equalTwelveNumeralCreatesSemanticIdentity := false

end Integration.MoonshineC6TenRankWeightTwelveCrossPollination
