import Integration.OggSSP2BActualFiveSlices

/-!
# Actual selected ten Tate generators as five modes x binary orientation

The current weight-two source gives 276 actual A-copy Hhat0 classes.  The
existing selected-ten construction chooses ten of those classes.  This file
changes only the *presentation* of those ten selected coordinates:

  TenState  <->  Mode5 x BinaryPhase.

The five-mode defect vector (3,3,2,1,1) is a separate function on Mode5.
It is NOT used as a vector-space dimension decomposition of the selected
ten-dimensional F2 module.

This mirrors the already-existing Agda Completion10 ~= Mode5 x BinaryPhase
ontology while keeping the Monster-specific source boundary explicit.
-/

namespace Integration.OggSSP2BFiveByTwoDefectArchitecture

inductive Mode5
  | mode09 | mode18 | mode27 | mode36 | mode45
  deriving DecidableEq, Repr, Fintype

inductive BinaryPhase
  | direct | counter
  deriving DecidableEq, Repr, Fintype

inductive TenState
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | j9
  deriving DecidableEq, Repr, Fintype

def encode : TenState → Mode5 × BinaryPhase
  | .d0 => (.mode09, .direct)
  | .j9 => (.mode09, .counter)
  | .d1 => (.mode18, .direct)
  | .d8 => (.mode18, .counter)
  | .d2 => (.mode27, .direct)
  | .d7 => (.mode27, .counter)
  | .d3 => (.mode36, .direct)
  | .d6 => (.mode36, .counter)
  | .d4 => (.mode45, .direct)
  | .d5 => (.mode45, .counter)

def decode : Mode5 × BinaryPhase → TenState
  | (.mode09, .direct) => .d0
  | (.mode09, .counter) => .j9
  | (.mode18, .direct) => .d1
  | (.mode18, .counter) => .d8
  | (.mode27, .direct) => .d2
  | (.mode27, .counter) => .d7
  | (.mode36, .direct) => .d3
  | (.mode36, .counter) => .d6
  | (.mode45, .direct) => .d4
  | (.mode45, .counter) => .d5

theorem decode_encode (x : TenState) : decode (encode x) = x := by
  cases x <;> rfl

theorem encode_decode (x : Mode5 × BinaryPhase) : encode (decode x) = x := by
  rcases x with ⟨m,p⟩
  cases m <;> cases p <;> rfl

def tenEquivFiveByTwo : TenState ≃ Mode5 × BinaryPhase where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem ten_state_count : Fintype.card TenState = 10 := by
  decide

theorem five_mode_count : Fintype.card Mode5 = 5 := by
  decide

theorem binary_phase_count : Fintype.card BinaryPhase = 2 := by
  decide

theorem ten_is_five_times_two :
    Fintype.card TenState =
      Fintype.card Mode5 * Fintype.card BinaryPhase := by
  decide

def flipPhase : BinaryPhase → BinaryPhase
  | .direct => .counter
  | .counter => .direct

def complement : TenState → TenState :=
  fun x => decode (encode x |>.1, flipPhase (encode x |>.2))

theorem complement_preserves_mode (x : TenState) :
    (encode (complement x)).1 = (encode x).1 := by
  cases x <;> rfl

theorem complement_flips_phase (x : TenState) :
    (encode (complement x)).2 = flipPhase (encode x).2 := by
  cases x <;> rfl

theorem complement_involutive (x : TenState) :
    complement (complement x) = x := by
  cases x <;> rfl

/-- Independent binary-tetrahedral/local-inertia defect depth. -/
def defectDepth : Mode5 → ℕ
  | .mode09 => 3
  | .mode18 => 3
  | .mode27 => 2
  | .mode36 => 1
  | .mode45 => 1

theorem defect_profile :
    (defectDepth .mode09,
      defectDepth .mode18,
      defectDepth .mode27,
      defectDepth .mode36,
      defectDepth .mode45) = (3,3,2,1,1) := by
  rfl

theorem defect_sum_is_ten :
    defectDepth .mode09 +
    defectDepth .mode18 +
    defectDepth .mode27 +
    defectDepth .mode36 +
    defectDepth .mode45 = 10 := by
  decide

/-- Every mode has exactly two oriented states, independently of its defect. -/
def statesAtMode (m : Mode5) : Finset TenState :=
  Finset.univ.filter (fun x => (encode x).1 = m)

theorem every_mode_has_two_orientations (m : Mode5) :
    (statesAtMode m).card = 2 := by
  cases m <;> native_decide

/-- This is the crucial typing correction: defect depth is not generally
the number of selected binary-orientation states over a mode. -/
theorem defect_is_not_fibre_cardinality_at_mode09 :
    defectDepth .mode09 ≠ (statesAtMode .mode09).card := by
  native_decide

theorem defect_is_not_fibre_cardinality_at_mode18 :
    defectDepth .mode18 ≠ (statesAtMode .mode18).card := by
  native_decide

theorem defect_is_not_fibre_cardinality_at_mode36 :
    defectDepth .mode36 ≠ (statesAtMode .mode36).card := by
  native_decide

theorem defect_is_not_fibre_cardinality_at_mode45 :
    defectDepth .mode45 ≠ (statesAtMode .mode45).card := by
  native_decide

/-- The selected ten actual A-copy Tate classes may be presented as one binary
coordinate over each of five modes.  This is still a selected submodule of the
276-dimensional source space; no source theorem here declares which ten A-copy
indices are canonical. -/
abbrev SelectedTenActualTateModule := TenState → ZMod 2
abbrev FiveByTwoActualTatePresentation := (Mode5 × BinaryPhase) → ZMod 2

def selectedTenToFiveByTwo
    (v : SelectedTenActualTateModule) :
    FiveByTwoActualTatePresentation :=
  fun mp => v (decode mp)

def fiveByTwoToSelectedTen
    (v : FiveByTwoActualTatePresentation) :
    SelectedTenActualTateModule :=
  fun s => v (encode s)

theorem selectedTen_roundTrip
    (v : SelectedTenActualTateModule) :
    fiveByTwoToSelectedTen (selectedTenToFiveByTwo v) = v := by
  funext s
  simp [fiveByTwoToSelectedTen, selectedTenToFiveByTwo, decode_encode]

theorem fiveByTwo_roundTrip
    (v : FiveByTwoActualTatePresentation) :
    selectedTenToFiveByTwo (fiveByTwoToSelectedTen v) = v := by
  funext mp
  simp [fiveByTwoToSelectedTen, selectedTenToFiveByTwo, encode_decode]

end Integration.OggSSP2BFiveByTwoDefectArchitecture
