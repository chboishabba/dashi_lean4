import Integration.OggSSP369RootRefinementBidi
import Mathlib

/-!
# Canonical [3,6,9] depth-three SSP lane slice

Lean does not yet port the full depth-indexed 369 tree.  This module mirrors
the exact canonical slice only: every SSP/Ogg lane is paired with the fixed
digit word [3,6,9].

The slice is bidirectional with the root-369 lane because the address is fixed.
It must not be confused with the full 27-address depth-three tree.
-/

namespace Integration.OggSSP369CanonicalThreeSixNineLift

open Integration.OggSSP369RootRefinementBidi
open Integration.MoonshineSSP15SignedFRACTRANBranch

inductive Lane369Digit
  | digit3 | digit6 | digit9
  deriving DecidableEq, Repr, Fintype

abbrev Canonical369Address := Fin 1

def canonicalDigits : List Lane369Digit :=
  [.digit3, .digit6, .digit9]

structure CanonicalThreeSixNineLane where
  prime : SSPPrime
  address : Canonical369Address
  deriving DecidableEq, Repr, Fintype

def oggToCanonical369 (prime : SSPPrime) : CanonicalThreeSixNineLane :=
  ⟨prime, 0⟩

def canonical369ToOgg (lane : CanonicalThreeSixNineLane) : SSPPrime :=
  lane.prime

theorem canonical_ogg_roundtrip (prime : SSPPrime) :
    canonical369ToOgg (oggToCanonical369 prime) = prime := rfl

theorem ogg_canonical_roundtrip (lane : CanonicalThreeSixNineLane) :
    oggToCanonical369 (canonical369ToOgg lane) = lane := by
  rcases lane with ⟨prime,address⟩
  have h : address = (0 : Fin 1) := Subsingleton.elim _ _
  subst h
  rfl

def rootToCanonical369 (root : Root369Refinement) : CanonicalThreeSixNineLane :=
  ⟨root.prime, 0⟩

def canonical369ToRoot (lane : CanonicalThreeSixNineLane) : Root369Refinement :=
  ⟨lane.prime, .root⟩

theorem root_canonical_roundtrip (root : Root369Refinement) :
    canonical369ToRoot (rootToCanonical369 root) = root := by
  rcases root with ⟨prime,address⟩
  cases address
  rfl

theorem canonical_root_roundtrip (lane : CanonicalThreeSixNineLane) :
    rootToCanonical369 (canonical369ToRoot lane) = lane := by
  rcases lane with ⟨prime,address⟩
  have h : address = (0 : Fin 1) := Subsingleton.elim _ _
  subst h
  rfl

def phaseOrbitToCanonical369
    (state : Integration.OggSSP15PhaseOrbitBidi.PhaseOrbit15) :
    CanonicalThreeSixNineLane :=
  oggToCanonical369
    (Integration.OggSSP15PhaseOrbitBidi.phaseOrbit15ToOgg state)

def canonical369ToPhaseOrbit
    (lane : CanonicalThreeSixNineLane) :
    Integration.OggSSP15PhaseOrbitBidi.PhaseOrbit15 :=
  Integration.OggSSP15PhaseOrbitBidi.oggToPhaseOrbit15
    (canonical369ToOgg lane)

theorem phase_canonical_roundtrip
    (state : Integration.OggSSP15PhaseOrbitBidi.PhaseOrbit15) :
    canonical369ToPhaseOrbit (phaseOrbitToCanonical369 state) = state := by
  simp [phaseOrbitToCanonical369, canonical369ToPhaseOrbit,
    canonical369ToOgg, oggToCanonical369,
    Integration.OggSSP15PhaseOrbitBidi.phase_orbit_ogg_roundtrip]

theorem canonical_phase_roundtrip (lane : CanonicalThreeSixNineLane) :
    phaseOrbitToCanonical369 (canonical369ToPhaseOrbit lane) = lane := by
  rcases lane with ⟨prime,address⟩
  have h : address = (0 : Fin 1) := Subsingleton.elim _ _
  subst h
  simp [phaseOrbitToCanonical369, canonical369ToPhaseOrbit,
    canonical369ToOgg, oggToCanonical369,
    Integration.OggSSP15PhaseOrbitBidi.ogg_phase_orbit_roundtrip]

inductive CanonicalSliceEqualsFullDepthThreeTree : Prop
inductive ThreeByFiveGeneratesThreeSixNineDigits : Prop

theorem canonical_slice_not_full_tree :
    ¬ CanonicalSliceEqualsFullDepthThreeTree := by
  intro h
  cases h

theorem three_by_five_does_not_generate_digits :
    ¬ ThreeByFiveGeneratesThreeSixNineDigits := by
  intro h
  cases h

structure Boundary where
  canonicalDigitWord369Owned : Bool
  canonicalAddressSingleton : Bool
  oggCanonicalSliceBidiPaid : Bool
  rootCanonicalSliceBidiPaid : Bool
  phaseOrbitCanonicalSliceBidiPaid : Bool
  fullDepthThreeTreePorted : Bool
  threeByFiveGeneratesDigits : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  canonicalDigitWord369Owned := true
  canonicalAddressSingleton := true
  oggCanonicalSliceBidiPaid := true
  rootCanonicalSliceBidiPaid := true
  phaseOrbitCanonicalSliceBidiPaid := true
  fullDepthThreeTreePorted := false
  threeByFiveGeneratesDigits := false

end Integration.OggSSP369CanonicalThreeSixNineLift
