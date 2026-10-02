import Integration.OggSSP15PhaseOrbitBidi
import Mathlib

/-!
# C3 equivariance of the chosen SSP15 3×5 presentation

The structural carrier `PhaseOrbit15 = BalancedPhase × FiveOrbit` has a
natural order-three action on the OUTER ternary phase, leaving the five-way
inner orbit fixed.  Transport through the exact Ogg/phase-orbit equivalence
gives a chosen order-three permutation of the fifteen Ogg lanes.

This is not identified with the independent affine SSP +12/+42 C3, which acts
on mobile complement modes / the inner mode coordinate.
-/

namespace Integration.OggSSP15PhaseOrbitC3

open Integration.OggSSP15PhaseOrbitBidi
open Integration.MoonshineSSP15SignedFRACTRANBranch

def advanceOuterPhase : BalancedPhase → BalancedPhase
  | .negative => .zero
  | .zero => .positive
  | .positive => .negative

theorem advance_outer_phase_cubed (phase : BalancedPhase) :
    advanceOuterPhase (advanceOuterPhase (advanceOuterPhase phase)) = phase := by
  cases phase <;> rfl

def advancePhaseOrbit : PhaseOrbit15 → PhaseOrbit15
  | (phase, orbit) => (advanceOuterPhase phase, orbit)

theorem advance_phase_orbit_cubed (state : PhaseOrbit15) :
    advancePhaseOrbit (advancePhaseOrbit (advancePhaseOrbit state)) = state := by
  rcases state with ⟨phase,orbit⟩
  cases phase <;> rfl

theorem advance_preserves_inner_orbit (state : PhaseOrbit15) :
    (advancePhaseOrbit state).2 = state.2 := rfl

def advanceChosenOggPresentation : SSPPrime → SSPPrime :=
  fun prime => phaseOrbit15ToOgg (advancePhaseOrbit (oggToPhaseOrbit15 prime))

theorem chosen_ogg_bidi_intertwines_outer_c3 (prime : SSPPrime) :
    oggToPhaseOrbit15 (advanceChosenOggPresentation prime) =
      advancePhaseOrbit (oggToPhaseOrbit15 prime) := by
  simp [advanceChosenOggPresentation, phase_orbit_ogg_roundtrip]

theorem chosen_ogg_presentation_cubed (prime : SSPPrime) :
    advanceChosenOggPresentation
      (advanceChosenOggPresentation
        (advanceChosenOggPresentation prime)) = prime := by
  have h := congrArg phaseOrbit15ToOgg
    (advance_phase_orbit_cubed (oggToPhaseOrbit15 prime))
  simpa [advanceChosenOggPresentation, phase_orbit_ogg_roundtrip,
    ogg_phase_orbit_roundtrip] using h

theorem presentation_p2_p3 : advanceChosenOggPresentation .p2 = .p3 := rfl
theorem presentation_p3_p5 : advanceChosenOggPresentation .p3 = .p5 := rfl
theorem presentation_p5_p2 : advanceChosenOggPresentation .p5 = .p2 := rfl

theorem presentation_p47_p59 : advanceChosenOggPresentation .p47 = .p59 := rfl
theorem presentation_p59_p71 : advanceChosenOggPresentation .p59 = .p71 := rfl
theorem presentation_p71_p47 : advanceChosenOggPresentation .p71 = .p47 := rfl

def chosenPrimeInnerOrbit (prime : SSPPrime) : FiveOrbit :=
  (oggToPhaseOrbit15 prime).2

theorem presentation_c3_preserves_inner_orbit (prime : SSPPrime) :
    chosenPrimeInnerOrbit (advanceChosenOggPresentation prime) =
      chosenPrimeInnerOrbit prime := by
  unfold chosenPrimeInnerOrbit
  rw [chosen_ogg_bidi_intertwines_outer_c3]
  rfl

/-! Minimal mirror of the independent mobile-mode C3 coordinate action. -/

inductive MobileMode3
  | mobile45 | mobile18 | mobile27
  deriving DecidableEq, Repr, Fintype

def affineAdvance12 : MobileMode3 → MobileMode3
  | .mobile45 => .mobile18
  | .mobile18 => .mobile27
  | .mobile27 => .mobile45

def affineAdvance42 : MobileMode3 → MobileMode3
  | .mobile45 => .mobile27
  | .mobile18 => .mobile45
  | .mobile27 => .mobile18

theorem affine_advance12_cubed (m : MobileMode3) :
    affineAdvance12 (affineAdvance12 (affineAdvance12 m)) = m := by
  cases m <;> rfl

theorem affine_advance42_cubed (m : MobileMode3) :
    affineAdvance42 (affineAdvance42 (affineAdvance42 m)) = m := by
  cases m <;> rfl

theorem affine_advance12_moves_mobile45 :
    affineAdvance12 .mobile45 = .mobile18 := rfl

theorem affine_advance42_moves_mobile45 :
    affineAdvance42 .mobile45 = .mobile27 := rfl

inductive PresentationOuterC3EqualsAffineModeC3 : Prop

theorem outer_phase_c3_not_promoted_to_affine_mode_c3 :
    ¬ PresentationOuterC3EqualsAffineModeC3 := by
  intro h
  cases h

structure Boundary where
  outerPhaseC3Owned : Bool
  outerPhaseC3OrderThree : Bool
  chosenOggPresentationActionOwned : Bool
  chosenOggBidiIntertwinesOuterC3 : Bool
  chosenInnerOrbitPreserved : Bool
  affineMobileModeC3Owned : Bool
  affineMobileModeC3MovesInnerMode : Bool
  outerPhaseC3IdentifiedWithAffineModeC3 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  outerPhaseC3Owned := true
  outerPhaseC3OrderThree := true
  chosenOggPresentationActionOwned := true
  chosenOggBidiIntertwinesOuterC3 := true
  chosenInnerOrbitPreserved := true
  affineMobileModeC3Owned := true
  affineMobileModeC3MovesInnerMode := true
  outerPhaseC3IdentifiedWithAffineModeC3 := false

end Integration.OggSSP15PhaseOrbitC3
