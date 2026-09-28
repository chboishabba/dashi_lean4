import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.MoonshineSSP15OggAddressCodec
import Mathlib

/-!
# Ogg / SSP15 ↔ 3 × 5 phase-orbit presentation

Lean mirror of the Agda composed bidi.

The authoritative SSP15 carrier remains the fifteen Ogg/Monster prime lanes.
This file composes the existing CHOSEN finite prime/internal indexing with an
exact finite 3×5 presentation of the internal lane.

Unlike the Agda source, Lean does not yet port the actual
T^2 / inner-inversion quotient theorem producing the five orbits.  Therefore
the finite 5-way orbit chart is exact as a presentation, while structural
quotient provenance is explicitly left unpaid.
-/

namespace Integration.OggSSP15PhaseOrbitBidi

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.MoonshineSSP15OggAddressCodec
open Integration.MoonshineNeutralCuspRelationCrossPollination

inductive FiveOrbit
  | zeroOrbit
  | firstAxisOrbit
  | secondAxisOrbit
  | equalSignOrbit
  | oppositeSignOrbit
  deriving DecidableEq, Repr, Fintype

abbrev PhaseOrbit15 := BalancedPhase × FiveOrbit

def orbitToMode : FiveOrbit → Mode5
  | .zeroOrbit => .m09
  | .firstAxisOrbit => .m18
  | .secondAxisOrbit => .m27
  | .equalSignOrbit => .m36
  | .oppositeSignOrbit => .m45

def modeToOrbit : Mode5 → FiveOrbit
  | .m09 => .zeroOrbit
  | .m18 => .firstAxisOrbit
  | .m27 => .secondAxisOrbit
  | .m36 => .equalSignOrbit
  | .m45 => .oppositeSignOrbit

theorem orbit_mode_roundtrip (orbit : FiveOrbit) :
    modeToOrbit (orbitToMode orbit) = orbit := by
  cases orbit <;> rfl

theorem mode_orbit_roundtrip (mode : Mode5) :
    orbitToMode (modeToOrbit mode) = mode := by
  cases mode <;> rfl

def phaseOrbitToInternal : PhaseOrbit15 → InternalLane
  | (phase, orbit) => (orbitToMode orbit, phase)

def internalToPhaseOrbit : InternalLane → PhaseOrbit15
  | (mode, phase) => (phase, modeToOrbit mode)

theorem phase_orbit_internal_roundtrip (state : PhaseOrbit15) :
    internalToPhaseOrbit (phaseOrbitToInternal state) = state := by
  rcases state with ⟨phase, orbit⟩
  simp [internalToPhaseOrbit, phaseOrbitToInternal, orbit_mode_roundtrip]

theorem internal_phase_orbit_roundtrip (lane : InternalLane) :
    phaseOrbitToInternal (internalToPhaseOrbit lane) = lane := by
  rcases lane with ⟨mode, phase⟩
  simp [internalToPhaseOrbit, phaseOrbitToInternal, mode_orbit_roundtrip]

def oggToPhaseOrbit15 : SSPPrime → PhaseOrbit15 :=
  fun prime => internalToPhaseOrbit (primeToInternal prime)

def phaseOrbit15ToOgg : PhaseOrbit15 → SSPPrime :=
  fun state => internalToPrime (phaseOrbitToInternal state)

theorem ogg_phase_orbit_roundtrip (prime : SSPPrime) :
    phaseOrbit15ToOgg (oggToPhaseOrbit15 prime) = prime := by
  simp [oggToPhaseOrbit15, phaseOrbit15ToOgg,
    internal_phase_orbit_roundtrip, internal_prime_roundtrip]

theorem phase_orbit_ogg_roundtrip (state : PhaseOrbit15) :
    oggToPhaseOrbit15 (phaseOrbit15ToOgg state) = state := by
  rcases state with ⟨phase, orbit⟩
  simp [oggToPhaseOrbit15, phaseOrbit15ToOgg,
    phase_orbit_internal_roundtrip, prime_internal_roundtrip]

def oggPhaseOrbitEquiv : SSPPrime ≃ PhaseOrbit15 where
  toFun := oggToPhaseOrbit15
  invFun := phaseOrbit15ToOgg
  left_inv := ogg_phase_orbit_roundtrip
  right_inv := phase_orbit_ogg_roundtrip

theorem five_orbit_count : Fintype.card FiveOrbit = 5 := by decide

theorem phase_orbit_count : Fintype.card PhaseOrbit15 = 15 := by
  native_decide

/-! Canonical exact Ogg address remains the identity code. -/

theorem exact_address_still_roundtrips (prime : SSPPrime) :
    ssp15LaneFromAddress (addressFromSSP15Lane prime) = prime :=
  lane_after_address prime

inductive ChosenPresentationIsCanonicalOggAddress : Prop
inductive FiveOrbitIsArithmeticPrimeInvariant : Prop
inductive ThreeByFiveRedefinesSSP15 : Prop

theorem chosen_presentation_not_canonical_address :
    ¬ ChosenPresentationIsCanonicalOggAddress := by
  intro h
  cases h

theorem five_orbit_not_promoted_to_arithmetic_invariant :
    ¬ FiveOrbitIsArithmeticPrimeInvariant := by
  intro h
  cases h

theorem three_by_five_does_not_redefine_ssp15 :
    ¬ ThreeByFiveRedefinesSSP15 := by
  intro h
  cases h

structure Boundary where
  authoritativeCarrierIsOggPrimeLane : Bool
  exactOggAddressRemainsCanonicalIdentity : Bool
  chosenPrimeInternalBijectionReused : Bool
  internalThreeByFiveBidiPaid : Bool
  composedOggThreeByFiveBidiPaid : Bool
  threeTimesFiveCountFifteen : Bool
  actualInnerT2InversionQuotientPorted : Bool
  chosenPresentationIsCanonicalAddress : Bool
  fiveOrbitArithmeticInvariant : Bool
  presentationRedefinesSSP15 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  authoritativeCarrierIsOggPrimeLane := true
  exactOggAddressRemainsCanonicalIdentity := true
  chosenPrimeInternalBijectionReused := true
  internalThreeByFiveBidiPaid := true
  composedOggThreeByFiveBidiPaid := true
  threeTimesFiveCountFifteen := true
  actualInnerT2InversionQuotientPorted := false
  chosenPresentationIsCanonicalAddress := false
  fiveOrbitArithmeticInvariant := false
  presentationRedefinesSSP15 := false

end Integration.OggSSP15PhaseOrbitBidi
