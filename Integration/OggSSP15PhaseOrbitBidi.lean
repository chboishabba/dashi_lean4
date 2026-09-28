import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.MoonshineSSP15OggAddressCodec
import Mathlib

/-!
# Ogg / SSP15 ↔ 3 × 5 phase-orbit presentation

Lean mirror of the Agda composed bidi.

The authoritative SSP15 carrier remains the fifteen Ogg/Monster prime lanes.
This file composes the existing CHOSEN finite prime/internal indexing with an
exact finite 3×5 presentation of the internal lane.

Lean now also owns the actual structural source of the five-way factor:
the inner two-trit sheet T^2 modulo simultaneous sign inversion.  Canonical
orbit representatives and the phase-preserving T^3 -> 3 x 5 reduction are
explicit below.  The remaining authority boundary is semantic, not structural:
this 3 x 5 presentation is not promoted to the canonical arithmetic identity
of the Ogg primes.
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

/-! ## Structural five-orbit source: T² modulo simultaneous inversion -/

abbrev InnerT2 := BalancedPhase × BalancedPhase

def negatePhase : BalancedPhase → BalancedPhase
  | .negative => .positive
  | .zero => .zero
  | .positive => .negative

theorem negate_phase_involutive (phase : BalancedPhase) :
    negatePhase (negatePhase phase) = phase := by
  cases phase <;> rfl

def innerInvert : InnerT2 → InnerT2
  | (y,z) => (negatePhase y, negatePhase z)

theorem inner_invert_involutive (state : InnerT2) :
    innerInvert (innerInvert state) = state := by
  rcases state with ⟨y,z⟩
  cases y <;> cases z <;> rfl

def quotientInnerT2 : InnerT2 → FiveOrbit
  | (.zero,.zero) => .zeroOrbit
  | (.negative,.zero) | (.positive,.zero) => .firstAxisOrbit
  | (.zero,.negative) | (.zero,.positive) => .secondAxisOrbit
  | (.negative,.negative) | (.positive,.positive) => .equalSignOrbit
  | (.negative,.positive) | (.positive,.negative) => .oppositeSignOrbit

theorem quotient_inner_inversion_invariant (state : InnerT2) :
    quotientInnerT2 (innerInvert state) = quotientInnerT2 state := by
  rcases state with ⟨y,z⟩
  cases y <;> cases z <;> rfl

def canonicalInnerRepresentative : FiveOrbit → InnerT2
  | .zeroOrbit => (.zero,.zero)
  | .firstAxisOrbit => (.positive,.zero)
  | .secondAxisOrbit => (.zero,.positive)
  | .equalSignOrbit => (.positive,.positive)
  | .oppositeSignOrbit => (.positive,.negative)

theorem quotient_canonical_representative (orbit : FiveOrbit) :
    quotientInnerT2 (canonicalInnerRepresentative orbit) = orbit := by
  cases orbit <;> rfl

abbrev BalancedT3 := BalancedPhase × BalancedPhase × BalancedPhase

def reduceBalancedT3 : BalancedT3 → PhaseOrbit15
  | (x,y,z) => (x, quotientInnerT2 (y,z))

def canonicalLiftPhaseOrbit : PhaseOrbit15 → BalancedT3
  | (phase,orbit) =>
      let yz := canonicalInnerRepresentative orbit
      (phase, yz.1, yz.2)

theorem reduce_canonical_lift (state : PhaseOrbit15) :
    reduceBalancedT3 (canonicalLiftPhaseOrbit state) = state := by
  rcases state with ⟨phase,orbit⟩
  cases orbit <;> rfl

def invertInnerBalancedT3 : BalancedT3 → BalancedT3
  | (x,y,z) => (x, negatePhase y, negatePhase z)

theorem reduce_inner_inversion_invariant (state : BalancedT3) :
    reduceBalancedT3 (invertInnerBalancedT3 state) =
      reduceBalancedT3 state := by
  rcases state with ⟨x,y,z⟩
  cases y <;> cases z <;> rfl


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

/-! ## Exact address ↔ phase-orbit commuting triangle -/

def addressToPhaseOrbit : SSP15OggAddress15 → PhaseOrbit15 :=
  fun address => oggToPhaseOrbit15 (ssp15LaneFromAddress address)

def phaseOrbitToAddress : PhaseOrbit15 → SSP15OggAddress15 :=
  fun state => addressFromSSP15Lane (phaseOrbit15ToOgg state)

theorem address_phase_orbit_roundtrip (address : SSP15OggAddress15) :
    phaseOrbitToAddress (addressToPhaseOrbit address) = address := by
  simp [addressToPhaseOrbit, phaseOrbitToAddress,
    ogg_phase_orbit_roundtrip, address_after_lane]

theorem phase_orbit_address_roundtrip (state : PhaseOrbit15) :
    addressToPhaseOrbit (phaseOrbitToAddress state) = state := by
  simp [addressToPhaseOrbit, phaseOrbitToAddress,
    phase_orbit_ogg_roundtrip, lane_after_address]

def addressPhaseOrbitEquiv : SSP15OggAddress15 ≃ PhaseOrbit15 where
  toFun := addressToPhaseOrbit
  invFun := phaseOrbitToAddress
  left_inv := address_phase_orbit_roundtrip
  right_inv := phase_orbit_address_roundtrip

def phaseOrbitPrimeValue (state : PhaseOrbit15) : Nat :=
  primeValue (phaseOrbit15ToOgg state)

def phaseOrbitAddressValue (state : PhaseOrbit15) : Nat :=
  addressValue (phaseOrbitToAddress state)

theorem phase_orbit_address_value_is_prime_value (state : PhaseOrbit15) :
    phaseOrbitAddressValue state = phaseOrbitPrimeValue state := by
  simp [phaseOrbitAddressValue, phaseOrbitPrimeValue, phaseOrbitToAddress,
    address_value_is_ssp15_prime]

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
  directAddressThreeByFiveBidiPaid : Bool
  exactPrimeValuePreservedThroughPresentation : Bool
  threeTimesFiveCountFifteen : Bool
  actualInnerT2InversionQuotientPorted : Bool
  canonicalQuotientRepresentativesOwned : Bool
  phasePreservingT3ReductionOwned : Bool
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
  directAddressThreeByFiveBidiPaid := true
  exactPrimeValuePreservedThroughPresentation := true
  threeTimesFiveCountFifteen := true
  actualInnerT2InversionQuotientPorted := true
  canonicalQuotientRepresentativesOwned := true
  phasePreservingT3ReductionOwned := true
  chosenPresentationIsCanonicalAddress := false
  fiveOrbitArithmeticInvariant := false
  presentationRedefinesSSP15 := false

end Integration.OggSSP15PhaseOrbitBidi
