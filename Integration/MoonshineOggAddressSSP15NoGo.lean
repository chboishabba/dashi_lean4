import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.MoonshineNeutralCuspRelationCrossPollination
import Mathlib

namespace Integration.MoonshineOggAddressSSP15NoGo

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.MoonshineNeutralCuspRelationCrossPollination

/-!
SSP15 itself is the fifteen Ogg/Monster prime lanes.  The exact Euclidean Ogg
address determines that lane.

This module concerns only the later lossy projection
`SSP15/Ogg lane -> (complement mode, binary orientation)`.  The decisive
obstruction is that this coarse observer omits mode09 and has collisions, so it
cannot be identified with the separate five-by-three internal presentation.
This is an observer-loss theorem, not an SSP15-from-Ogg no-go.
-/

inductive BinaryOrientation
  | direct | counter
  deriving DecidableEq, Repr

abbrev AddressCoarse10 := Mode5 × BinaryOrientation

def addressMode : SSPPrime → Mode5
  | .p2  => .m27
  | .p3  => .m36
  | .p5  => .m45
  | .p7  => .m27
  | .p11 => .m27
  | .p13 => .m45
  | .p17 => .m18
  | .p19 => .m18
  | .p23 => .m45
  | .p29 => .m27
  | .p31 => .m45
  | .p41 => .m45
  | .p47 => .m27
  | .p59 => .m45
  | .p71 => .m18

def addressOrientation : SSPPrime → BinaryOrientation
  | .p2  => .direct
  | .p3  => .direct
  | .p5  => .counter
  | .p7  => .counter
  | .p11 => .direct
  | .p13 => .direct
  | .p17 => .counter
  | .p19 => .direct
  | .p23 => .counter
  | .p29 => .direct
  | .p31 => .direct
  | .p41 => .counter
  | .p47 => .direct
  | .p59 => .counter
  | .p71 => .counter

def addressCoarse10 (p : SSPPrime) : AddressCoarse10 :=
  (addressMode p, addressOrientation p)

theorem p2_p11_coarse_collision :
    addressCoarse10 .p2 = addressCoarse10 .p11 := rfl

theorem p5_p23_coarse_collision :
    addressCoarse10 .p5 = addressCoarse10 .p23 := rfl

theorem address_mode_ne_m09 (p : SSPPrime) :
    addressMode p ≠ .m09 := by
  cases p <;> decide

theorem address_coarse10_not_injective :
    ¬ Function.Injective addressCoarse10 := by
  intro h
  have hp := h p2_p11_coarse_collision
  cases hp

/-- No equivalence between the fifteen Ogg primes and the fifteen internal
lanes can preserve the address-derived complement-mode coordinate. -/
theorem no_mode_preserving_equiv :
    ¬ ∃ e : SSPPrime ≃ InternalLane,
        ∀ p, (e p).1 = addressMode p := by
  rintro ⟨e, preserves⟩
  let target : InternalLane := (.m09, .zero)
  let p : SSPPrime := e.symm target
  have htarget : e p = target := by
    simp [p]
  have hmode : (e p).1 = Mode5.m09 := by
    simpa [target] using congrArg Prod.fst htarget
  have had : addressMode p = Mode5.m09 := by
    rw [← preserves p]
    exact hmode
  exact address_mode_ne_m09 p had

/-- The prior explicit prime/internal indexing remains a valid carrier
bijection, but cannot be justified solely by the current address-mode law. -/
def chosenCarrierEquiv : SSPPrime ≃ InternalLane where
  toFun := primeToInternal
  invFun := internalToPrime
  left_inv := internal_prime_roundtrip
  right_inv := prime_internal_roundtrip

theorem chosen_equiv_not_address_mode_preserving :
    ¬ ∀ p, (chosenCarrierEquiv p).1 = addressMode p := by
  intro h
  exact no_mode_preserving_equiv ⟨chosenCarrierEquiv, h⟩

structure Boundary where
  addressCoarseModeOrientationOwned : Bool
  explicitCoarseCollisionOwned : Bool
  addressMode09Absent : Bool
  modePreservingFifteenBijectionImpossible : Bool
  chosenCarrierBijectionStillExists : Bool
  chosenCarrierBijectionDerivedFromAddressLaw : Bool
  ssp15CarrierIsOggPrimeCarrier : Bool
  exactOggAddressDeterminesSSP15Lane : Bool
  extraRefinementNeededForCanonicalSSP15Lane : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  addressCoarseModeOrientationOwned := true
  explicitCoarseCollisionOwned := true
  addressMode09Absent := true
  modePreservingFifteenBijectionImpossible := true
  chosenCarrierBijectionStillExists := true
  chosenCarrierBijectionDerivedFromAddressLaw := false
  ssp15CarrierIsOggPrimeCarrier := true
  exactOggAddressDeterminesSSP15Lane := true
  extraRefinementNeededForCanonicalSSP15Lane := false

end Integration.MoonshineOggAddressSSP15NoGo
