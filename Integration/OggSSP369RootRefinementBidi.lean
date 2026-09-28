import Integration.OggSSP15PhaseOrbitBidi
import Mathlib

/-!
# Ogg / SSP15 ↔ root 369 refinement

Lean currently has no full depth-indexed 369 refinement hierarchy.  This file
mirrors only the mathematically forced depth-zero piece: the root address is
unique, so a root refinement is exactly an SSP prime lane plus that singleton
address.

No deeper p-adic/refinement semantics are claimed.
-/

namespace Integration.OggSSP369RootRefinementBidi

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.OggSSP15PhaseOrbitBidi

inductive Root369Address
  | root
  deriving DecidableEq, Repr, Fintype

structure Root369Refinement where
  prime : SSPPrime
  address : Root369Address
  deriving DecidableEq, Repr, Fintype

def oggToRoot369 (prime : SSPPrime) : Root369Refinement :=
  ⟨prime, .root⟩

def root369ToOgg (state : Root369Refinement) : SSPPrime :=
  state.prime

theorem root_ogg_roundtrip (prime : SSPPrime) :
    root369ToOgg (oggToRoot369 prime) = prime := rfl

theorem ogg_root_roundtrip (state : Root369Refinement) :
    oggToRoot369 (root369ToOgg state) = state := by
  rcases state with ⟨prime,address⟩
  cases address
  rfl

def oggRoot369Equiv : SSPPrime ≃ Root369Refinement where
  toFun := oggToRoot369
  invFun := root369ToOgg
  left_inv := root_ogg_roundtrip
  right_inv := ogg_root_roundtrip

def phaseOrbitToRoot369 (state : PhaseOrbit15) : Root369Refinement :=
  oggToRoot369 (phaseOrbit15ToOgg state)

def root369ToPhaseOrbit (state : Root369Refinement) : PhaseOrbit15 :=
  oggToPhaseOrbit15 (root369ToOgg state)

theorem phase_root_roundtrip (state : PhaseOrbit15) :
    root369ToPhaseOrbit (phaseOrbitToRoot369 state) = state := by
  simp [phaseOrbitToRoot369, root369ToPhaseOrbit, phase_orbit_ogg_roundtrip]

theorem root_phase_roundtrip (state : Root369Refinement) :
    phaseOrbitToRoot369 (root369ToPhaseOrbit state) = state := by
  rcases state with ⟨prime,address⟩
  cases address
  simp [phaseOrbitToRoot369, root369ToPhaseOrbit, ogg_phase_orbit_roundtrip,
    oggToRoot369]

def phaseOrbitRoot369Equiv : PhaseOrbit15 ≃ Root369Refinement where
  toFun := phaseOrbitToRoot369
  invFun := root369ToPhaseOrbit
  left_inv := phase_root_roundtrip
  right_inv := root_phase_roundtrip

def addressToRoot369
    (address : Integration.MoonshineSSP15OggAddressCodec.SSP15OggAddress15) :
    Root369Refinement :=
  oggToRoot369
    (Integration.MoonshineSSP15OggAddressCodec.ssp15LaneFromAddress address)

def root369ToAddress
    (state : Root369Refinement) :
    Integration.MoonshineSSP15OggAddressCodec.SSP15OggAddress15 :=
  Integration.MoonshineSSP15OggAddressCodec.addressFromSSP15Lane
    (root369ToOgg state)

theorem address_root_roundtrip
    (address : Integration.MoonshineSSP15OggAddressCodec.SSP15OggAddress15) :
    root369ToAddress (addressToRoot369 address) = address := by
  simp [addressToRoot369, root369ToAddress,
    Integration.MoonshineSSP15OggAddressCodec.address_after_lane]

theorem root_address_roundtrip (state : Root369Refinement) :
    addressToRoot369 (root369ToAddress state) = state := by
  rcases state with ⟨prime,address⟩
  cases address
  simp [addressToRoot369, root369ToAddress, oggToRoot369,
    Integration.MoonshineSSP15OggAddressCodec.lane_after_address]

def addressRoot369Equiv :
    Integration.MoonshineSSP15OggAddressCodec.SSP15OggAddress15 ≃
      Root369Refinement where
  toFun := addressToRoot369
  invFun := root369ToAddress
  left_inv := address_root_roundtrip
  right_inv := root_address_roundtrip

inductive Root369CreatesFullPAdicHierarchy : Prop

theorem root_only_does_not_create_full_padic_hierarchy :
    ¬ Root369CreatesFullPAdicHierarchy := by
  intro h
  cases h

structure Boundary where
  rootAddressSingleton : Bool
  oggRoot369BidiPaid : Bool
  phaseOrbitRoot369BidiPaid : Bool
  exactAddressRoot369BidiPaid : Bool
  fullDepthRefinementHierarchyPorted : Bool
  pAdicCoordinateBridgePorted : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rootAddressSingleton := true
  oggRoot369BidiPaid := true
  phaseOrbitRoot369BidiPaid := true
  exactAddressRoot369BidiPaid := true
  fullDepthRefinementHierarchyPorted := false
  pAdicCoordinateBridgePorted := false

end Integration.OggSSP369RootRefinementBidi
