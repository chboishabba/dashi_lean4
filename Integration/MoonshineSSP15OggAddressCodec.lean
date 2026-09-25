import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.MoonshineOggAddressSSP15NoGo
import Mathlib

namespace Integration.MoonshineSSP15OggAddressCodec

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.MoonshineOggAddressSSP15NoGo

/-!
SSP15 is the fifteen Ogg / Monster prime lanes.

The exact Euclidean Ogg address `p = 9*q + r`, restricted to those fifteen
primes, is therefore a genuine 15-way lane code.  Complement mode and binary
orientation are downstream observations and may collide without collapsing
lane identity.
-/

abbrev SSP15Lane := SSPPrime

inductive SSP15OggAddress15
  | a02 | a03 | a05 | a07 | a11 | a13 | a17 | a19
  | a23 | a29 | a31 | a41 | a47 | a59 | a71
  deriving DecidableEq, Repr

def coarseSheets : SSP15OggAddress15 → Nat
  | .a02 | .a03 | .a05 | .a07 => 0
  | .a11 | .a13 | .a17 => 1
  | .a19 | .a23 => 2
  | .a29 | .a31 => 3
  | .a41 => 4
  | .a47 => 5
  | .a59 => 6
  | .a71 => 7

def remainder : SSP15OggAddress15 → Nat
  | .a02 => 2 | .a03 => 3 | .a05 => 5 | .a07 => 7
  | .a11 => 2 | .a13 => 4 | .a17 => 8 | .a19 => 1
  | .a23 => 5 | .a29 => 2 | .a31 => 4 | .a41 => 5
  | .a47 => 2 | .a59 => 5 | .a71 => 8

def addressValue (a : SSP15OggAddress15) : Nat :=
  coarseSheets a * 9 + remainder a

def addressFromSSP15Lane : SSP15Lane → SSP15OggAddress15
  | .p2 => .a02 | .p3 => .a03 | .p5 => .a05 | .p7 => .a07
  | .p11 => .a11 | .p13 => .a13 | .p17 => .a17 | .p19 => .a19
  | .p23 => .a23 | .p29 => .a29 | .p31 => .a31 | .p41 => .a41
  | .p47 => .a47 | .p59 => .a59 | .p71 => .a71

def ssp15LaneFromAddress : SSP15OggAddress15 → SSP15Lane
  | .a02 => .p2 | .a03 => .p3 | .a05 => .p5 | .a07 => .p7
  | .a11 => .p11 | .a13 => .p13 | .a17 => .p17 | .a19 => .p19
  | .a23 => .p23 | .a29 => .p29 | .a31 => .p31 | .a41 => .p41
  | .a47 => .p47 | .a59 => .p59 | .a71 => .p71

theorem lane_after_address (lane : SSP15Lane) :
    ssp15LaneFromAddress (addressFromSSP15Lane lane) = lane := by
  cases lane <;> rfl

theorem address_after_lane (a : SSP15OggAddress15) :
    addressFromSSP15Lane (ssp15LaneFromAddress a) = a := by
  cases a <;> rfl

def primeValue : SSP15Lane → Nat
  | .p2 => 2 | .p3 => 3 | .p5 => 5 | .p7 => 7
  | .p11 => 11 | .p13 => 13 | .p17 => 17 | .p19 => 19
  | .p23 => 23 | .p29 => 29 | .p31 => 31 | .p41 => 41
  | .p47 => 47 | .p59 => 59 | .p71 => 71

theorem address_value_is_ssp15_prime (lane : SSP15Lane) :
    addressValue (addressFromSSP15Lane lane) = primeValue lane := by
  cases lane <;> rfl

/-- The old coarse observer factors through the exact SSP15/Ogg lane.  Its
collisions are therefore observer collisions, not lane identifications. -/
def coarseObserverFromExactAddress (a : SSP15OggAddress15) : AddressCoarse10 :=
  addressCoarse10 (ssp15LaneFromAddress a)

theorem coarse_observer_factors_through_exact_lane (lane : SSP15Lane) :
    coarseObserverFromExactAddress (addressFromSSP15Lane lane) =
      addressCoarse10 lane := by
  cases lane <;> rfl

structure Boundary where
  ssp15CarrierIsOggPrimeCarrier : Bool
  exactAddressCarrierHasFifteenCases : Bool
  exactAddressDecodesSSP15Lane : Bool
  laneAddressRoundTripPaid : Bool
  addressLaneRoundTripPaid : Bool
  coarseModeOrientationIsOnlyDerivedObserver : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ssp15CarrierIsOggPrimeCarrier := true
  exactAddressCarrierHasFifteenCases := true
  exactAddressDecodesSSP15Lane := true
  laneAddressRoundTripPaid := true
  addressLaneRoundTripPaid := true
  coarseModeOrientationIsOnlyDerivedObserver := true

end Integration.MoonshineSSP15OggAddressCodec
