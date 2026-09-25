import Integration.MoonshineOggAddressSSP15NoGo
import Integration.MoonshineSSP15PrimeInternalFibre
import Mathlib

namespace Integration.MoonshineOggAddressResidualFibre

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.MoonshineOggAddressSSP15NoGo
open Integration.MoonshineSSP15PrimeInternalFibre

/-!
The Ogg/nonary law supplies a coarse address observation, not a canonical
internal SSP15 lane.  The corrected semantic object therefore retains the full
`(prime, internalLane)` state as residual data.

This module records the exact lossless factorization and proves that dropping
the residual is genuinely lossy.
-/

abbrev AddressObservedPrimeInternal :=
  AddressCoarse10 × PrimeInternalCarrier

def observeWithResidual (s : PrimeInternalCarrier) :
    AddressObservedPrimeInternal :=
  (addressCoarse10 s.1, s)

def observedAddress (s : AddressObservedPrimeInternal) : AddressCoarse10 :=
  s.1

def residualPrimeInternal (s : AddressObservedPrimeInternal) :
    PrimeInternalCarrier :=
  s.2

theorem recover_after_observe (s : PrimeInternalCarrier) :
    residualPrimeInternal (observeWithResidual s) = s := rfl

theorem address_observation_factors_through_prime (s : PrimeInternalCarrier) :
    observedAddress (observeWithResidual s) = addressCoarse10 s.1 := rfl

/-- Same prime, distinct internal lanes: the coarse Ogg observer intentionally
forgets the internal SSP15 coordinate. -/
theorem p71_neutral_counterposed_same_observed_address :
    observedAddress (observeWithResidual p71NeutralPair) =
      observedAddress (observeWithResidual p71CounterposedPair) := rfl

theorem p71_residual_still_distinguishes_states :
    residualPrimeInternal (observeWithResidual p71NeutralPair) ≠
      residualPrimeInternal (observeWithResidual p71CounterposedPair) := by
  simpa [residualPrimeInternal, observeWithResidual] using
    p71_neutral_counterposed_distinct

/-- Because p2 and p11 have the same coarse observation, no function from the
coarse address carrier back to primes can be a left inverse of the observer. -/
theorem coarse_address_has_no_prime_left_inverse :
    ¬ ∃ recoverPrime : AddressCoarse10 → SSPPrime,
        ∀ p, recoverPrime (addressCoarse10 p) = p := by
  rintro ⟨recoverPrime, h⟩
  have hsame :
      recoverPrime (addressCoarse10 .p2) =
        recoverPrime (addressCoarse10 .p11) :=
    congrArg recoverPrime p2_p11_coarse_collision
  have hp : SSPPrime.p2 = SSPPrime.p11 := by
    rw [h .p2, h .p11] at hsame
    exact hsame
  cases hp

structure Boundary where
  coarseAddressIsObservationOnly : Bool
  fullPrimeInternalStateRetainedUpstairs : Bool
  residualRoundTripIsExact : Bool
  coarseAddressForgetsInternalLane : Bool
  coarseAddressCannotRecoverPrime : Bool
  residualRefinementRequiredForLosslessSemantics : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  coarseAddressIsObservationOnly := true
  fullPrimeInternalStateRetainedUpstairs := true
  residualRoundTripIsExact := true
  coarseAddressForgetsInternalLane := true
  coarseAddressCannotRecoverPrime := true
  residualRefinementRequiredForLosslessSemantics := true

end Integration.MoonshineOggAddressResidualFibre
