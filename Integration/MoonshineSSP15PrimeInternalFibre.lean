import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.MoonshineOggAddressSSP15NoGo
import Mathlib

namespace Integration.MoonshineSSP15PrimeInternalFibre

open Integration.MoonshineSSP15SignedFRACTRANBranch

/-!
SSP15 itself is the fifteen Ogg/Monster prime lanes.

The product below is only an enriched state space obtained by attaching an
independent five-by-three internal observer state to an SSP15/Ogg lane.
Therefore 15*15=225 counts enriched combinations, not SSP15 lanes.
-/

abbrev PrimeInternalCarrier := SSPPrime × InternalLane

theorem prime_internal_count_arithmetic : 15 * 15 = 225 := by norm_num

def chosenGaugeSection (p : SSPPrime) : PrimeInternalCarrier :=
  (p, primeToInternal p)

theorem chosen_gauge_preserves_prime (p : SSPPrime) :
    (chosenGaugeSection p).1 = p := rfl

theorem chosen_gauge_uses_chosen_lane (p : SSPPrime) :
    (chosenGaugeSection p).2 = primeToInternal p := rfl

def p71NeutralPair : PrimeInternalCarrier :=
  (.p71, (.m09, .zero))

def p71CounterposedPair : PrimeInternalCarrier :=
  (.p71, (.m18, .negative))

theorem p71_neutral_counterposed_distinct :
    p71NeutralPair ≠ p71CounterposedPair := by decide

theorem chosen_gauge_p71_not_neutral :
    chosenGaugeSection .p71 ≠ p71NeutralPair := by decide

theorem chosen_gauge_p71_not_counterposed :
    chosenGaugeSection .p71 ≠ p71CounterposedPair := by decide

/-- Prime and internal lane remain independent coordinates. -/
structure PrimeInternalState where
  prime : SSPPrime
  lane : InternalLane
  deriving DecidableEq, Repr

def attachPrimeInternal (p : SSPPrime) (l : InternalLane) : PrimeInternalState :=
  ⟨p,l⟩

theorem attached_lane_exact (p : SSPPrime) (l : InternalLane) :
    (attachPrimeInternal p l).lane = l := rfl

theorem same_prime_multiple_internal_states :
    (attachPrimeInternal .p71 (.m09,.zero)).prime =
      (attachPrimeInternal .p71 (.m18,.negative)).prime
    ∧
    (attachPrimeInternal .p71 (.m09,.zero)).lane ≠
      (attachPrimeInternal .p71 (.m18,.negative)).lane := by
  constructor
  · rfl
  · decide



/-! Canonical signed lift from the full prime/internal pair. -/

def primeInternalToPointedSigned (s : PrimeInternalCarrier) : PointedSignedLane :=
  ⟨s.1, phaseToUnitMultiplicity s.2.2⟩

theorem prime_internal_pointed_prime_exact (s : PrimeInternalCarrier) :
    (primeInternalToPointedSigned s).selectedPrime = s.1 := rfl

theorem prime_internal_pointed_phase_exact (s : PrimeInternalCarrier) :
    coarseMultiplicity (primeInternalToPointedSigned s).signedMultiplicity = s.2.2 := by
  rcases s with ⟨p, m, ph⟩
  cases ph <;> rfl

def primeInternalValuation (s : PrimeInternalCarrier) : SSPValuation :=
  pointedValuation (primeInternalToPointedSigned s)

theorem prime_internal_valuation_own_lane (s : PrimeInternalCarrier) :
    primeInternalValuation s s.1 =
      phaseToUnitMultiplicity s.2.2 := by
  simp [primeInternalValuation, primeInternalToPointedSigned, pointedValuation]

structure Boundary where
  primeLaneCountFifteen : Bool
  ssp15LaneCarrierIsOggPrimeCarrier : Bool
  internalLaneCountFifteen : Bool
  coarseProductCount225 : Bool
  product225IsSSP15LaneCount : Bool
  primeAndInternalAreIndependentCoordinates : Bool
  chosenBijectionIsGaugeSection : Bool
  chosenGaugeExhaustsSemanticCarrier : Bool
  explicitOffGaugeP71StatesOwned : Bool
  canonicalSignedLiftUsesPrimeInternalPair : Bool
  primeEqualsInternalLaneSemantically : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  primeLaneCountFifteen := true
  ssp15LaneCarrierIsOggPrimeCarrier := true
  internalLaneCountFifteen := true
  coarseProductCount225 := true
  product225IsSSP15LaneCount := false
  primeAndInternalAreIndependentCoordinates := true
  chosenBijectionIsGaugeSection := true
  chosenGaugeExhaustsSemanticCarrier := false
  explicitOffGaugeP71StatesOwned := true
  canonicalSignedLiftUsesPrimeInternalPair := true
  primeEqualsInternalLaneSemantically := false

end Integration.MoonshineSSP15PrimeInternalFibre
