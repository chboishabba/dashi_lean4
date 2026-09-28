import Integration.TrialecticDyadicLocalComplement
import Integration.MoonshineNeutralCuspRelationCrossPollination
import Integration.MoonshineSSP15SignedFRACTRANBranch
import Integration.TernaryHub
import Mathlib

/-!
# Trialectic T5 -> SSP15 phase/orbit × nine-state residual

Compact Lean mirror of the Agda participant-centered recognition chain.

For the AB complement
  (AC, BC, CA, CB, CC)
we read
  incomingToC  = (AC,BC)
  outgoingFromC = (CA,CB)
  selfC         = CC.

Only the incoming pair is quotiented by simultaneous inversion. Hence

  T5 -> (BalancedPhase × NineOrbit5) × NinePoint
     = PhaseOrbit15 × NinePoint,

with a canonical section. The 15-state factor is then recharted through the
already-existing InternalLane ↔ SSPPrime bijection. The outgoing nine-state
residual is retained exactly.

This is a chosen SSP15 presentation, not a derivation of Ogg arithmetic labels
from T5 and not permission to discard the nine-state residual.
-/

namespace Integration.TrialecticSSP15PhaseOrbitRecognition

open Integration.TernaryHub
open Integration.TrialecticDyadicLocalComplement
open Integration.MoonshineNeutralCuspRelationCrossPollination
open Integration.MoonshineSSP15SignedFRACTRANBranch

def sspToPhase : SSPTrit → BalancedPhase
  | .negOne => .negative
  | .zero => .zero
  | .posOne => .positive

def phaseToSSP : BalancedPhase → SSPTrit
  | .negative => .negOne
  | .zero => .zero
  | .positive => .posOne

theorem phase_ssp_roundtrip (x : SSPTrit) :
    phaseToSSP (sspToPhase x) = x := by
  cases x <;> rfl

theorem ssp_phase_roundtrip (x : BalancedPhase) :
    sspToPhase (phaseToSSP x) = x := by
  cases x <;> rfl

structure CCenteredComplement where
  incomingToC : NinePoint
  outgoingFromC : NinePoint
  selfC : BalancedPhase
  deriving DecidableEq, Repr, Fintype

def t5ToCCentered : T5Carrier → CCenteredComplement
  | ⟨ac,bc,ca,cb,cc⟩ =>
      ⟨(sspToPhase ac, sspToPhase bc),
       (sspToPhase ca, sspToPhase cb),
       sspToPhase cc⟩

def cCenteredToT5 : CCenteredComplement → T5Carrier
  | ⟨(ac,bc),(ca,cb),cc⟩ =>
      ⟨phaseToSSP ac, phaseToSSP bc,
       phaseToSSP ca, phaseToSSP cb,
       phaseToSSP cc⟩

theorem ccentered_after_t5 (state : T5Carrier) :
    cCenteredToT5 (t5ToCCentered state) = state := by
  rcases state with ⟨ac,bc,ca,cb,cc⟩
  simp [t5ToCCentered, cCenteredToT5, phase_ssp_roundtrip]

theorem t5_after_ccentered (state : CCenteredComplement) :
    t5ToCCentered (cCenteredToT5 state) = state := by
  rcases state with ⟨⟨ac,bc⟩,⟨ca,cb⟩,cc⟩
  simp [t5ToCCentered, cCenteredToT5, ssp_phase_roundtrip]

def t5CCenteredEquiv : T5Carrier ≃ CCenteredComplement where
  toFun := t5ToCCentered
  invFun := cCenteredToT5
  left_inv := ccentered_after_t5
  right_inv := t5_after_ccentered

abbrev PhaseOrbitWithNineResidual :=
  PhaseOrbit15 × NinePoint

def participantCenteredQuotient :
    CCenteredComplement → PhaseOrbitWithNineResidual
  | ⟨incoming,outgoing,self⟩ =>
      ((self, quotientNine incoming), outgoing)

def canonicalLiftParticipantCentered :
    PhaseOrbitWithNineResidual → CCenteredComplement
  | ((phase,orbit),outgoing) =>
      ⟨canonicalNineRepresentative orbit, outgoing, phase⟩

theorem participant_centered_section_roundtrip
    (state : PhaseOrbitWithNineResidual) :
    participantCenteredQuotient
      (canonicalLiftParticipantCentered state) = state := by
  rcases state with ⟨⟨phase,orbit⟩,outgoing⟩
  simp [participantCenteredQuotient, canonicalLiftParticipantCentered,
    quotient_canonical_representative]

def invertIncoming (state : CCenteredComplement) : CCenteredComplement :=
  { state with incomingToC := invertNine state.incomingToC }

theorem participant_centered_inversion_invariant
    (state : CCenteredComplement) :
    participantCenteredQuotient (invertIncoming state) =
      participantCenteredQuotient state := by
  rcases state with ⟨incoming,outgoing,self⟩
  simp [participantCenteredQuotient, invertIncoming,
    quotientNine_inversion_invariant]

def quotientT5 :
    T5Carrier → PhaseOrbitWithNineResidual :=
  participantCenteredQuotient ∘ t5ToCCentered

def canonicalLiftT5 :
    PhaseOrbitWithNineResidual → T5Carrier :=
  cCenteredToT5 ∘ canonicalLiftParticipantCentered

theorem quotient_lift_t5_roundtrip
    (state : PhaseOrbitWithNineResidual) :
    quotientT5 (canonicalLiftT5 state) = state := by
  rw [show quotientT5 (canonicalLiftT5 state) =
      participantCenteredQuotient
        (t5ToCCentered
          (cCenteredToT5
            (canonicalLiftParticipantCentered state))) by rfl]
  rw [t5_after_ccentered]
  exact participant_centered_section_roundtrip state

def phaseOrbitToInternal : PhaseOrbit15 → InternalLane
  | (phase,orbit) => (orbitToMode orbit, phase)

def internalToPhaseOrbit : InternalLane → PhaseOrbit15
  | (mode,phase) => (phase, modeToOrbit mode)

theorem phase_orbit_internal_roundtrip (state : PhaseOrbit15) :
    internalToPhaseOrbit (phaseOrbitToInternal state) = state := by
  rcases state with ⟨phase,orbit⟩
  simp [phaseOrbitToInternal, internalToPhaseOrbit, orbit_mode_roundtrip]

theorem internal_phase_orbit_roundtrip (state : InternalLane) :
    phaseOrbitToInternal (internalToPhaseOrbit state) = state := by
  rcases state with ⟨mode,phase⟩
  simp [phaseOrbitToInternal, internalToPhaseOrbit, mode_orbit_roundtrip]

def phaseOrbitInternalEquiv : PhaseOrbit15 ≃ InternalLane where
  toFun := phaseOrbitToInternal
  invFun := internalToPhaseOrbit
  left_inv := phase_orbit_internal_roundtrip
  right_inv := internal_phase_orbit_roundtrip

abbrev SSPPrimeWithNineResidual :=
  SSPPrime × NinePoint

def phaseOrbitResidualToPrimeResidual :
    PhaseOrbitWithNineResidual → SSPPrimeWithNineResidual
  | (phaseOrbit,residual) =>
      (internalToPrime (phaseOrbitToInternal phaseOrbit), residual)

def primeResidualToPhaseOrbitResidual :
    SSPPrimeWithNineResidual → PhaseOrbitWithNineResidual
  | (prime,residual) =>
      (internalToPhaseOrbit (primeToInternal prime), residual)

theorem phase_prime_residual_roundtrip
    (state : PhaseOrbitWithNineResidual) :
    primeResidualToPhaseOrbitResidual
      (phaseOrbitResidualToPrimeResidual state) = state := by
  rcases state with ⟨phaseOrbit,residual⟩
  rw [show primeResidualToPhaseOrbitResidual
      (phaseOrbitResidualToPrimeResidual (phaseOrbit,residual)) =
      (internalToPhaseOrbit
        (primeToInternal
          (internalToPrime (phaseOrbitToInternal phaseOrbit))), residual) by rfl]
  rw [prime_internal_roundtrip, phase_orbit_internal_roundtrip]

theorem prime_phase_residual_roundtrip
    (state : SSPPrimeWithNineResidual) :
    phaseOrbitResidualToPrimeResidual
      (primeResidualToPhaseOrbitResidual state) = state := by
  rcases state with ⟨prime,residual⟩
  rw [show phaseOrbitResidualToPrimeResidual
      (primeResidualToPhaseOrbitResidual (prime,residual)) =
      (internalToPrime
        (phaseOrbitToInternal
          (internalToPhaseOrbit (primeToInternal prime))), residual) by rfl]
  rw [internal_phase_orbit_roundtrip, internal_prime_roundtrip]

def phaseOrbitResidualPrimeEquiv :
    PhaseOrbitWithNineResidual ≃ SSPPrimeWithNineResidual where
  toFun := phaseOrbitResidualToPrimeResidual
  invFun := primeResidualToPhaseOrbitResidual
  left_inv := phase_prime_residual_roundtrip
  right_inv := prime_phase_residual_roundtrip

def quotientT5ToPrimeResidual :
    T5Carrier → SSPPrimeWithNineResidual :=
  phaseOrbitResidualToPrimeResidual ∘ quotientT5

def canonicalLiftPrimeResidual :
    SSPPrimeWithNineResidual → T5Carrier :=
  canonicalLiftT5 ∘ primeResidualToPhaseOrbitResidual

theorem quotient_lift_prime_residual_roundtrip
    (state : SSPPrimeWithNineResidual) :
    quotientT5ToPrimeResidual
      (canonicalLiftPrimeResidual state) = state := by
  rw [show quotientT5ToPrimeResidual
      (canonicalLiftPrimeResidual state) =
      phaseOrbitResidualToPrimeResidual
        (quotientT5
          (canonicalLiftT5
            (primeResidualToPhaseOrbitResidual state))) by rfl]
  rw [quotient_lift_t5_roundtrip, prime_phase_residual_roundtrip]

theorem phase_orbit_count : Fintype.card PhaseOrbit15 = 15 := by
  native_decide

theorem nine_residual_count : Fintype.card NinePoint = 9 := by
  native_decide

theorem quotient_target_count :
    Fintype.card PhaseOrbitWithNineResidual = 135 := by
  native_decide

theorem t5_count : Fintype.card T5Carrier = 243 :=
  t5_state_count

inductive ChosenPrimePresentationIsOggArithmeticQuotient : Prop
inductive NineResidualMayBeDiscarded : Prop
inductive T5QuotientIsBijection : Prop

theorem chosen_prime_presentation_not_promoted_to_arithmetic_quotient :
    ¬ ChosenPrimePresentationIsOggArithmeticQuotient := by
  intro h
  cases h

theorem nine_residual_not_discarded :
    ¬ NineResidualMayBeDiscarded := by
  intro h
  cases h

theorem quotient_section_not_promoted_to_bijection :
    ¬ T5QuotientIsBijection := by
  intro h
  cases h

structure Boundary where
  t5ParticipantCenteredBidi : Bool
  incomingNineQuotientOwned : Bool
  outgoingNineResidualRetained : Bool
  quotientTargetIsThreeTimesFiveTimesNine : Bool
  quotientCanonicalSectionPaid : Bool
  phaseOrbitInternalLaneBidiPaid : Bool
  internalLanePrimeBidiReused : Bool
  primeResidualPresentationBidiPaid : Bool
  chosenPrimePresentationIsArithmeticOggQuotient : Bool
  residualDiscarded : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  t5ParticipantCenteredBidi := true
  incomingNineQuotientOwned := true
  outgoingNineResidualRetained := true
  quotientTargetIsThreeTimesFiveTimesNine := true
  quotientCanonicalSectionPaid := true
  phaseOrbitInternalLaneBidiPaid := true
  internalLanePrimeBidiReused := true
  primeResidualPresentationBidiPaid := true
  chosenPrimePresentationIsArithmeticOggQuotient := false
  residualDiscarded := false

end Integration.TrialecticSSP15PhaseOrbitRecognition
