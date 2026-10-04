import Integration.TrialecticDyadicLocalComplement
import Integration.TrialecticT5ComplementPhaseOrbitResidual
import Integration.TrialecticDyadicC3
import Mathlib

/-!
# Participant-centered SSP-style factor inside the dyadic complement

For AB local, the missing participant is C and the five-trit complement is

  (AC, BC, CA, CB, CC).

Interpret it as:
- incoming-to-C pair (AC,BC);
- outgoing-from-C pair (CA,CB);
- C self-coordinate CC.

Quotient only the incoming pair by simultaneous inversion.  Then

  (CC, [(AC,BC)]_±) : PhaseOrbit15

and the outgoing pair (CA,CB) remains as the exact nine-state residual.
-/

namespace Integration.TrialecticParticipantCenteredSSPFactor

open Integration.TrialecticDyadicLocalComplement
open Integration.TrialecticT5ComplementPhaseOrbitResidual
open Integration.TrialecticDyadicC3
open Integration.OggSSP15PhaseOrbitBidi
open Integration.TernaryHub

structure CCenteredComplement where
  incomingToC : InnerT2
  outgoingFromC : InnerT2
  selfC : BalancedPhase
  deriving DecidableEq, Repr, Fintype

def t5ToCCentered : T5Carrier → CCenteredComplement
  | ⟨ac,bc,ca,cb,cc⟩ =>
      ⟨ (sspToBalanced ac, sspToBalanced bc)
      , (sspToBalanced ca, sspToBalanced cb)
      , sspToBalanced cc
      ⟩

def cCenteredToT5 : CCenteredComplement → T5Carrier
  | ⟨incoming,outgoing,self⟩ =>
      ⟨ balancedToSSP incoming.1
      , balancedToSSP incoming.2
      , balancedToSSP outgoing.1
      , balancedToSSP outgoing.2
      , balancedToSSP self
      ⟩

theorem c_centered_t5_roundtrip (state : T5Carrier) :
    cCenteredToT5 (t5ToCCentered state) = state := by
  rcases state with ⟨ac,bc,ca,cb,cc⟩
  cases ac <;> cases bc <;> cases ca <;> cases cb <;> cases cc <;> rfl

theorem t5_c_centered_roundtrip (state : CCenteredComplement) :
    t5ToCCentered (cCenteredToT5 state) = state := by
  rcases state with ⟨⟨ac,bc⟩,⟨ca,cb⟩,cc⟩
  cases ac <;> cases bc <;> cases ca <;> cases cb <;> cases cc <;> rfl

def participantCenteredPhaseOrbit (state : CCenteredComplement) : PhaseOrbit15 :=
  (state.selfC, quotientInnerT2 state.incomingToC)

def participantCenteredResidual (state : CCenteredComplement) : InnerT2 :=
  state.outgoingFromC

def participantCenteredQuotient
    (state : CCenteredComplement) : PhaseOrbitWithNineResidual :=
  (participantCenteredPhaseOrbit state, participantCenteredResidual state)

def canonicalLiftParticipantCentered
    (state : PhaseOrbitWithNineResidual) : CCenteredComplement :=
  ⟨canonicalInnerRepresentative state.1.2, state.2, state.1.1⟩

theorem participant_centered_quotient_lift
    (state : PhaseOrbitWithNineResidual) :
    participantCenteredQuotient
      (canonicalLiftParticipantCentered state) = state := by
  rcases state with ⟨⟨phase,orbit⟩,⟨ca,cb⟩⟩
  cases phase <;> cases orbit <;> cases ca <;> cases cb <;> rfl

def invertIncomingToC (state : CCenteredComplement) : CCenteredComplement :=
  { state with incomingToC := innerInvert state.incomingToC }

theorem participant_centered_inversion_invariant
    (state : CCenteredComplement) :
    participantCenteredQuotient (invertIncomingToC state) =
      participantCenteredQuotient state := by
  rcases state with ⟨⟨ac,bc⟩,outgoing,self⟩
  cases ac <;> cases bc <;> rfl

theorem generic_quotient_agrees_participant_centered (state : T5Carrier) :
    quotientT5 state = participantCenteredQuotient (t5ToCCentered state) := by
  rcases state with ⟨ac,bc,ca,cb,cc⟩
  rfl

inductive CenteredParticipant
  | centeredA | centeredB | centeredC
  deriving DecidableEq, Repr, Fintype

def rotateCenteredParticipant : CenteredParticipant → CenteredParticipant
  | .centeredC => .centeredA
  | .centeredA => .centeredB
  | .centeredB => .centeredC

theorem centered_participant_cubed (p : CenteredParticipant) :
    rotateCenteredParticipant
      (rotateCenteredParticipant
        (rotateCenteredParticipant p)) = p := by
  cases p <;> rfl

theorem ab_centered_at_c : CenteredParticipant.centeredC =
    CenteredParticipant.centeredC := rfl

theorem ab_after_one_c3_centered_at_a :
    rotateCenteredParticipant .centeredC = .centeredA := rfl

theorem ab_after_two_c3_centered_at_b :
    rotateCenteredParticipant (rotateCenteredParticipant .centeredC) =
      .centeredB := rfl

theorem centered_factor_count :
    Fintype.card PhaseOrbitWithNineResidual = 135 :=
  quotient_target_count

inductive ParticipantCenteredFactorIsArithmeticOggMeaning : Prop
inductive OutgoingNineResidualMayBeDiscarded : Prop

theorem centered_factor_not_promoted_to_arithmetic_ogg_meaning :
    ¬ ParticipantCenteredFactorIsArithmeticOggMeaning := by
  intro h
  cases h

theorem outgoing_nine_residual_not_discarded :
    ¬ OutgoingNineResidualMayBeDiscarded := by
  intro h
  cases h

structure Boundary where
  complementRechartedIncomingOutgoingSelf : Bool
  incomingPairQuotientProducesFiveOrbit : Bool
  selfCoordinateSuppliesOuterPhase : Bool
  outgoingPairRetainedAsNineResidual : Bool
  quotientCanonicalSectionPaid : Bool
  genericT5QuotientAgreementPaid : Bool
  participantC3CyclesCenteredParticipant : Bool
  targetCount135 : Bool
  arithmeticOggMeaningClaimed : Bool
  residualDiscarded : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  complementRechartedIncomingOutgoingSelf := true
  incomingPairQuotientProducesFiveOrbit := true
  selfCoordinateSuppliesOuterPhase := true
  outgoingPairRetainedAsNineResidual := true
  quotientCanonicalSectionPaid := true
  genericT5QuotientAgreementPaid := true
  participantC3CyclesCenteredParticipant := true
  targetCount135 := true
  arithmeticOggMeaningClaimed := false
  residualDiscarded := false

end Integration.TrialecticParticipantCenteredSSPFactor
