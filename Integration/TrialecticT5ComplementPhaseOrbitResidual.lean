import Integration.TrialecticDyadicLocalComplement
import Integration.OggSSP15PhaseOrbitBidi
import Mathlib

/-!
# Five-trit complement -> SSP15 phase-orbit × nine-state residual

For the AB complement coordinates

  (AC, BC, CA, CB, CC),

quotient the selected pair (AC,BC) by simultaneous sign inversion.  Retain
(CA,CB) as an explicit nine-state residual and CC as the outer ternary phase.

This yields a canonical quotient

  T5 -> PhaseOrbit15 × InnerT2

with a canonical section.  The target has 15*9 = 135 states.

Hence the SSP15 3×5 presentation is visible inside the five-trit complement
only together with an extra nine-state residual.  No canonical deletion of
that residual is claimed.
-/

namespace Integration.TrialecticT5ComplementPhaseOrbitResidual

open Integration.TrialecticDyadicLocalComplement
open Integration.OggSSP15PhaseOrbitBidi
open Integration.TernaryHub

def sspToBalanced : SSPTrit → BalancedPhase
  | .negOne => .negative
  | .zero => .zero
  | .posOne => .positive

def balancedToSSP : BalancedPhase → SSPTrit
  | .negative => .negOne
  | .zero => .zero
  | .positive => .posOne

theorem balanced_ssp_roundtrip (phase : BalancedPhase) :
    sspToBalanced (balancedToSSP phase) = phase := by
  cases phase <;> rfl

theorem ssp_balanced_roundtrip (phase : SSPTrit) :
    balancedToSSP (sspToBalanced phase) = phase := by
  cases phase <;> rfl

abbrev PhaseOrbitWithNineResidual := PhaseOrbit15 × InnerT2

def quotientT5 : T5Carrier → PhaseOrbitWithNineResidual
  | ⟨ac,bc,ca,cb,cc⟩ =>
      (
        (sspToBalanced cc,
          quotientInnerT2 (sspToBalanced ac, sspToBalanced bc)),
        (sspToBalanced ca, sspToBalanced cb)
      )

def canonicalLiftT5 : PhaseOrbitWithNineResidual → T5Carrier
  | ((phase, orbit), residual) =>
      let selected := canonicalInnerRepresentative orbit
      ⟨ balancedToSSP selected.1
      , balancedToSSP selected.2
      , balancedToSSP residual.1
      , balancedToSSP residual.2
      , balancedToSSP phase
      ⟩

theorem quotient_canonical_lift_t5
    (state : PhaseOrbitWithNineResidual) :
    quotientT5 (canonicalLiftT5 state) = state := by
  rcases state with ⟨⟨phase,orbit⟩,⟨ca,cb⟩⟩
  cases phase <;> cases orbit <;> cases ca <;> cases cb <;> rfl

def invertSelectedT2 : T5Carrier → T5Carrier
  | ⟨ac,bc,ca,cb,cc⟩ =>
      ⟨ balancedToSSP (negatePhase (sspToBalanced ac))
      , balancedToSSP (negatePhase (sspToBalanced bc))
      , ca, cb, cc
      ⟩

theorem quotient_selected_inversion_invariant (state : T5Carrier) :
    quotientT5 (invertSelectedT2 state) = quotientT5 state := by
  rcases state with ⟨ac,bc,ca,cb,cc⟩
  cases ac <;> cases bc <;> cases ca <;> cases cb <;> cases cc <;> rfl

theorem quotient_target_count :
    Fintype.card PhaseOrbitWithNineResidual = 135 := by
  native_decide

theorem quotient_target_factors_15_times_9 :
    Fintype.card PhaseOrbitWithNineResidual =
      Fintype.card PhaseOrbit15 * Fintype.card InnerT2 := by
  norm_num [phase_orbit_count]

theorem inner_t2_count : Fintype.card InnerT2 = 9 := by
  native_decide

/-! The 15-state factor is literally the existing SSP15 phase-orbit type. -/

def ssp15Factor :
    PhaseOrbitWithNineResidual → PhaseOrbit15 :=
  Prod.fst

def nineResidual :
    PhaseOrbitWithNineResidual → InnerT2 :=
  Prod.snd

inductive NineResidualCanBeDroppedCanonically : Prop
inductive FiveTritComplementEqualsSSP15Carrier : Prop

theorem nine_residual_not_dropped_without_new_law :
    ¬ NineResidualCanBeDroppedCanonically := by
  intro h
  cases h

theorem t5_not_promoted_to_ssp15_identity :
    ¬ FiveTritComplementEqualsSSP15Carrier := by
  intro h
  cases h

structure Boundary where
  selectedInnerT2QuotientOwned : Bool
  quotientInvariantUnderSelectedInversion : Bool
  canonicalSectionOwned : Bool
  quotientTargetPhaseOrbit15TimesNineResidual : Bool
  quotientTargetCount135 : Bool
  ssp15FactorCount15 : Bool
  nineResidualCount9 : Bool
  nineResidualDroppedCanonically : Bool
  t5IdentifiedWithSSP15Carrier : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  selectedInnerT2QuotientOwned := true
  quotientInvariantUnderSelectedInversion := true
  canonicalSectionOwned := true
  quotientTargetPhaseOrbit15TimesNineResidual := true
  quotientTargetCount135 := true
  ssp15FactorCount15 := true
  nineResidualCount9 := true
  nineResidualDroppedCanonically := false
  t5IdentifiedWithSSP15Carrier := false

end Integration.TrialecticT5ComplementPhaseOrbitResidual
