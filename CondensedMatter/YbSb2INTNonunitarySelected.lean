import CondensedMatter.SuperconductingTimeReversalGaugeObstruction

namespace CondensedMatter
namespace YbSb2

/-!
Finite exact selected-state model for the internally antisymmetric nonunitary
triplet (INT) proposal in Kataria et al., PRL accepted 3 Aug 2026,
DOI 10.1103/drzq-lfn5, arXiv:2601.07460.

Source formula:
  Δ̂ = (i τ_y) ⊗ (d · s)(i σ_y)
  d = Δ₀ η
  q = i (η × η*) ≠ 0.

This file formalizes the gauge/TR consequence of a selected nonzero q.
It does not claim a microscopic derivation of YbSb₂'s ground state.
-/

inductive Chirality
  | zero
  | positive
  | negative
  deriving DecidableEq, Repr

def negateQ : Chirality → Chirality
  | .zero => .zero
  | .positive => .negative
  | .negative => .positive

theorem fixedQIsZero
    (q : Chirality)
    (h : q = negateQ q) :
    q = .zero := by
  cases q <;> simp [negateQ] at h ⊢

inductive GlobalPhase
  | phase0
  | phaseQuarter
  | phaseHalf
  | phaseThreeQuarter
  deriving DecidableEq, Repr

inductive INTState
  | unitary
  | selected
  | conjugate
  deriving DecidableEq, Repr

def globalGauge (_ : GlobalPhase) (x : INTState) : INTState := x

def reverseINT : INTState → INTState
  | .unitary => .unitary
  | .selected => .conjugate
  | .conjugate => .selected

def qWitness : INTState → Chirality
  | .unitary => .zero
  | .selected => .positive
  | .conjugate => .negative

theorem gaugeLeavesQ
    (g : GlobalPhase) (x : INTState) :
    qWitness (globalGauge g x) = qWitness x := rfl

theorem timeReverseFlipsQ
    (x : INTState) :
    qWitness (reverseINT x) = negateQ (qWitness x) := by
  cases x <;> rfl

def intTRSystem : TROddGaugeWitnessSystem where
  State := INTState
  Gauge := GlobalPhase
  Witness := Chirality
  gaugeAction := globalGauge
  timeReverse := reverseINT
  witness := qWitness
  zeroWitness := .zero
  negateWitness := negateQ
  gaugeInvariant := gaugeLeavesQ
  timeReverseOdd := timeReverseFlipsQ
  fixedPointIsZero := fixedQIsZero

theorem selectedQNonzero :
    intTRSystem.WitnessNonzero .selected := by
  simp [TROddGaugeWitnessSystem.WitnessNonzero, intTRSystem, qWitness]

theorem selectedINTBreaksTRUpToGauge :
    ¬ intTRSystem.TRGaugeEquivalent .selected :=
  intTRSystem.nonzero_trOdd_witness_obstructs_trGaugeEquivalence
    .selected
    selectedQNonzero

/--
Provenance tag for the paper's displayed surface-state order-parameter choice
η = (1/√2)(1, exp(iπ/4), 0).

The current exact theorem consumes the source-selected nonzero-q orientation.
A subsequent owner should calculate i(η × η*) explicitly in ℂ³ and identify
that calculation with the selected q-witness.
-/
inductive EtaSelection
  | paperEta
  | paperEtaConjugate
  deriving DecidableEq, Repr

def stateOfEta : EtaSelection → INTState
  | .paperEta => .selected
  | .paperEtaConjugate => .conjugate

theorem paperEtaBreaksTRUpToGauge :
    ¬ intTRSystem.TRGaugeEquivalent (stateOfEta .paperEta) := by
  exact selectedINTBreaksTRUpToGauge

end YbSb2
end CondensedMatter
