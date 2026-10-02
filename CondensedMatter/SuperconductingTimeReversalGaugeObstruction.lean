import Mathlib

namespace CondensedMatter

/--
Reusable abstract package for a superconducting order parameter carrying a
TR-odd, gauge-invariant witness.

The intended application is q = i (η × η*) for a nonunitary triplet state,
but the theorem is independent of that representation.
-/
structure TROddGaugeWitnessSystem where
  State : Type
  Gauge : Type
  Witness : Type
  gaugeAction : Gauge → State → State
  timeReverse : State → State
  witness : State → Witness
  zeroWitness : Witness
  negateWitness : Witness → Witness
  gaugeInvariant :
    ∀ (g : Gauge) (x : State),
      witness (gaugeAction g x) = witness x
  timeReverseOdd :
    ∀ x : State,
      witness (timeReverse x) = negateWitness (witness x)
  fixedPointIsZero :
    ∀ w : Witness,
      w = negateWitness w →
      w = zeroWitness

namespace TROddGaugeWitnessSystem

variable (S : TROddGaugeWitnessSystem)

def TRGaugeEquivalent (x : S.State) : Prop :=
  ∃ g : S.Gauge, S.timeReverse x = S.gaugeAction g x

def WitnessNonzero (x : S.State) : Prop :=
  S.witness x ≠ S.zeroWitness

theorem trGaugeEquivalent_forces_witness_zero
    (x : S.State)
    (hTR : S.TRGaugeEquivalent x) :
    S.witness x = S.zeroWitness := by
  rcases hTR with ⟨g, hrg⟩
  apply S.fixedPointIsZero
  have hrev : S.witness (S.timeReverse x) = S.witness x := by
    rw [hrg]
    exact S.gaugeInvariant g x
  calc
    S.witness x = S.negateWitness (S.witness x) := by
      rw [← S.timeReverseOdd x, hrev]

theorem nonzero_trOdd_witness_obstructs_trGaugeEquivalence
    (x : S.State)
    (hnz : S.WitnessNonzero x) :
    ¬ S.TRGaugeEquivalent x := by
  intro hTR
  exact hnz (S.trGaugeEquivalent_forces_witness_zero x hTR)

end TROddGaugeWitnessSystem
end CondensedMatter
