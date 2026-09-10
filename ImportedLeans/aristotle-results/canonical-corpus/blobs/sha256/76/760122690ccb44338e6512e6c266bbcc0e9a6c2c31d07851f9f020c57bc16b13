/-
# A non-vacuity witness for the gauge-invariant physical carrier

`GaugeInvariantL2Carrier` builds the physical Hilbert carrier out of one literal
measure together with a measure-preserving gauge action.  An interface is worth
nothing if it is empty, so this file exhibits a completely concrete inhabitant:

* the configuration space is the finite group `Ω = ZMod 2` — the smallest
  honest "one link, one gauge group" configuration space;
* the physical measure is the Haar measure of that finite group, i.e.
  `Measure.count` (a genuine finite measure here, total mass `2`);
* the gauge action is left translation, which is measure preserving because
  `Measure.count` is left invariant;
* the constant wavefunction `1` is gauge invariant and **nonzero** in `L²`.

Hence `invariantSubspace` and therefore `PhysicalCarrier` are non-trivial in a
case where the gauge action is not the identity: none of the statements proved
about the carrier are vacuous.  No claim is made that this toy configuration
space is the Yang–Mills one.
-/
import Mathlib
import RequestProject.YangMills.GaugeInvariantL2Carrier

namespace RequestProject.YangMills.GaugeInvariantCarrierWitness

open MeasureTheory
open RequestProject.YangMills.GaugeInvariantL2Carrier

/-- The toy configuration space: the finite group `ZMod 2`. -/
abbrev Conf := ZMod 2

/-- The physical measure: counting measure, the Haar measure of a finite group. -/
noncomputable abbrev physMeasure : Measure Conf := Measure.count

instance : IsFiniteMeasure physMeasure := by
  constructor
  simp [physMeasure, Measure.count_apply_finite]

/-- The gauge action: left translation. -/
def gaugeAct : Conf → Conf → Conf := fun g x => g + x

theorem gaugeAct_measurePreserving (g : Conf) :
    MeasurePreserving (gaugeAct g) physMeasure physMeasure :=
  measurePreserving_add_left physMeasure g

/-- The nontrivial gauge transformation really moves configurations. -/
theorem gaugeAct_ne_id : gaugeAct 1 ≠ id := by
  intro h
  have := congrFun h 0
  simp [gaugeAct] at this

/-- The constant wavefunction. -/
noncomputable def constWave : Lp ℂ 2 physMeasure := (memLp_const (1 : ℂ)).toLp _

/-- It is gauge invariant. -/
theorem constWave_mem_invariantSubspace :
    constWave ∈ invariantSubspace gaugeAct gaugeAct_measurePreserving := by
  rw [mem_invariantSubspace_iff]
  intro _
  rfl

/-- It is nonzero. -/
theorem constWave_ne_zero : constWave ≠ 0 := by
  intro h
  have hc := (memLp_const (1 : ℂ) (μ := physMeasure) (p := 2)).coeFn_toLp
  rw [show ((memLp_const (1 : ℂ) (μ := physMeasure) (p := 2)).toLp _) = constWave from rfl,
    h] at hc
  have h0 : ∀ᵐ x ∂physMeasure, (0 : ℂ) = 1 := by
    filter_upwards [hc, Lp.coeFn_zero ℂ 2 physMeasure] with x hx hx0
    exact (hx0.trans (Pi.zero_apply x)).symm.trans hx
  have h1 := (MeasureTheory.Measure.ae_count_iff).mp h0 0
  simp at h1

/-- **The physical carrier of a nontrivial gauge action is non-trivial.** -/
theorem physicalCarrier_nontrivial :
    ∃ x : PhysicalCarrier gaugeAct gaugeAct_measurePreserving, x ≠ 0 :=
  ⟨⟨constWave, constWave_mem_invariantSubspace⟩, by
    intro h
    exact constWave_ne_zero (congrArg Subtype.val h)⟩

end RequestProject.YangMills.GaugeInvariantCarrierWitness

#print axioms RequestProject.YangMills.GaugeInvariantCarrierWitness.physicalCarrier_nontrivial
#print axioms RequestProject.YangMills.GaugeInvariantCarrierWitness.gaugeAct_ne_id
