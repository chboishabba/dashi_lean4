/-
# Row B — non-vacuity and axiom checks for the derived activity decay rate

`PolymerActivityDecay` derives the Row-B activity decay rate from the product
structure of a Mayer/cluster activity rather than transcribing it from a source.
A derived bound is only worth having if the objects it bounds are not identically
zero, so this file records:

* `mayerFactor_ne_zero` — the Mayer factor of a nonzero interaction is nonzero;
* `mayerActivity_ne_zero` — hence a polymer activity with a nonzero interaction
  at each constituent is nonzero, so the exponential majorant is a genuine
  estimate on a genuinely nonvanishing family;
* `mayerActivity_lattice4_ne_zero` — the same, for a concrete four-dimensional
  lattice polymer;
* the `#print axioms` audit of the whole derived-rate lane.
-/
import RequestProject.YangMills.PolymerActivityDecay

namespace YangMills

namespace PolymerDecayChecks

open Finset

/-- The Mayer factor of a nonzero interaction is nonzero: `e^{−V} = 1` only at
`V = 0`. -/
theorem mayerFactor_ne_zero {V : ℝ} (hV : V ≠ 0) : mayerFactor V ≠ 0 := by
  rw [mayerFactor, sub_ne_zero]
  intro h
  exact hV (by simpa using (Real.exp_eq_one_iff (-V)).mp h)

/-- A polymer activity with a nonvanishing interaction at each constituent does
not vanish. -/
theorem mayerActivity_ne_zero {ι : Type*} {V : ι → ℝ} {S : Finset ι}
    (hV : ∀ p ∈ S, V p ≠ 0) : mayerActivity V S ≠ 0 := by
  rw [mayerActivity]
  exact Finset.prod_ne_zero_iff.mpr fun p hp => mayerFactor_ne_zero (hV p hp)

/-- A concrete four-dimensional lattice polymer with a small but nonzero
interaction has a nonzero activity, and the derived majorant applies to it. -/
theorem mayerActivity_lattice4_ne_zero (S : Finset (Fin 4 → ℤ)) :
    mayerActivity (fun _ : Fin 4 → ℤ => (1 : ℝ) / 1000) S ≠ 0 :=
  mayerActivity_ne_zero fun _ _ => by norm_num

/-- The interaction `1/1000` sits strictly below the four-dimensional threshold,
so the derived rate strictly exceeds the proved entropy rate for it. -/
theorem lattice4_rate_exceeds_entropy_at_thousandth :
    lattice4EntropyRate < activityDecayRate (2 * ((1 : ℝ) / 1000)) :=
  lattice4_mayer_rate_exceeds_entropy (by norm_num) (by norm_num)

end PolymerDecayChecks

/-! ## Axiom audit -/

#print axioms activityDecayRate_gt_of_lt_exp_neg
#print axioms abs_mayerFactor_le
#print axioms abs_mayerActivity_le
#print axioms mayerActivity_exp_decay
#print axioms abs_integratedMayerActivity_le
#print axioms exp_neg_lattice4EntropyRate
#print axioms lattice4_threshold_lower
#print axioms lattice4_mayer_rate_exceeds_entropy
#print axioms lattice4_mayer_shell_energy_geometric
#print axioms lattice4_mayer_shell_energy_tsum_le
#print axioms smallCoupling_mayer_threshold
#print axioms PolymerDecayChecks.mayerActivity_ne_zero
#print axioms PolymerDecayChecks.lattice4_rate_exceeds_entropy_at_thousandth

end YangMills
