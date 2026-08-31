/-
# Row B — non-vacuity and axiom checks for the CMP 116 activity-rate conversion

`CMP116ActivityRate` converts the two shapes in which the source states its
small-field polymer activity estimates — a unit-lattice *volume* exponential and
a *tree-length* exponential — into the block-unit exponential majorant that the
proved Row-B shell-energy theorem consumes, and shows that the block size `M`
cancels in the volume form.  This file records that the hypothesis package is
inhabited, so nothing above is vacuous, and audits the axioms.

* `wShell`, `wVol`, `wAct` — a concrete, nonzero four-dimensional lattice
  polymer family satisfying the volume-form hypotheses at `M = 1`, `κ₁ = 30`;
* `cmp116_volume_package_inhabited` — the Row-B shell-energy conclusion for it;
* `wAct_ne_zero` — the activities are not identically zero.
-/
import RequestProject.YangMills.CMP116ActivityRate

namespace YangMills

namespace CMP116RateChecks

open Finset

/-- The base site of the witness polymer family. -/
def wV : Fin 4 → ℤ := fun _ => 0

/-- A one-polymer shell family: the single site `wV` sits in shell `1`. -/
def wShell : ℕ → Finset (Finset (Fin 4 → ℤ)) := fun n => if n = 1 then {{wV}} else ∅

/-- The unit-lattice volume of a block polymer at block size `M = 1`. -/
def wVol : Finset (Fin 4 → ℤ) → ℝ := fun S => (S.card : ℝ)

/-- A nonvanishing activity with exactly the source's volume decay. -/
noncomputable def wAct : Finset (Fin 4 → ℤ) → ℝ :=
  fun S => Real.exp (-(cmp116BlockRate 30 * (S.card : ℝ)))

theorem wShell_mem {n : ℕ} {S : Finset (Fin 4 → ℤ)} (hS : S ∈ wShell n) :
    S = {wV} ∧ n = 1 := by
  by_cases hn : n = 1
  · subst hn
    simp [wShell] at hS
    exact ⟨hS, rfl⟩
  · simp [wShell, hn] at hS

theorem wAct_ne_zero (S : Finset (Fin 4 → ℤ)) : wAct S ≠ 0 :=
  ne_of_gt (Real.exp_pos _)

/-- **The volume-form hypothesis package is inhabited**, so
`cmp116_block_marked_shell_energy_geometric` is not vacuous. -/
theorem cmp116_volume_package_inhabited (n : ℕ) :
    ∑ S ∈ wShell n, |wAct S|
      ≤ (((1 : ℝ) * markCost 0 (cmp116BlockRate 30) lattice4EntropyRate) * 2)
          * shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate 30) lattice4EntropyRate) ^ n := by
  refine cmp116_block_marked_shell_energy_geometric (A := 1) (kappa1 := 30) (M := 1) (m := 0)
    (vol := wVol) (v := wV) Nat.one_pos ?_ ?_ ?_ (by norm_num) ?_ n
  · intro k S hS
    obtain ⟨hSeq, hk⟩ := wShell_mem hS
    subst hSeq; subst hk
    exact ⟨isAnimal_singleton _ _, by simp⟩
  · intro k S hS
    obtain ⟨hSeq, hk⟩ := wShell_mem hS
    subst hSeq; subst hk
    simp [wVol]
  · intro k S hS
    obtain ⟨hSeq, hk⟩ := wShell_mem hS
    subst hSeq; subst hk
    simp only [wAct, wVol, abs_of_pos (Real.exp_pos _)]
    norm_num
  · have := cmp116_threshold_lt_22
    linarith

end CMP116RateChecks

/-! ## Axiom audit -/

#print axioms cmp116BlockRate_exceeds_entropy
#print axioms cmp116_threshold_lt_22
#print axioms cmp116_block_activity_bound
#print axioms cmp116_block_marked_shell_energy_geometric
#print axioms cmp116_block_marked_shell_energy_tsum_le
#print axioms cmp116_tree_activity_bound
#print axioms cmp116_tree_marked_shell_energy_geometric
#print axioms cmp116TreeRate_exceeds_entropy
#print axioms CMP116RateChecks.cmp116_volume_package_inhabited

end YangMills
