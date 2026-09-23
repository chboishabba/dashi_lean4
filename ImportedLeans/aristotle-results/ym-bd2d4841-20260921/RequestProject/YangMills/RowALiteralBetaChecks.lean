/-
# Axiom and sharpness checks for the Row-A literal beta sensitivity lane

This file records the machine checks for the Row-A sensitivity development:

* every top-level theorem of the lane depends only on the three standard Lean
  axioms `propext`, `Classical.choice`, `Quot.sound` — no new postulate, no
  `sorry`, no imported authority;
* the witness of `RowALiteralBetaWitness` is not degenerate: the shell
  coefficient genuinely depends on the coupling, and the derived marginal
  sensitivity weight is strictly positive.  So the contraction constant of the
  witness is produced by an actual direct channel sensitivity, not by a
  vanishing one.
-/
import RequestProject.YangMills.RowALiteralBetaWitness
import RequestProject.YangMills.IrrelevantHistoryDuhamel

namespace YangMills
namespace RowAWitness

/-! ## 1. The witness is non-degenerate -/

/-- The witness shell coefficient really varies with the coupling: the direct
sensitivity that the lane estimates is nonzero. -/
theorem shell_nonconstant : shell 0 100 (1 / 10) ≠ shell 0 100 0 := by
  rw [shell_eq, shell_eq]
  norm_num

/-- The derived marginal weight of the witness is strictly positive at every
scale, so the response kernel has a genuinely nonzero diagonal. -/
theorem marginalWeight_pos (j : ℕ) :
    0 < literalMarginalWeight (1 / 100) 100 (1 - 1 / 1000) j := by
  have hx : (0 : ℝ) < 100 + (1 - 1 / 1000) * j := by positivity
  rw [literalMarginalWeight]
  positivity

/-- The kernel mass of the witness is strictly positive: the contraction is a
genuine estimate, not the trivial `q = 0`. -/
theorem kernelMass_pos : 0 < literalKernelMass (1 / 100) 0 0 100 (1 - 1 / 1000) := by
  rw [literalKernelMass]
  norm_num

end RowAWitness

/-! ## 2. The Duhamel response bound is not vacuous -/

namespace DuhamelWitness

/-- A genuinely contracting irrelevant map, driven by the coupling. -/
noncomputable def Rmap : ℕ → ℝ → ℝ → ℝ := fun _ g x => (1 / 2) * x + g

/-- The irrelevant state it generates from a common initial value. -/
noncomputable def rstate : ℕ → ℝ → ℝ
  | 0, _ => 0
  | (j + 1), p => Rmap j p (rstate j p)

theorem contraction (j : ℕ) (g x y : ℝ) : ‖Rmap j g x - Rmap j g y‖ ≤ (1 / 2) * ‖x - y‖ := by
  have h : Rmap j g x - Rmap j g y = (1 / 2) * (x - y) := by simp [Rmap]; ring
  rw [h, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  norm_num

theorem drive (j : ℕ) (a b x : ℝ) : ‖Rmap j a x - Rmap j b x‖ ≤ 1 * |a - b| := by
  have h : Rmap j a x - Rmap j b x = a - b := by simp [Rmap]
  rw [h, Real.norm_eq_abs]
  norm_num

/-- The Duhamel bound applies to a genuinely nonzero, genuinely contracting
response. -/
theorem duhamel_witness (j : ℕ) (p q : ℝ) :
    ‖rstate j p - rstate j q‖
      ≤ ∑ k ∈ Finset.range j, (1 / 2 : ℝ) ^ (j - 1 - k) * 1 * |p - q| :=
  irrelevant_response_duhamel (R := Rmap) (r := rstate) (u := fun _ p => p)
    (thmem := 1 / 2) (D := fun _ => 1)
    (fun _ _ => rfl) (fun _ _ => rfl) contraction drive (by norm_num) j p q

/-- …and the response it bounds is itself nonzero, so the estimate is not the
trivial `0 ≤ 0`. -/
theorem duhamel_response_nonzero : rstate 1 1 - rstate 1 0 = 1 := by
  simp [rstate, Rmap]

end DuhamelWitness

/-! ## 3. Axiom checks -/

section AxiomChecks

-- differentiated source majorants
#print axioms abs_logDetChannel_sub_le
#print axioms abs_tailPolyChannel_sub_le
#print axioms abs_frozenShellInteraction_sub_le

-- the shooting coordinate `u = g⁻²`
#print axioms abs_couplingOf_sub_le
#print axioms sum_inv_cube_linear_le

-- the response bootstrap
#print axioms trajectory_diff_le_of_kernel
#print axioms cumulative_beta_lipschitz_of_kernel
#print axioms splitKernel_mass_le
#print axioms rowA_completion_of_tube_sensitivity

-- the literal assembly
#print axioms literal_direct_sensitivity
#print axioms literal_sigma_lt_half
#print axioms literal_cumulative_beta_contraction
#print axioms rowA_completion_of_literal_channels

-- the witness
#print axioms RowAWitness.rowA_completion_witness
#print axioms RowAWitness.cumulative_contraction_witness

-- the derived irrelevant history response
#print axioms irrelevant_response_duhamel
#print axioms literal_mem_of_irrelevant_contraction
#print axioms rowA_completion_of_local_rg_data
#print axioms DuhamelWitness.duhamel_witness

end AxiomChecks

end YangMills
