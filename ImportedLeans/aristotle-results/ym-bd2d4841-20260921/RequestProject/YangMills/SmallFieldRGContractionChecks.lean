/-
# Row A — non-vacuity and axiom checks for the derived contraction and drive

`SmallFieldRGContraction` derives the two renormalisation-group constants that
Row A previously assumed: the irrelevant contraction factor `θ = L^{−δ} + η` and
the coupling drive strength `D_j = (C_gen/2)g_j⁶`.  A derivation is only worth
having if the objects involved are non-degenerate, so this file records:

* `blockScaling_value` — the rescaling really multiplies by `L^{4−dim}`, with an
  explicit nonzero value: a dimension-six operator at block size `2` is damped by
  exactly `1/4`;
* `blockScaling_contract_sharp` — the derived factor is attained, so `L^{−δ}` is
  not an overestimate that hides a vanishing map;
* `rpow_neg_lt_one_witness` — the factor is genuinely below one;
* `drive_positive` — the derived drive strength is strictly positive at every
  scale for a nonzero generation constant, so the domination inequality is a real
  competition and not a vacuous one;
* the `#print axioms` audit of the derived-contraction lane.
-/
import RequestProject.YangMills.SmallFieldRGContraction

namespace YangMills

namespace ScalingChecks

open Finset

/-- A dimension-six operator at block size two is damped by exactly `1/4`. -/
theorem blockScaling_value (r : Fin 1 → ℝ) :
    blockScaling (2 : ℝ) (fun _ => (6 : ℝ)) r 0 = r 0 / 4 := by
  have h : ((4 : ℝ) - 6) = ((-2 : ℤ) : ℝ) := by norm_num
  rw [blockScaling, h, Real.rpow_intCast]
  norm_num
  ring

/-- The derived contraction factor is attained: the bound `L^{−δ}` of
`blockScaling_contract` is sharp for the dimension-`4+δ` sector. -/
theorem blockScaling_contract_sharp :
    ‖blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 1)
        - blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 0)‖
      = (2 : ℝ) ^ (-(2 : ℝ)) * ‖(fun _ : Fin 1 => (1 : ℝ)) - (fun _ => 0)‖ := by
  have hval : ((2 : ℝ) ^ (-(2 : ℝ))) = 1 / 4 := by
    have h : (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) := by norm_num
    rw [h, Real.rpow_intCast]
    norm_num
  have hL : ‖blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 1)
      - blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 0)‖ = 1 / 4 := by
    have h1 : (blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 1)
        - blockScaling (2 : ℝ) (fun _ : Fin 1 => (6 : ℝ)) (fun _ => 0)) = fun _ => (1 : ℝ) / 4 := by
      funext o
      have ho : o = 0 := Subsingleton.elim _ _
      subst ho
      simp only [Pi.sub_apply]
      rw [blockScaling_value, blockScaling_value]
      norm_num
    rw [h1]
    simp [pi_norm_const]
  have hR : ‖(fun _ : Fin 1 => (1 : ℝ)) - (fun _ => 0)‖ = 1 := by
    have h2 : ((fun _ : Fin 1 => (1 : ℝ)) - (fun _ => 0)) = fun _ => (1 : ℝ) := by
      funext o; simp
    rw [h2]
    simp [pi_norm_const]
  rw [hL, hR, hval]
  norm_num

/-- The derived factor is strictly below one. -/
theorem rpow_neg_lt_one_witness : (2 : ℝ) ^ (-(2 : ℝ)) < 1 :=
  rpow_neg_lt_one (by norm_num) (by norm_num)

/-- The derived drive strength is strictly positive at every scale, so the
domination inequality it must satisfy is a genuine competition. -/
theorem drive_positive (j : ℕ) : 0 < literalMarginalWeight 1 1 1 j := by
  have hx : (0 : ℝ) < 1 + 1 * (j : ℝ) := by positivity
  rw [literalMarginalWeight]
  positivity

/-- The scale-free domination inequality is satisfiable: `L_coef = C_gen = 1`,
`C_dir = 1`, `θ = 1/2` needs only `C_mem ≥ 2`. -/
theorem domination_satisfiable (k : ℕ) :
    (1 : ℝ) * literalMarginalWeight 1 1 1 k ≤ 2 * (1 / 2) * literalMarginalWeight 1 1 1 k :=
  literalMarginalWeight_dominate (by norm_num) (by norm_num) (by norm_num) k

end ScalingChecks

/-! ## Axiom audit -/

#print axioms blockScaling_contract
#print axioms rpow_neg_lt_one
#print axioms rgStep_contract
#print axioms rgStep_theta_lt_one
#print axioms rgStep_drive
#print axioms couplingOf_cube_mul_cube
#print axioms drive_of_cubic_generation
#print axioms literalMarginalWeight_dominate
#print axioms irrelevant_response_duhamel_tube
#print axioms literal_mem_of_tube_contraction
#print axioms exists_constants_for_contraction
#print axioms rowA_completion_of_scaling_rg_data
#print axioms ScalingChecks.blockScaling_contract_sharp
#print axioms ScalingChecks.drive_positive

end YangMills
