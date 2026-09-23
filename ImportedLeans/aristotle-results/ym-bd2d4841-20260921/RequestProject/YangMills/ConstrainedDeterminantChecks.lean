/-
# Boundary tests for the constrained-determinant round

Every theorem of this round is an identity or an inequality about supplied data,
so the honest question is whether the statements have content or are satisfied
trivially.  The following instances answer that, by exhibiting concrete numbers.

Take the two-dimensional fluctuation space with the unconstrained propagator
`G̃ = 1` and the single constraint `Q = (1, 0)`.

* `constrainedPropagator_example` — the Schur formula really does project:
  `G = diag(0,1) ≠ G̃`.
* `borderedDeterminant_example` — the bordered determinant is `−1`, in
  particular nonzero, so the constrained Gaussian of this instance exists and
  the factorisation `det Â = (−1)^{#constraints} det Δ det(QΔ⁻¹Qᵀ)` is not read
  off a degenerate case.
* `constraintSector_ne_zero` — the constraint (ghost) sector of
  `betaTrace_constrained_split` is *not* identically zero: here the constrained
  functional is `1/2` and the unconstrained one is `1`, so the automatic
  gauge/constraint subtraction carries the value `−1/2`.
* `ward_shift_nonzero` — the longitudinal shift used in the Ward reduction is a
  genuinely nonzero matrix, so `brillouinIntegrand_ward` is not invariance under
  adding zero.
* `betaTrace_neg_of_seagull` — the seagull hypothesis in
  `betaTrace_nonneg_of_seagull_nonpos` cannot be dropped: with `V = 0` and
  `S = 1` the functional is `−1 < 0`.
-/
import RequestProject.YangMills.CMP109SymbolChain

namespace YangMills

open Matrix

/-- The constraint of the worked instance: a single condition on a
two-dimensional fluctuation space. -/
def testQ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

theorem testQ_reduced : testQ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * testQᵀ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [testQ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Schur projection is a genuine projection: `G = diag(0,1) ≠ G̃ = 1`. -/
theorem constrainedPropagator_example :
    constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testQ = !![0, 0; 0, 1] := by
  rw [constrainedPropagator, testQ_reduced]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [testQ, Matrix.mul_apply]

theorem constrainedPropagator_ne_unconstrained :
    constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testQ
      ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [constrainedPropagator_example]
  intro h
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp at this

theorem testQ_reduced_inv : (testQ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * testQᵀ).det = 1 := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = 1 from Matrix.inv_eq_right_inv (by simp),
    testQ_reduced, Matrix.det_one]

/-- The bordered determinant of the instance is `−1`: nonzero, so the
constrained Gaussian is nondegenerate. -/
theorem borderedDeterminant_example :
    (borderedOperator (1 : Matrix (Fin 2) (Fin 2) ℝ) testQ).det = -1 := by
  rw [borderedOperator_det _ _ (by simp), testQ_reduced_inv]
  simp

/-- The constrained one-loop functional of the instance is `1/2`. -/
theorem betaTrace_constrained_example :
    betaTrace (constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testQ) 1 1 0
      = 1 / 2 := by
  rw [constrainedPropagator_example, betaTrace]
  norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The unconstrained one-loop functional of the instance is `1`. -/
theorem betaTrace_unconstrained_example :
    betaTrace (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 0 = 1 := by
  rw [betaTrace]
  norm_num [Matrix.trace_fin_two, Matrix.one_apply]

/-- **The constraint (ghost) sector is not identically zero.**  The automatic
gauge/constraint subtraction of `betaTrace_constrained_split` carries the value
`−1/2` on this instance. -/
theorem constraintSector_ne_zero :
    betaTrace (constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testQ) 1 1 0
      ≠ betaTrace (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 0 := by
  rw [betaTrace_constrained_example, betaTrace_unconstrained_example]
  norm_num

/-- The longitudinal shift used in the Ward reduction is a nonzero matrix, so
the invariance statement is not invariance under adding zero. -/
theorem ward_shift_nonzero :
    testQᵀ * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) ≠ (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [testQ, Matrix.mul_apply] at this

/-- The seagull hypothesis cannot be dropped: with a vanishing first variation
and `S = 1` the functional is negative. -/
theorem betaTrace_neg_of_seagull :
    betaTrace (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 1 = -1 := by
  rw [betaTrace]
  norm_num [Matrix.trace_fin_two, Matrix.one_apply]

end YangMills
