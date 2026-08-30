/-
# Boundary tests for the seagull sign criterion

`SeagullSign` reduces the sign of the Gaussian coefficient to the sign of the
second background variation.  The following worked instance shows that both
sides of that reduction have content.

The instance is the two-dimensional constrained fluctuation space of
`ConstrainedDeterminantChecks` (`G̃ = 1`, single constraint `Q = (1,0)`, so the
constrained propagator is `G = diag(0,1)`) with a two-element Brillouin set, a
symmetric first variation `v = diag(0,1)` and second variation `s = ∓1`.

* `paramagnetic_instance_integrand` — with the paramagnetic sign `s = −1` the
  integrand is `1` at each momentum, so the Brillouin sum is `2`.
* `paramagnetic_instance_sum_pos` — the same conclusion obtained *through* the
  general criterion `brillouinSum_pos_of_paramagnetic_seagull`, so that theorem
  is instantiable end to end.
* `diamagnetic_instance_integrand` / `diamagnetic_instance_sum_not_pos` — with
  the diamagnetic sign `s = +1` the integrand is `0` and the Brillouin sum is
  *not* positive.  The sign hypothesis on the second variation is therefore
  load-bearing, exactly as `betaTrace_nonpos_of_pure_diamagnetic` predicts.
-/
import RequestProject.YangMills.SeagullSign
import RequestProject.YangMills.ConstrainedDeterminantChecks

namespace YangMills

open Matrix

/-- The unconstrained symbol of the worked instance, `g̃ = 1`, presented as a
Gram matrix. -/
theorem test_gram : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp

/-- The constrained symbol of the worked instance is `diag(0,1)`. -/
theorem test_constrained :
    constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ = !![0, 0; 0, 1] := by
  rw [test_gram, constrainedPropagator_example]

/-- The symmetric first variation of the worked instance. -/
def testV : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

theorem testV_symm : testVᵀ = testV := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [testV]

/-- The constrained propagator does not annihilate the first variation. -/
theorem test_bubble_ne_zero :
    constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ * testV
        * constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ ≠ 0 := by
  rw [test_constrained]
  intro h
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  simp [testV, Matrix.mul_apply, Fin.sum_univ_succ] at this

theorem test_reduced_det :
    (testQ * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) * testQᵀ).det ≠ 0 := by
  rw [test_gram, testQ_reduced, Matrix.det_one]
  norm_num

/-- **Paramagnetic instance.**  With `s = −1 = −(1ᵀ1)` the integrand is `1`. -/
theorem paramagnetic_instance_integrand :
    brillouinIntegrand (constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ)
        testV testV (-((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)) = 1 := by
  rw [brillouinIntegrand, test_constrained, betaTrace, test_gram]
  norm_num [testV, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply]

/-- The Brillouin sum over two momenta is `2`. -/
theorem paramagnetic_instance_sum :
    ∑ _q : Fin 2,
        brillouinIntegrand (constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ)
          testV testV (-((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)) = 2 := by
  rw [Finset.sum_const, paramagnetic_instance_integrand]
  norm_num

/-- **The general paramagnetic criterion is instantiable.**  Applying
`brillouinSum_pos_of_paramagnetic_seagull` to the worked instance gives a
strictly positive Brillouin sum. -/
theorem paramagnetic_instance_sum_pos :
    0 < ∑ _q : Fin 2,
        brillouinIntegrand (constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ)
          testV testV (-((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)) :=
  brillouinSum_pos_of_paramagnetic_seagull (ι := Fin 2) (m := Fin 1)
    (fun _ => 1) (fun _ => testQ) (fun _ => test_reduced_det)
    (fun _ => testV) (fun _ => -((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)) (fun _ => 1)
    (fun _ => testV_symm) (fun _ => rfl) 0 test_bubble_ne_zero

/-- **Diamagnetic instance.**  With `s = +1` the integrand is `0`: bubble and
seagull cancel exactly. -/
theorem diamagnetic_instance_integrand :
    brillouinIntegrand (constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ)
        testV testV ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) = 0 := by
  rw [brillouinIntegrand, test_constrained, betaTrace, test_gram]
  norm_num [testV, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply]

/-- **The sign hypothesis is load-bearing.**  With a diamagnetic second
variation the Brillouin sum of the same instance is not positive. -/
theorem diamagnetic_instance_sum_not_pos :
    ¬ (0 < ∑ _q : Fin 2,
        brillouinIntegrand (constrainedPropagator ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) testQ)
          testV testV ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)) := by
  rw [Finset.sum_const, diamagnetic_instance_integrand]
  norm_num

end YangMills
