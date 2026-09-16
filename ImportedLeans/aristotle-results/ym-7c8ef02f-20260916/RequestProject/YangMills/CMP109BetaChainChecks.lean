/-
# Non-vacuity and sharpness checks for the source-facing chain

Each theorem of the chain built in this round is an identity whose hypotheses
could in principle be unsatisfiable, or whose conclusion could be trivially
zero.  This file rules that out with worked instances, and it records one
sharpness test showing that the third-order hypothesis of the beta projection is
load-bearing rather than decorative.

* `hessian_instance_nonzero` — the trace-log Hessian is genuinely computed: on a
  2×2 instance it takes the nonzero value `1`.
* `deriv_phat_zero`, `mixedD_secondOrder_ne_zero` — the beta projection of a
  *second*-order lattice-derivative term is `4π² ≠ 0`.  So the hypothesis
  `a + b = 3` in `betaProjection_kills_thirdOrder` cannot be weakened to
  `a + b = 2`: the theorem is not an artefact of the mixed derivative being
  identically zero.
* `ward_instance_nontrivial`, `ward_instance_nonzero_longitudinal` — the
  constrained propagator of an actual constraint is nonzero, the reduced block is
  invertible, and the Ward cancellation still applies to a *nonzero* longitudinal
  variation.  So `betaTrace_eq_zero_of_longitudinal` is not vacuous.
-/
import RequestProject.YangMills.CMP109BetaChain

namespace YangMills

open Matrix Real

/-- The Gaussian trace-log Hessian is nonzero on an explicit instance:
`A = 1`, `V₁ = V₂ = 1`, `S = 0` on a two-dimensional carrier gives `1`. -/
theorem hessian_instance_nonzero :
    deriv (fun x : ℝ => deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log (((1 : Matrix (Fin 2) (Fin 2) ℝ) + x • 1 + t • 1
        + (x * t) • 0).det) + 0) 0) 0 = 1 := by
  have hA : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
  rw [gaussianHessian_eq_betaTrace (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 0 hA 0]
  simp [betaTrace, Matrix.trace_one]

/-- The literal lattice factor has slope `2π` at zero momentum. -/
theorem deriv_phat_zero : deriv phat 0 = 2 * π := by
  have h : HasDerivAt (fun x : ℝ => π * x) π 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul π
  have h2 : HasDerivAt phat (2 * (Real.cos (π * 0) * π)) 0 :=
    ((Real.hasDerivAt_sin (π * 0)).comp 0 h).const_mul 2
  simpa [phat, sinAtom] using h2.deriv

/-- **Sharpness of the third-order hypothesis.**  A term with only *two* lattice
derivative factors survives the beta projection with the nonzero value `4π²`. -/
theorem mixedD_secondOrder_ne_zero :
    mixedD (fun s t => phat s * phat t) = 4 * π ^ 2 := by
  have hin : ∀ s : ℝ, deriv (fun t => phat s * phat t) 0 = phat s * (2 * π) := by
    intro s
    rw [deriv_const_mul_field, deriv_phat_zero]
  rw [mixedD, funext hin, deriv_mul_const (differentiableAt_phat 0), deriv_phat_zero]
  ring

/-- A concrete constraint: one linear condition on a two-dimensional carrier. -/
def testConstraint : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

lemma testConstraint_block :
    testConstraint * (1 : Matrix (Fin 2) (Fin 2) ℝ) * testConstraintᵀ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [testConstraint, Matrix.mul_apply]

lemma testConstraint_block_det :
    (testConstraint * (1 : Matrix (Fin 2) (Fin 2) ℝ) * testConstraintᵀ).det ≠ 0 := by
  rw [testConstraint_block]; simp

/-- The constrained propagator of an actual constraint is not the zero matrix, so
the annihilation identities `Q G = 0`, `G Qᵀ = 0` are not vacuous. -/
theorem ward_instance_nontrivial :
    constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testConstraint ≠ 0 := by
  intro h
  have h11 : constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testConstraint 1 1 = 0 := by
    rw [h]; rfl
  rw [constrainedPropagator, testConstraint_block] at h11
  simp [testConstraint, Matrix.mul_apply] at h11

/-- The Ward cancellation applies to a *nonzero* longitudinal variation: with
`V₁ = S = Qᵀ Q ≠ 0` the bubble-minus-seagull functional vanishes. -/
theorem ward_instance_nonzero_longitudinal (V₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    testConstraintᵀ * testConstraint ≠ 0 ∧
      betaTrace (constrainedPropagator (1 : Matrix (Fin 2) (Fin 2) ℝ) testConstraint)
        (testConstraintᵀ * testConstraint) V₂ (testConstraintᵀ * testConstraint) = 0 := by
  constructor
  · intro h
    have h00 : (testConstraintᵀ * testConstraint) 0 0 = 0 := by rw [h]; rfl
    simp [testConstraint, Matrix.mul_apply] at h00
  · exact constrainedPropagator_ward (1 : Matrix (Fin 2) (Fin 2) ℝ) testConstraint
      testConstraint_block_det rfl rfl V₂

/-- **The read-off is not vacuous, and it is not zero.**  For the polarisation
`Π(p) = β·p̂_0 p̂_1 + p̂_0² p̂_1` — marginal term plus a genuine third-order
remainder — the beta projection returns exactly `β` times the projection of the
marginal term, namely `β·4π²`.  Both hypotheses and conclusion are inhabited by
an explicit function, and the remainder really is invisible to the projection
even though it is nonzero. -/
theorem readoff_instance (beta : ℝ) :
    mixedMomentumD
      (fun p => beta * (phat (p 0) * phat (p 1)) + phat (p 0) ^ 2 * phat (p 1)) 0 1
      = beta * (4 * π ^ 2) := by
  have h0 : ∀ x t : ℝ, momentumSlice 0 1 x t 0 = x := by intro x t; simp [momentumSlice]
  have h1 : ∀ x t : ℝ, momentumSlice 0 1 x t 1 = t := by intro x t; simp [momentumSlice]
  have hMfun : (fun x t => phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1))
      = fun x t : ℝ => phat x * phat t := by
    funext x t; rw [h0, h1]
  have hM : ∀ x : ℝ, DifferentiableAt ℝ
      (fun t => phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1)) 0 := by
    intro x
    have he : (fun t => phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1))
        = fun t => phat x * phat t := by funext t; rw [h0, h1]
    rw [he]
    exact (differentiableAt_phat 0).const_mul _
  have hM' : DifferentiableAt ℝ (fun x => deriv (fun t =>
      phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1)) 0) 0 := by
    have he : (fun x : ℝ => deriv (fun t =>
        phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1)) 0)
        = fun x : ℝ => phat x * (2 * π) := by
      funext x
      have hx : (fun t => phat (momentumSlice 0 1 x t 0) * phat (momentumSlice 0 1 x t 1))
          = fun t => phat x * phat t := by funext t; rw [h0, h1]
      rw [hx, deriv_const_mul_field, deriv_phat_zero]
    rw [he]
    exact (differentiableAt_phat 0).mul_const _
  have hkey := beta_readoff_thirdOrder
    (Pi := fun p => beta * (phat (p 0) * phat (p 1)) + phat (p 0) ^ 2 * phat (p 1))
    (M := fun p => phat (p 0) * phat (p 1))
    (R := fun p => phat (p 0) ^ 2 * phat (p 1))
    (mu := 0) (nu := 1) (beta := beta) (g := fun _ _ => 1) (a := 2) (b := 1)
    (fun p => rfl) (by norm_num)
    (by intro x t; simp only []; rw [h0, h1]; ring)
    (fun x => differentiableAt_const _) (by simp) (by simp)
    hM hM'
  rw [hkey]
  congr 1
  rw [mixedMomentumD, hMfun]
  exact mixedD_secondOrder_ne_zero

end YangMills
