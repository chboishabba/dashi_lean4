import Mathlib

noncomputable section

namespace RequestProject.NavierStokes.R571VectorStateVariation

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Mean-value theorem on the literal opposite-shift geometry.  A uniform
Fréchet-derivative norm bound K on a transported vector field X gives

  ‖X(k+y) - X(k-y)‖ ≤ 2 K ‖y‖.

This is the continuum segment version of the finite-path Cauchy donor and is
the exact state-variation shape required by the R571 G2 leaf. -/
theorem oppositeShift_variation_of_fderivBound
    {X : E → V} {k y : E} {K : NNReal}
    (hDiff : Differentiable ℝ X)
    (hDeriv : ∀ x, ‖fderiv ℝ X x‖₊ ≤ K) :
    ‖X (k + y) - X (k - y)‖ ≤ 2 * (K : ℝ) * ‖y‖ := by
  have hLip : LipschitzWith K X :=
    lipschitzWith_of_nnnorm_fderiv_le hDiff hDeriv
  have h := hLip.dist_le_mul (k + y) (k - y)
  have hdist : dist (k + y) (k - y) = 2 * ‖y‖ := by
    rw [dist_eq_norm]
    have hsub : (k + y) - (k - y) = (2 : ℝ) • y := by
      module
    rw [hsub, norm_smul]
    norm_num
  rw [dist_eq_norm, hdist] at h
  nlinarith

/-- Squared form, matching the Agda
VectorStateDifferenceSquaredEnvelope interface. -/
theorem oppositeShift_variation_sq_of_fderivBound
    {X : E → V} {k y : E} {K : NNReal}
    (hDiff : Differentiable ℝ X)
    (hDeriv : ∀ x, ‖fderiv ℝ X x‖₊ ≤ K) :
    ‖X (k + y) - X (k - y)‖ ^ 2
      ≤ ‖y‖ ^ 2 * (2 * (K : ℝ)) ^ 2 := by
  have h := oppositeShift_variation_of_fderivBound
    (X := X) (k := k) (y := y) hDiff hDeriv
  have hleft : 0 ≤ ‖X (k + y) - X (k - y)‖ := norm_nonneg _
  have hright : 0 ≤ 2 * (K : ℝ) * ‖y‖ := by positivity
  have hsquare :=
    pow_le_pow_left₀ hleft h 2
  calc
    ‖X (k + y) - X (k - y)‖ ^ 2
        ≤ (2 * (K : ℝ) * ‖y‖) ^ 2 := hsquare
    _ = ‖y‖ ^ 2 * (2 * (K : ℝ)) ^ 2 := by ring

/-- Local convex-set version.  This is the form needed when the transported
state is only controlled on an annular/interaction cell rather than globally. -/
theorem oppositeShift_variation_of_fderivBound_on
    {X : E → V} {k y : E} {K : NNReal} {s : Set E}
    (hs : Convex ℝ s)
    (hplus : k + y ∈ s)
    (hminus : k - y ∈ s)
    (hDiff : ∀ x ∈ s, DifferentiableAt ℝ X x)
    (hDeriv : ∀ x ∈ s, ‖fderiv ℝ X x‖₊ ≤ K) :
    ‖X (k + y) - X (k - y)‖ ≤ 2 * (K : ℝ) * ‖y‖ := by
  have hLip : LipschitzOnWith K X s :=
    hs.lipschitzOnWith_of_nnnorm_fderiv_le hDiff hDeriv
  have h := hLip.dist_le_mul hplus hminus
  have hdist : dist (k + y) (k - y) = 2 * ‖y‖ := by
    rw [dist_eq_norm]
    have hsub : (k + y) - (k - y) = (2 : ℝ) • y := by
      module
    rw [hsub, norm_smul]
    norm_num
  rw [dist_eq_norm, hdist] at h
  nlinarith

end RequestProject.NavierStokes.R571VectorStateVariation
