import Mathlib
import RequestProject.NavierStokes.R571PairedSecondMoment

noncomputable section

namespace RequestProject.NavierStokes.R571StateVariation

open RequestProject.NavierStokes.R571

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz bound on the transported scalar state pays the R571 two-point
state-difference leaf.  The factor 2 is geometric: the two samples are k+y and
k-y, whose separation is 2‖y‖. -/
theorem stateDerivativeEnvelope_of_lipschitz
    {g : E → ℝ} {k y : E} {g1 : ℝ} {K : NNReal}
    (hg1 : ∀ x, |g x| ≤ g1)
    (hLip : LipschitzWith K g) :
    StateDerivativeEnvelope g1 (2 * (K : ℝ))
      (g (k + y)) (g (k - y)) ‖y‖ := by
  have hg1_nonneg : 0 ≤ g1 := by
    have h := hg1 k
    exact le_trans (abs_nonneg (g k)) h
  have hdist : dist (k + y) (k - y) = 2 * ‖y‖ := by
    rw [dist_eq_norm]
    have hsub : (k + y) - (k - y) = (2 : ℝ) • y := by
      module
    rw [hsub, norm_smul]
    norm_num
  have hdiff := hLip.dist_le_mul (k + y) (k - y)
  rw [Real.dist_eq, hdist] at hdiff
  refine
    { g1_nonneg := hg1_nonneg
      g2_nonneg := by positivity
      plus_le := hg1 (k + y)
      minus_le := hg1 (k - y)
      difference_le := ?_ }
  nlinarith

/-- The R571 pointwise payment with G2 discharged by a genuine Lipschitz
estimate on the transported state.  The only state hypotheses left are a
uniform amplitude envelope and a Lipschitz constant. -/
theorem r571_pairedSecondMoment_of_lipschitzState
    [InnerProductSpace ℝ E]
    (s : DASHI.NS.Unforced.HelicitySign)
    {k y : E} {w g1 : ℝ} {K : NNReal} {g : E → ℝ}
    (hw : 0 ≤ w) (hk : 1 ≤ ‖k‖)
    (hg1 : ∀ x, |g x| ≤ g1)
    (hLip : LipschitzWith K g) :
    w * (|radialSymbol s (k + y) - radialSymbol s k|
            * |g (k + y) - g (k - y)|
          + |centeredRadialDefect s k y| * |g (k - y)|)
      ≤ w * (‖y‖ * ‖y‖) * (2 * (K : ℝ) + g1) := by
  exact r571_pairedSecondMoment_of_stateEnvelope s hw hk
    (stateDerivativeEnvelope_of_lipschitz hg1 hLip)

/-- Finite-family form.  Crucially the state constants are outside the finite
sum, so no Galerkin-cardinality factor is introduced. -/
theorem r571_finite_pairedSecondMoment_of_lipschitzState
    [InnerProductSpace ℝ E]
    {ι : Type*} (fam : Finset ι)
    (sgn : ι → DASHI.NS.Unforced.HelicitySign)
    (kv yv : ι → E) (w : ι → ℝ)
    (g : ι → E → ℝ) {g1 : ℝ} {K : NNReal}
    (hw : ∀ i ∈ fam, 0 ≤ w i)
    (hk : ∀ i ∈ fam, 1 ≤ ‖kv i‖)
    (hg1 : ∀ i ∈ fam, ∀ x, |g i x| ≤ g1)
    (hLip : ∀ i ∈ fam, LipschitzWith K (g i)) :
    ∑ i ∈ fam, w i *
        (|radialSymbol (sgn i) (kv i + yv i) - radialSymbol (sgn i) (kv i)|
            * |g i (kv i + yv i) - g i (kv i - yv i)|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |g i (kv i - yv i)|)
      ≤ (2 * (K : ℝ) + g1)
          * ∑ i ∈ fam, w i * (‖yv i‖ * ‖yv i‖) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := r571_pairedSecondMoment_of_lipschitzState
    (sgn i) (hw i hi) (hk i hi) (hg1 i hi) (hLip i hi)
  calc
    w i *
        (|radialSymbol (sgn i) (kv i + yv i) - radialSymbol (sgn i) (kv i)|
            * |g i (kv i + yv i) - g i (kv i - yv i)|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |g i (kv i - yv i)|)
        ≤ w i * (‖yv i‖ * ‖yv i‖) * (2 * (K : ℝ) + g1) := h
    _ = (2 * (K : ℝ) + g1) * (w i * (‖yv i‖ * ‖yv i‖)) := by ring

end RequestProject.NavierStokes.R571StateVariation
