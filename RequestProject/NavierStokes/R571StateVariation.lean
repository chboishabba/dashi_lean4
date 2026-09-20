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

/-- A uniform Fréchet-derivative bound pays the Lipschitz hypothesis by
Mathlib's mean-value inequality.  This is the analytic form wanted by the
R290/R503 state-derivative slot. -/
theorem stateDerivativeEnvelope_of_fderivBound
    {g : E → ℝ} {k y : E} {g1 : ℝ} {K : NNReal}
    (hg1 : ∀ x, |g x| ≤ g1)
    (hDiff : Differentiable ℝ g)
    (hDeriv : ∀ x, ‖fderiv ℝ g x‖₊ ≤ K) :
    StateDerivativeEnvelope g1 (2 * (K : ℝ))
      (g (k + y)) (g (k - y)) ‖y‖ := by
  exact stateDerivativeEnvelope_of_lipschitz hg1
    (lipschitzWith_of_nnnorm_fderiv_le hDiff hDeriv)

/-- R571 pointwise second-moment payment directly from a uniform derivative
bound on the transported state.  At this point G2 is no longer an independent
two-point assumption: it is 2K, with K the operator-norm bound on fderiv g. -/
theorem r571_pairedSecondMoment_of_fderivBound
    [InnerProductSpace ℝ E]
    (s : DASHI.NS.Unforced.HelicitySign)
    {k y : E} {w g1 : ℝ} {K : NNReal} {g : E → ℝ}
    (hw : 0 ≤ w) (hk : 1 ≤ ‖k‖)
    (hg1 : ∀ x, |g x| ≤ g1)
    (hDiff : Differentiable ℝ g)
    (hDeriv : ∀ x, ‖fderiv ℝ g x‖₊ ≤ K) :
    w * (|radialSymbol s (k + y) - radialSymbol s k|
            * |g (k + y) - g (k - y)|
          + |centeredRadialDefect s k y| * |g (k - y)|)
      ≤ w * (‖y‖ * ‖y‖) * (2 * (K : ℝ) + g1) := by
  exact r571_pairedSecondMoment_of_stateEnvelope s hw hk
    (stateDerivativeEnvelope_of_fderivBound hg1 hDiff hDeriv)

/-- Finite-family derivative form.  This is the source shape needed by a
same-object R290/R503 adapter: one cutoff-independent derivative bound K and
one amplitude envelope g1 suffice for every cell. -/
theorem r571_finite_pairedSecondMoment_of_fderivBound
    [InnerProductSpace ℝ E]
    {ι : Type*} (fam : Finset ι)
    (sgn : ι → DASHI.NS.Unforced.HelicitySign)
    (kv yv : ι → E) (w : ι → ℝ)
    (g : ι → E → ℝ) {g1 : ℝ} {K : NNReal}
    (hw : ∀ i ∈ fam, 0 ≤ w i)
    (hk : ∀ i ∈ fam, 1 ≤ ‖kv i‖)
    (hg1 : ∀ i ∈ fam, ∀ x, |g i x| ≤ g1)
    (hDiff : ∀ i ∈ fam, Differentiable ℝ (g i))
    (hDeriv : ∀ i ∈ fam, ∀ x, ‖fderiv ℝ (g i) x‖₊ ≤ K) :
    ∑ i ∈ fam, w i *
        (|radialSymbol (sgn i) (kv i + yv i) - radialSymbol (sgn i) (kv i)|
            * |g i (kv i + yv i) - g i (kv i - yv i)|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |g i (kv i - yv i)|)
      ≤ (2 * (K : ℝ) + g1)
          * ∑ i ∈ fam, w i * (‖yv i‖ * ‖yv i‖) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := r571_pairedSecondMoment_of_fderivBound
    (sgn i) (hw i hi) (hk i hi) (hg1 i hi)
    (hDiff i hi) (hDeriv i hi)
  calc
    w i *
        (|radialSymbol (sgn i) (kv i + yv i) - radialSymbol (sgn i) (kv i)|
            * |g i (kv i + yv i) - g i (kv i - yv i)|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |g i (kv i - yv i)|)
        ≤ w i * (‖yv i‖ * ‖yv i‖) * (2 * (K : ℝ) + g1) := h
    _ = (2 * (K : ℝ) + g1) * (w i * (‖yv i‖ * ‖yv i‖)) := by ring

/-! ## Periodic lattice shortcut: G2 follows from G1

On the periodic integer Fourier lattice every nonzero displacement has norm at
least one.  Therefore no differentiability in the frequency index is needed:
the triangle inequality alone turns the already-required amplitude envelope
G1 into the difference envelope G2 = 2*G1.
-/

/-- If both opposite samples are bounded by G1 and the displacement magnitude
is at least one, the complete R571 state envelope holds with G2 = 2*G1.

This is the exact observation
  |g+ - g-| <= |g+| + |g-| <= 2 G1 <= y (2 G1).
It is particularly suited to T^3, where a nonzero integer Fourier displacement
has norm at least one. -/
theorem stateDerivativeEnvelope_of_amplitude_of_one_le_displacement
    {g1 gPlus gMinus y : ℝ}
    (hg1 : 0 ≤ g1)
    (hy : 1 ≤ y)
    (hPlus : |gPlus| ≤ g1)
    (hMinus : |gMinus| ≤ g1) :
    StateDerivativeEnvelope g1 (2 * g1) gPlus gMinus y := by
  have hdiff : |gPlus - gMinus| ≤ 2 * g1 := by
    calc
      |gPlus - gMinus| ≤ |gPlus| + |gMinus| := abs_sub _ _
      _ ≤ g1 + g1 := add_le_add hPlus hMinus
      _ = 2 * g1 := by ring
  refine
    { g1_nonneg := hg1
      g2_nonneg := by positivity
      plus_le := hPlus
      minus_le := hMinus
      difference_le := ?_ }
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  nlinarith

/-- Norm-specialized form: a nontrivial opposite shift with norm >= 1 pays the
G2 leaf from G1 alone. -/
theorem stateDerivativeEnvelope_of_amplitude_of_one_le_norm
    {E : Type*} [SeminormedAddCommGroup E]
    {g1 gPlus gMinus : ℝ} {y : E}
    (hg1 : 0 ≤ g1)
    (hy : 1 ≤ ‖y‖)
    (hPlus : |gPlus| ≤ g1)
    (hMinus : |gMinus| ≤ g1) :
    StateDerivativeEnvelope g1 (2 * g1) gPlus gMinus ‖y‖ :=
  stateDerivativeEnvelope_of_amplitude_of_one_le_displacement
    hg1 hy hPlus hMinus

/-- Consequently the R571 radial payment needs only G1 on a lattice-scale
nonzero displacement.  The coefficient becomes G2+G1 = 3*G1. -/
theorem r571_pairedSecondMoment_of_amplitude_of_one_le_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : DASHI.NS.Unforced.HelicitySign)
    {k y : E} {w g1 gPlus gMinus : ℝ}
    (hw : 0 ≤ w)
    (hk : 1 ≤ ‖k‖)
    (hy : 1 ≤ ‖y‖)
    (hg1 : 0 ≤ g1)
    (hPlus : |gPlus| ≤ g1)
    (hMinus : |gMinus| ≤ g1) :
    w * (|radialSymbol s (k + y) - radialSymbol s k|
            * |gPlus - gMinus|
          + |centeredRadialDefect s k y| * |gMinus|)
      ≤ w * (‖y‖ * ‖y‖) * (3 * g1) := by
  have hstate :
      StateDerivativeEnvelope g1 (2 * g1) gPlus gMinus ‖y‖ :=
    stateDerivativeEnvelope_of_amplitude_of_one_le_norm
      hg1 hy hPlus hMinus
  have h := r571_pairedSecondMoment_of_stateEnvelope s hw hk hstate
  convert h using 1 <;> ring

/-- Finite-family form with one cutoff-independent G1 envelope.  This removes
the independent G2 hypothesis entirely. -/
theorem r571_finite_pairedSecondMoment_of_amplitude_of_one_le_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (fam : Finset ι)
    (sgn : ι → DASHI.NS.Unforced.HelicitySign)
    (kv yv : ι → E) (w gPlus gMinus : ι → ℝ) {g1 : ℝ}
    (hw : ∀ i ∈ fam, 0 ≤ w i)
    (hk : ∀ i ∈ fam, 1 ≤ ‖kv i‖)
    (hy : ∀ i ∈ fam, 1 ≤ ‖yv i‖)
    (hg1 : 0 ≤ g1)
    (hPlus : ∀ i ∈ fam, |gPlus i| ≤ g1)
    (hMinus : ∀ i ∈ fam, |gMinus i| ≤ g1) :
    ∑ i ∈ fam, w i *
        (|radialSymbol (sgn i) (kv i + yv i)
            - radialSymbol (sgn i) (kv i)|
            * |gPlus i - gMinus i|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |gMinus i|)
      ≤ (3 * g1) * ∑ i ∈ fam, w i * (‖yv i‖ * ‖yv i‖) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := r571_pairedSecondMoment_of_amplitude_of_one_le_norm
    (sgn i) (hw i hi) (hk i hi) (hy i hi) hg1
    (hPlus i hi) (hMinus i hi)
  calc
    w i *
        (|radialSymbol (sgn i) (kv i + yv i)
            - radialSymbol (sgn i) (kv i)|
            * |gPlus i - gMinus i|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)|
            * |gMinus i|)
        ≤ w i * (‖yv i‖ * ‖yv i‖) * (3 * g1) := h
    _ = (3 * g1) * (w i * (‖yv i‖ * ‖yv i‖)) := by ring

end RequestProject.NavierStokes.R571StateVariation
