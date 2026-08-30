/-
# The chain: constrained Gaussian normalisation ⟶ finite Brillouin sum of symbols

This module welds the pieces of the recut Row A1a into the single statement a
literal symbol extraction is meant to be fed into.

Assume, at a translation-invariant background:

* the fluctuation operator `Δ` and the constraint `Q`, with the constrained
  Gaussian normalisation `Z = ∫ dB δ(QB) e^{−½⟨B,Δ(s,t)B⟩}`, whose logarithm is
  `−½ log det Â(s,t) + c` for the bordered operator `Â` of
  `ConstrainedDeterminant`;
* the constrained propagator `G = Δ⁻¹ − Δ⁻¹Qᵀ(QΔ⁻¹Qᵀ)⁻¹QΔ⁻¹` and the background
  jets `V₁, V₂, S` are diagonalised by one Fourier transform `F` into
  matrix-valued symbols `g(q), v₁(q), v₂(q), s(q)` on the internal
  (Lorentz ⊗ colour) space.

Then (`constrainedGaussianHessian_brillouin`)

    ∂_s∂_t log Z |₀ = ∑_q I(q),
    I(q) = ½ tr( g(q) v₁(q) g(q) v₂(q) ) − ½ tr( g(q) s(q) ),

an exact finite sum over the Brillouin set `ι`, with `I(q)` the *same*
bubble-minus-seagull functional evaluated on the symbols.  Two further
statements make the reduction usable:

* `brillouinIntegrand_ward` — at each momentum the integrand only depends on the
  jets modulo the longitudinal subspace `{Q(q)ᵀA} + {BQ(q)}`, so a literal jet
  may be normalised modulo the Ward kernel *before* the matrices are multiplied;
* `brillouinIntegrand_bubble_nonneg` — the bubble half of the diagonal integrand
  (`v₁ = v₂ = v` symmetric) is nonnegative at every momentum, because the
  constrained propagator of a Gram covariance is a Gram matrix
  (`ConstrainedPositivity`).  Whatever sign the coefficient has, it is decided
  by the seagull term.

**Provenance.**  Nothing here supplies a literal symbol: `g, v₁, v₂, s` are
data.  The theorems say exactly what a literal extraction buys, and no numerical
value of any beta coefficient is asserted.
-/
import RequestProject.YangMills.ConstrainedDeterminant
import RequestProject.YangMills.BlockBrillouin
import RequestProject.YangMills.WardKernelReduction
import RequestProject.YangMills.ConstrainedPositivity

namespace YangMills

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The scalar Brillouin integrand at one momentum:
`I(q) = ½ tr(g v₁ g v₂) − ½ tr(g s)`.  It is the same bubble-minus-seagull
functional as the operator-level one, evaluated on the symbols. -/
noncomputable def brillouinIntegrand (g v₁ v₂ s : Matrix κ κ ℝ) : ℝ :=
  betaTrace g v₁ v₂ s

/-- **The constrained Gaussian Hessian as a finite Brillouin sum of matrix
symbols.**  For the bordered (constrained) normalisation and Fourier-diagonalised
data,

    ∂_s∂_t ( −½ log det Â(s,t) + c )|₀ = ∑_q I(q). -/
theorem constrainedGaussianHessian_brillouin
    (D V₁ V₂ S : Matrix (κ × ι) (κ × ι) ℝ) (Q : Matrix μ (κ × ι) ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) (c : ℝ)
    {F : Matrix (κ × ι) (κ × ι) ℝ} (hF : F.det ≠ 0)
    (g v₁ v₂ s : ι → Matrix κ κ ℝ)
    (hG : constrainedPropagator D⁻¹ Q = F * blockDiagonal g * F⁻¹)
    (hV₁ : V₁ = F * blockDiagonal v₁ * F⁻¹)
    (hV₂ : V₂ = F * blockDiagonal v₂ * F⁻¹)
    (hS : S = F * blockDiagonal s * F⁻¹) :
    deriv (fun x : ℝ => deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log
        ((borderedOperator (D + x • V₁ + t • V₂ + (x * t) • S) Q).det) + c) 0) 0
      = ∑ q, brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q) := by
  rw [borderedHessian_eq_betaTrace D V₁ V₂ S Q hD hK c]
  exact betaTrace_blockBrillouin hF g v₁ v₂ s hG hV₁ hV₂ hS

omit [DecidableEq κ] in
/-- **The Brillouin integrand only sees the jets modulo the Ward kernel.**  At
each momentum, longitudinal components of the jets may be discarded before any
matrix product is formed. -/
theorem brillouinIntegrand_ward (gt : Matrix κ κ ℝ) (Qq : Matrix μ κ ℝ)
    (h : (Qq * gt * Qqᵀ).det ≠ 0) (v₁ v₂ sq : Matrix κ κ ℝ)
    (A₁ A₂ A₃ : Matrix μ κ ℝ) (B₁ B₂ B₃ : Matrix κ μ ℝ) :
    brillouinIntegrand (constrainedPropagator gt Qq)
        (v₁ + Qqᵀ * A₁ + B₁ * Qq) (v₂ + Qqᵀ * A₂ + B₂ * Qq) (sq + Qqᵀ * A₃ + B₃ * Qq)
      = brillouinIntegrand (constrainedPropagator gt Qq) v₁ v₂ sq :=
  betaTrace_ward_invariant_constrained gt Qq h v₁ v₂ sq A₁ A₂ A₃ B₁ B₂ B₃

/-- **The bubble half of the diagonal integrand is nonnegative at every
momentum.**  With `g̃(q) = B(q)ᵀB(q)` a Gram covariance and a symmetric variation,
the constrained symbol is a Gram matrix and the bubble term is a sum of squares;
so the whole integrand is nonnegative wherever the seagull trace is
nonpositive. -/
theorem brillouinIntegrand_bubble_nonneg (Bq : Matrix κ κ ℝ) (Qq : Matrix μ κ ℝ)
    (hK : (Qq * (Bqᵀ * Bq) * Qqᵀ).det ≠ 0) {v : Matrix κ κ ℝ} (hv : vᵀ = v) :
    0 ≤ (constrainedPropagator (Bqᵀ * Bq) Qq * v * constrainedPropagator (Bqᵀ * Bq) Qq
        * v).trace :=
  trace_bubble_nonneg (constrainedPropagator_gram Bq Qq hK) hv

/-- The diagonal integrand is nonnegative once the seagull trace is
nonpositive. -/
theorem brillouinIntegrand_nonneg_of_seagull_nonpos (Bq : Matrix κ κ ℝ)
    (Qq : Matrix μ κ ℝ) (hK : (Qq * (Bqᵀ * Bq) * Qqᵀ).det ≠ 0)
    {v sq : Matrix κ κ ℝ} (hv : vᵀ = v)
    (hs : (constrainedPropagator (Bqᵀ * Bq) Qq * sq).trace ≤ 0) :
    0 ≤ brillouinIntegrand (constrainedPropagator (Bqᵀ * Bq) Qq) v v sq :=
  betaTrace_nonneg_of_seagull_nonpos (constrainedPropagator_gram Bq Qq hK) hv hs

omit [DecidableEq ι] [DecidableEq κ] in
/-- Summing the pointwise sign criterion: if every momentum contributes
nonnegatively, so does the whole Brillouin sum. -/
theorem brillouinSum_nonneg (g v₁ v₂ s : ι → Matrix κ κ ℝ)
    (h : ∀ q, 0 ≤ brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q)) :
    0 ≤ ∑ q, brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q) :=
  Finset.sum_nonneg fun q _ => h q

omit [DecidableEq ι] [DecidableEq κ] in
/-- A strictly positive floor for the coefficient follows from a strictly
positive floor for the integrand on a nonempty Brillouin set. -/
theorem brillouinSum_ge_of_pointwise [Nonempty ι] (g v₁ v₂ s : ι → Matrix κ κ ℝ)
    {b : ℝ} (h : ∀ q, b ≤ brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q)) :
    (Fintype.card ι : ℝ) * b ≤ ∑ q, brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q) := by
  calc (Fintype.card ι : ℝ) * b = ∑ _q : ι, b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ q, brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q) :=
        Finset.sum_le_sum fun q _ => h q

omit [DecidableEq ι] [DecidableEq κ] in
/-- A strictly positive Brillouin sum from pointwise nonnegativity plus one
strictly positive momentum. -/
theorem brillouinSum_pos_of_exists (g v₁ v₂ s : ι → Matrix κ κ ℝ)
    (hnn : ∀ q, 0 ≤ brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q))
    (q₀ : ι) (hq₀ : 0 < brillouinIntegrand (g q₀) (v₁ q₀) (v₂ q₀) (s q₀)) :
    0 < ∑ q, brillouinIntegrand (g q) (v₁ q) (v₂ q) (s q) :=
  Finset.sum_pos' (fun q _ => hnn q) ⟨q₀, Finset.mem_univ q₀, hq₀⟩

omit [DecidableEq ι] in
/-- **A checkable criterion for a positive Gaussian coefficient `b_Z > 0`.**
Suppose that at every momentum

* the unconstrained symbol is a Gram covariance `g̃(q) = B(q)ᵀB(q)` with an
  invertible reduced constraint block,
* the background variation `v(q)` is symmetric, and
* the seagull trace is nonpositive,

and that at one momentum the constrained propagator does not annihilate the
variation.  Then the whole diagonal Brillouin sum is strictly positive.  This
reduces the A1a target to pointwise conditions on the literal symbols: no global
control over the Brillouin zone and no near/far split is needed. -/
theorem brillouinSum_pos_criterion (Bq : ι → Matrix κ κ ℝ) (Qs : ι → Matrix μ κ ℝ)
    (hK : ∀ q, (Qs q * ((Bq q)ᵀ * Bq q) * (Qs q)ᵀ).det ≠ 0)
    (v s : ι → Matrix κ κ ℝ) (hv : ∀ q, (v q)ᵀ = v q)
    (hs : ∀ q, (constrainedPropagator ((Bq q)ᵀ * Bq q) (Qs q) * s q).trace ≤ 0)
    (q₀ : ι)
    (hq₀ : constrainedPropagator ((Bq q₀)ᵀ * Bq q₀) (Qs q₀) * v q₀
        * constrainedPropagator ((Bq q₀)ᵀ * Bq q₀) (Qs q₀) ≠ 0) :
    0 < ∑ q, brillouinIntegrand (constrainedPropagator ((Bq q)ᵀ * Bq q) (Qs q))
        (v q) (v q) (s q) := by
  refine brillouinSum_pos_of_exists _ _ _ _ (fun q => ?_) q₀ ?_
  · exact betaTrace_nonneg_of_seagull_nonpos
      (constrainedPropagator_gram (Bq q) (Qs q) (hK q)) (hv q) (hs q)
  · exact betaTrace_pos_of_seagull_nonpos
      (constrainedPropagator_gram (Bq q₀) (Qs q₀) (hK q₀)) (hv q₀) hq₀ (hs q₀)

end YangMills
