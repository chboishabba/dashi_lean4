/-
# Fourier reduction of the one-loop trace to a Brillouin-zone sum

At a translation-invariant background the constrained operator, its propagator
and its variations are all diagonalised by the same lattice Fourier transform.
This file turns the operator identity of `TraceLogHessian` into *one explicit
scalar sum over momenta*: if

    G = F · diag g · F⁻¹,  V₁ = F · diag v₁ · F⁻¹,
    V₂ = F · diag v₂ · F⁻¹,  S = F · diag s · F⁻¹,

then

    ½ Tr(G V₁ G V₂) − ½ Tr(G S) = ∑_q ( ½ g q² v₁ q v₂ q − ½ g q s q ).

The right-hand side is the scalar Brillouin integrand — the object an actual
one-loop calculation has to evaluate — and it is produced here from the trace,
not assumed.

The diagonalisation lemmas are stated over an arbitrary field, so the same
statements apply verbatim to the complex Fourier transform; the final
`betaTrace` reduction is over `ℝ`, matching `TraceLogHessian.betaTrace`.
-/
import RequestProject.YangMills.TraceLogHessian

namespace YangMills

open Matrix Finset

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugated diagonal matrices multiply by multiplying their symbols. -/
theorem conj_diagonal_mul {F : Matrix ι ι K} (hF : F.det ≠ 0) (a b : ι → K) :
    (F * diagonal a * F⁻¹) * (F * diagonal b * F⁻¹)
      = F * diagonal (fun q => a q * b q) * F⁻¹ := by
  have hinv : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hF)
  calc (F * diagonal a * F⁻¹) * (F * diagonal b * F⁻¹)
      = F * diagonal a * (F⁻¹ * F) * diagonal b * F⁻¹ := by
        simp [Matrix.mul_assoc]
    _ = F * (diagonal a * diagonal b) * F⁻¹ := by
        rw [hinv]; simp [Matrix.mul_assoc]
    _ = F * diagonal (fun q => a q * b q) * F⁻¹ := by
        rw [Matrix.diagonal_mul_diagonal]

/-- The trace of a conjugated diagonal matrix is the sum of its symbol. -/
theorem trace_conj_diagonal {F : Matrix ι ι K} (hF : F.det ≠ 0) (a : ι → K) :
    (F * diagonal a * F⁻¹).trace = ∑ q, a q := by
  have hinv : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hF)
  rw [Matrix.trace_mul_cycle, hinv, Matrix.one_mul, Matrix.trace_diagonal]

/-- **`betaTrace_scalarBrillouinReduction`.**  With every operator diagonalised
by the same Fourier transform, the bubble-minus-seagull trace collapses to one
scalar momentum sum. -/
theorem betaTrace_brillouin {F : Matrix ι ι ℝ} (hF : F.det ≠ 0) (g v₁ v₂ s : ι → ℝ)
    {G V₁ V₂ S : Matrix ι ι ℝ}
    (hG : G = F * diagonal g * F⁻¹) (hV₁ : V₁ = F * diagonal v₁ * F⁻¹)
    (hV₂ : V₂ = F * diagonal v₂ * F⁻¹) (hS : S = F * diagonal s * F⁻¹) :
    betaTrace G V₁ V₂ S
      = ∑ q, (1 / 2 * (g q * g q * v₁ q * v₂ q) - 1 / 2 * (g q * s q)) := by
  have hbubble : (G * V₁ * G * V₂).trace = ∑ q, g q * v₁ q * (g q * v₂ q) := by
    rw [hG, hV₁, hV₂, Matrix.mul_assoc (F * diagonal g * F⁻¹) (F * diagonal v₁ * F⁻¹),
      conj_diagonal_mul hF, conj_diagonal_mul hF, conj_diagonal_mul hF,
      trace_conj_diagonal hF]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hseagull : (G * S).trace = ∑ q, g q * s q := by
    rw [hG, hS, conj_diagonal_mul hF, trace_conj_diagonal hF]
  rw [betaTrace, hbubble, hseagull, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

end YangMills
