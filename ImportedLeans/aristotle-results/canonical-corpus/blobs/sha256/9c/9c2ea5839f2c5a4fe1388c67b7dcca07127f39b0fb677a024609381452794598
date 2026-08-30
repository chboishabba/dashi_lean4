/-
# Matrix-valued symbols: the Brillouin reduction with Lorentz/colour indices

`BrillouinReduction` reduces the one-loop trace to a scalar momentum sum when
every operator is diagonalised by the same Fourier transform with *scalar*
symbols.  A gauge field carries indices, so the physical symbols are matrices
`g(q), v_μ(q), s_{μν}(q)` acting on the internal (Lorentz ⊗ colour) space, and
the operators are block diagonal in momentum rather than diagonal.  This module
proves the reduction in that generality:

    G  = F · blockDiag g  · F⁻¹,   V₁ = F · blockDiag v₁ · F⁻¹,
    V₂ = F · blockDiag v₂ · F⁻¹,   S  = F · blockDiag s  · F⁻¹

    ⟹  ½Tr(G V₁ G V₂) − ½Tr(G S) = ∑_q [ ½tr(g(q) v₁(q) g(q) v₂(q)) − ½tr(g(q) s(q)) ]
                                  = ∑_q betaTrace (g q) (v₁ q) (v₂ q) (s q).

So the Brillouin integrand *is* the same bubble-minus-seagull functional,
evaluated at one momentum — the object called `I_{μν}(q)` in the source-facing
notation.

Two further structural facts are proved, both saying that the constrained
geometry is computed momentum by momentum:

* `blockDiagonal_inv` — inverting a block-diagonal operator inverts each block;
* `constrainedPropagator_blockDiagonal` — the Schur-projected constrained
  propagator of block-diagonal data is the block diagonal of the constrained
  propagators of the blocks, i.e. `G(q) = g̃(q) − g̃(q)Q(q)ᵀ(Q(q)g̃(q)Q(q)ᵀ)⁻¹Q(q)g̃(q)`.

Nothing here supplies a literal symbol; it supplies the exact reduction that a
literal symbol is fed into.
-/
import RequestProject.YangMills.ConstrainedPropagator

namespace YangMills

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [DecidableEq κ] in
/-- Conjugated block-diagonal matrices multiply blockwise. -/
theorem conj_blockDiagonal_mul {N : Type*} [Fintype N] [DecidableEq N]
    {F : Matrix N N ℝ} (hF : F.det ≠ 0) (E : Matrix (κ × ι) (κ × ι) ℝ → Matrix N N ℝ)
    (a b : ι → Matrix κ κ ℝ)
    (hE : ∀ X Y, E (X * Y) = E X * E Y) :
    (F * E (blockDiagonal a) * F⁻¹) * (F * E (blockDiagonal b) * F⁻¹)
      = F * E (blockDiagonal fun q => a q * b q) * F⁻¹ := by
  have hinv : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hF)
  calc (F * E (blockDiagonal a) * F⁻¹) * (F * E (blockDiagonal b) * F⁻¹)
      = F * E (blockDiagonal a) * (F⁻¹ * F) * E (blockDiagonal b) * F⁻¹ := by
        simp [Matrix.mul_assoc]
    _ = F * (E (blockDiagonal a) * E (blockDiagonal b)) * F⁻¹ := by
        rw [hinv]; simp [Matrix.mul_assoc]
    _ = F * E (blockDiagonal fun q => a q * b q) * F⁻¹ := by
        rw [← hE, blockDiagonal_mul]

/-- Conjugated block-diagonal matrices multiply blockwise (identity embedding). -/
theorem conj_blockDiag_mul {F : Matrix (κ × ι) (κ × ι) ℝ} (hF : F.det ≠ 0)
    (a b : ι → Matrix κ κ ℝ) :
    (F * blockDiagonal a * F⁻¹) * (F * blockDiagonal b * F⁻¹)
      = F * blockDiagonal (fun q => a q * b q) * F⁻¹ :=
  conj_blockDiagonal_mul hF id a b (fun _ _ => rfl)

/-- The trace of a conjugated block-diagonal matrix is the sum of the block
traces. -/
theorem trace_conj_blockDiag {F : Matrix (κ × ι) (κ × ι) ℝ} (hF : F.det ≠ 0)
    (a : ι → Matrix κ κ ℝ) :
    (F * blockDiagonal a * F⁻¹).trace = ∑ q, (a q).trace := by
  have hinv : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hF)
  rw [Matrix.trace_mul_cycle, hinv, Matrix.one_mul, Matrix.trace_blockDiagonal]

/-- **`betaTrace_blockBrillouin`.**  With matrix-valued symbols the one-loop
functional is the momentum sum of the *same* functional evaluated on the
symbols:

    ½Tr(G V₁ G V₂) − ½Tr(G S) = ∑_q betaTrace (g q) (v₁ q) (v₂ q) (s q). -/
theorem betaTrace_blockBrillouin {F : Matrix (κ × ι) (κ × ι) ℝ} (hF : F.det ≠ 0)
    (g v₁ v₂ s : ι → Matrix κ κ ℝ)
    {G V₁ V₂ S : Matrix (κ × ι) (κ × ι) ℝ}
    (hG : G = F * blockDiagonal g * F⁻¹) (hV₁ : V₁ = F * blockDiagonal v₁ * F⁻¹)
    (hV₂ : V₂ = F * blockDiagonal v₂ * F⁻¹) (hS : S = F * blockDiagonal s * F⁻¹) :
    betaTrace G V₁ V₂ S = ∑ q, betaTrace (g q) (v₁ q) (v₂ q) (s q) := by
  have hbubble : (G * V₁ * G * V₂).trace = ∑ q, (g q * v₁ q * g q * v₂ q).trace := by
    rw [hG, hV₁, hV₂, Matrix.mul_assoc (F * blockDiagonal g * F⁻¹),
      conj_blockDiag_mul hF, conj_blockDiag_mul hF, conj_blockDiag_mul hF,
      trace_conj_blockDiag hF]
    exact Finset.sum_congr rfl fun q _ => by rw [← Matrix.mul_assoc (g q)]
  have hseagull : (G * S).trace = ∑ q, (g q * s q).trace := by
    rw [hG, hS, conj_blockDiag_mul hF, trace_conj_blockDiag hF]
  rw [betaTrace, hbubble, hseagull, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => rfl

/-- Inverting a block-diagonal matrix inverts each block. -/
theorem blockDiagonal_inv (M : ι → Matrix κ κ ℝ) (h : ∀ q, (M q).det ≠ 0) :
    (blockDiagonal M)⁻¹ = blockDiagonal fun q => (M q)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blockDiagonal_mul]
  have : (fun q => M q * (M q)⁻¹) = fun _ : ι => (1 : Matrix κ κ ℝ) := by
    funext q
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (h q))
  rw [this]
  exact Matrix.blockDiagonal_one

omit [DecidableEq κ] in
/-- **The constrained propagator is computed momentum by momentum.**  For
block-diagonal fluctuation data and a block-diagonal constraint,

    G = blockDiag (fun q => g̃(q) − g̃(q)Q(q)ᵀ(Q(q)g̃(q)Q(q)ᵀ)⁻¹Q(q)g̃(q)). -/
theorem constrainedPropagator_blockDiagonal (gt : ι → Matrix κ κ ℝ)
    (Qs : ι → Matrix μ κ ℝ) (h : ∀ q, (Qs q * gt q * (Qs q)ᵀ).det ≠ 0) :
    constrainedPropagator (blockDiagonal gt) (blockDiagonal Qs)
      = blockDiagonal fun q => constrainedPropagator (gt q) (Qs q) := by
  have hK : (blockDiagonal Qs * blockDiagonal gt * (blockDiagonal Qs)ᵀ)
      = blockDiagonal fun q => Qs q * gt q * (Qs q)ᵀ := by
    rw [blockDiagonal_transpose, blockDiagonal_mul, blockDiagonal_mul]
  rw [constrainedPropagator, hK, blockDiagonal_inv _ h, blockDiagonal_transpose]
  simp only [← blockDiagonal_mul, ← blockDiagonal_sub]
  rfl

end YangMills
