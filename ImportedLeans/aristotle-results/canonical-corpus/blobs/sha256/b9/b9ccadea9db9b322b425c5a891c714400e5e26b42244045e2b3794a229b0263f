/-
# Positivity of the constrained propagator, and the sign of the bubble

The A1a fork asks whether the scalar integrand of the one-loop coefficient is
sign definite.  Half of that question can be answered once and for all, before
any symbol is extracted, and this module answers it.

* `constrainedPropagator_gram` — if the unconstrained propagator is a Gram
  matrix `G̃ = BᵀB` (which every covariance is) then so is the *constrained*
  one:

      G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃ = CᵀC,   C = (1 − BQᵀ(QG̃Qᵀ)⁻¹QBᵀ) B,

  because `P = BQᵀ(QG̃Qᵀ)⁻¹QBᵀ` is an orthogonal projection.  The Schur
  projection therefore never destroys positivity; `constrainedPropagator_posSemidef`
  states the same in Mathlib's `PosSemidef` language.

* `trace_bubble_nonneg` — for such a `G` and any *symmetric* variation `V`,

      Tr(G V G V) = Tr(MᵀM) ≥ 0,   M = C V Cᵀ.

  So the bubble term of the diagonal Hessian entries (`μ = ν`) is nonnegative
  pointwise — momentum by momentum after Fourier diagonalisation
  (`bubble_symbol_nonneg`).  It cannot be the source of a negative coefficient.

* `betaTrace_nonneg_of_seagull_nonpos` — consequently the whole
  bubble-minus-seagull functional is nonnegative as soon as the seagull trace
  `Tr(G S)` is nonpositive.  All the sign risk in the diagonal one-loop
  coefficient sits in the seagull term.

Everything is exact algebra over `ℝ`; no estimate, no spectral theory, no square
root of a matrix is used — the Gram factorisation is produced explicitly.
-/
import RequestProject.YangMills.ConstrainedPropagator

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Gram factor of the constrained propagator:
`C = (1 − B Qᵀ (Q BᵀB Qᵀ)⁻¹ Q Bᵀ) B`. -/
noncomputable def constrainedGramFactor (B : Matrix n n ℝ) (Q : Matrix m n ℝ) :
    Matrix n n ℝ :=
  (1 - B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ)) * B

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The reduced constraint block of a Gram covariance is symmetric. -/
theorem reducedBlock_transpose (B : Matrix n n ℝ) (Q : Matrix m n ℝ) :
    (Q * (Bᵀ * B) * Qᵀ)ᵀ = Q * (Bᵀ * B) * Qᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- `P = B Qᵀ K⁻¹ Q Bᵀ` is symmetric. -/
theorem schurProjection_transpose (B : Matrix n n ℝ) (Q : Matrix m n ℝ) :
    (B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))ᵀ
      = B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, reducedBlock_transpose]
  simp [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- `P = B Qᵀ K⁻¹ Q Bᵀ` is idempotent. -/
theorem schurProjection_idem (B : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hK : (Q * (Bᵀ * B) * Qᵀ).det ≠ 0) :
    (B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))
        * (B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))
      = B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ) := by
  have hKK : (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * (Bᵀ * B) * Qᵀ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hK)
  calc (B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))
        * (B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))
      = (B * Qᵀ) * (((Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * (Bᵀ * B) * Qᵀ))
          * ((Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ))) := by
        simp [Matrix.mul_assoc]
    _ = B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ) := by
        rw [hKK, Matrix.one_mul]; simp [Matrix.mul_assoc]

/-- **The constrained propagator of a Gram covariance is itself a Gram matrix.**
`G̃ = BᵀB ⟹ G = CᵀC` with `C = (1 − BQᵀK⁻¹QBᵀ)B`.  The Schur projection is an
orthogonal projection, so it preserves positivity exactly. -/
theorem constrainedPropagator_gram (B : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hK : (Q * (Bᵀ * B) * Qᵀ).det ≠ 0) :
    constrainedPropagator (Bᵀ * B) Q
      = (constrainedGramFactor B Q)ᵀ * constrainedGramFactor B Q := by
  set P : Matrix n n ℝ := B * Qᵀ * (Q * (Bᵀ * B) * Qᵀ)⁻¹ * (Q * Bᵀ) with hP
  have hPt : Pᵀ = P := schurProjection_transpose B Q
  have hPP : P * P = P := schurProjection_idem B Q hK
  have hfac : ((1 - P) * B)ᵀ * ((1 - P) * B) = Bᵀ * ((1 - P) * B) := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hPt,
      show (Bᵀ * (1 - P)) * ((1 - P) * B) = Bᵀ * ((1 - P) * (1 - P)) * B by
        simp [Matrix.mul_assoc],
      show (1 - P) * (1 - P) = 1 - P by
        have h : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        rw [h, hPP]; abel]
    simp [Matrix.mul_assoc]
  rw [constrainedGramFactor, ← hP, hfac, constrainedPropagator]
  simp [hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The constrained propagator of a Gram covariance is positive semidefinite. -/
theorem constrainedPropagator_posSemidef (B : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hK : (Q * (Bᵀ * B) * Qᵀ).det ≠ 0) :
    (constrainedPropagator (Bᵀ * B) Q).PosSemidef := by
  rw [constrainedPropagator_gram B Q hK]
  simpa using Matrix.posSemidef_conjTranspose_mul_self (constrainedGramFactor B Q)

omit [DecidableEq m] [DecidableEq n] in
/-- **The bubble term is nonnegative.**  For a Gram propagator `G = CᵀC` and a
symmetric variation `V`, `Tr(G V G V) = Tr(MᵀM) ≥ 0` with `M = C V Cᵀ`. -/
theorem trace_bubble_nonneg {G V : Matrix n n ℝ} {C : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) :
    0 ≤ (G * V * G * V).trace := by
  set M : Matrix n n ℝ := C * V * Cᵀ with hM
  have hMt : Mᵀ = M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hV]
    simp [Matrix.mul_assoc]
  have e1 : G * V * G * V = Cᵀ * ((C * V * Cᵀ) * (C * V)) := by
    rw [hG]; simp [Matrix.mul_assoc]
  have e2 : (C * V * Cᵀ) * (C * V) * Cᵀ = M * M := by
    rw [hM]; simp [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm, e2]
  nth_rewrite 1 [← hMt]
  have : (Mᵀ * M).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self M
  exact this.trace_nonneg

omit [DecidableEq m] [DecidableEq n] in
/-- The trace `Tr(MᵀM)` is strictly positive for a nonzero `M`. -/
theorem trace_transpose_mul_self_pos {M : Matrix n n ℝ} (h : M ≠ 0) :
    0 < (Mᵀ * M).trace := by
  have hsum : (Mᵀ * M).trace = ∑ i, ∑ j, (M j i) ^ 2 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by ext i j; simp [hc i j])
  rw [hsum]
  refine Finset.sum_pos' (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _)
    ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.sum_pos' (fun l _ => sq_nonneg _)
    ⟨i, Finset.mem_univ i, by positivity⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **Strict positivity of the bubble.**  If the propagator does not annihilate
the variation — `G V G ≠ 0` — the bubble term is strictly positive. -/
theorem trace_bubble_pos {G V : Matrix n n ℝ} {C : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hne : G * V * G ≠ 0) :
    0 < (G * V * G * V).trace := by
  set M : Matrix n n ℝ := C * V * Cᵀ with hM
  have hMt : Mᵀ = M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hV]
    simp [Matrix.mul_assoc]
  have hGVG : Cᵀ * M * C = G * V * G := by
    rw [hM, hG]; simp [Matrix.mul_assoc]
  have hMne : M ≠ 0 := by
    intro h0
    apply hne
    rw [← hGVG, h0]
    simp
  have e1 : G * V * G * V = Cᵀ * ((C * V * Cᵀ) * (C * V)) := by
    rw [hG]; simp [Matrix.mul_assoc]
  have e2 : (C * V * Cᵀ) * (C * V) * Cᵀ = M * M := by
    rw [hM]; simp [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm, e2]
  nth_rewrite 1 [← hMt]
  exact trace_transpose_mul_self_pos hMne

omit [DecidableEq m] [DecidableEq n] in
/-- **Strict sign criterion.**  A Gram propagator, a symmetric variation that is
not annihilated, and a nonpositive seagull give a strictly positive one-loop
functional. -/
theorem betaTrace_pos_of_seagull_nonpos {G V S : Matrix n n ℝ} {C : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hne : G * V * G ≠ 0) (hS : (G * S).trace ≤ 0) :
    0 < betaTrace G V V S := by
  have hb := trace_bubble_pos hG hV hne
  rw [betaTrace]
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- **Sign criterion for the diagonal one-loop coefficient.**  With a Gram
(constrained) propagator and a symmetric first variation, the whole
bubble-minus-seagull functional is nonnegative as soon as the seagull trace is
nonpositive.  All the sign risk sits in the seagull. -/
theorem betaTrace_nonneg_of_seagull_nonpos {G V S : Matrix n n ℝ} {C : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hS : (G * S).trace ≤ 0) :
    0 ≤ betaTrace G V V S := by
  have hb := trace_bubble_nonneg hG hV
  rw [betaTrace]
  have : 0 ≤ 1 / 2 * (G * V * G * V).trace := by positivity
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- The same statement momentum by momentum: after block diagonalisation the
bubble part of the integrand is nonnegative in every Brillouin cell. -/
theorem bubble_symbol_nonneg {ι : Type*} [Fintype ι] (g v : ι → Matrix n n ℝ)
    (C : ι → Matrix n n ℝ) (hg : ∀ q, g q = (C q)ᵀ * C q) (hv : ∀ q, (v q)ᵀ = v q) :
    0 ≤ ∑ q, (g q * v q * g q * v q).trace :=
  Finset.sum_nonneg fun q _ => trace_bubble_nonneg (hg q) (hv q)

end YangMills
