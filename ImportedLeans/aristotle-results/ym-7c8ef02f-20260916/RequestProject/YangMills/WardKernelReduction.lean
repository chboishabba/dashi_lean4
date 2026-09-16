/-
# Reducing the jets modulo the Ward kernel, before any multiplication

The constrained propagator satisfies `Q G = 0` and `G Qᵀ = 0`
(`ConstrainedPropagator`).  Consequently the one-loop integrand does not depend
on the background jets `V₁, V₂, S` themselves but only on their classes modulo
the two-sided longitudinal subspace

    L = { Qᵀ A }  +  { B Q }  ⊂  End(H).

This module proves that invariance:

* `betaTrace_ward_invariant` — for any `G` with `G Qᵀ = 0` and `Q G = 0`,

      betaTrace G (V₁ + QᵀA₁ + B₁Q) (V₂ + QᵀA₂ + B₂Q) (S + QᵀA₃ + B₃Q)
        = betaTrace G V₁ V₂ S;

* `betaTrace_ward_invariant_constrained` — the same with `G` the literal
  Schur-projected constrained propagator, so the hypotheses are discharged from
  invertibility of the reduced block alone.

The practical content: when a literal jet is extracted, any longitudinal
component may be dropped *before* the matrices are multiplied and before the
Fourier sum is formed.  Only the class `[V_μ] ∈ End(H)/L` enters the scalar
integrand.  `betaTrace_eq_zero_of_twoSided_longitudinal` is the extreme case —
a purely longitudinal jet pair contributes nothing at all.
-/
import RequestProject.YangMills.ConstrainedPropagator

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- A jet reduced modulo the left longitudinal subspace: `G (V + QᵀA) = G V`. -/
theorem mul_left_longitudinal_eq {G : Matrix n n ℝ} {Q : Matrix m n ℝ}
    (hGQ : G * Qᵀ = 0) (V : Matrix n n ℝ) (A : Matrix m n ℝ) :
    G * (V + Qᵀ * A) = G * V := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hGQ, Matrix.zero_mul, add_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- **Ward-kernel invariance of the one-loop integrand.**  If `G Qᵀ = 0` and
`Q G = 0` then the bubble-minus-seagull functional only sees the jets modulo the
two-sided longitudinal subspace `{QᵀA} + {BQ}`. -/
theorem betaTrace_ward_invariant {G : Matrix n n ℝ} {Q : Matrix m n ℝ}
    (hGQ : G * Qᵀ = 0) (hQG : Q * G = 0) (V₁ V₂ S : Matrix n n ℝ)
    (A₁ A₂ A₃ : Matrix m n ℝ) (B₁ B₂ B₃ : Matrix n m ℝ) :
    betaTrace G (V₁ + Qᵀ * A₁ + B₁ * Q) (V₂ + Qᵀ * A₂ + B₂ * Q)
        (S + Qᵀ * A₃ + B₃ * Q)
      = betaTrace G V₁ V₂ S := by
  have hleft : ∀ (V : Matrix n n ℝ) (A : Matrix m n ℝ) (B : Matrix n m ℝ),
      G * (V + Qᵀ * A + B * Q) = G * V + G * B * Q := by
    intro V A B
    rw [show V + Qᵀ * A + B * Q = (V + Qᵀ * A) + B * Q from rfl, Matrix.mul_add,
      mul_left_longitudinal_eq hGQ, Matrix.mul_assoc]
  have htrz : ∀ B : Matrix n m ℝ, (G * B * Q).trace = 0 := by
    intro B
    rw [Matrix.trace_mul_comm,
      show Q * (G * B) = (Q * G) * B by rw [Matrix.mul_assoc], hQG, Matrix.zero_mul,
      Matrix.trace_zero]
  have hsea : (G * (S + Qᵀ * A₃ + B₃ * Q)).trace = (G * S).trace := by
    rw [hleft S A₃ B₃, Matrix.trace_add, htrz, add_zero]
  have hbub : (G * (V₁ + Qᵀ * A₁ + B₁ * Q) * G * (V₂ + Qᵀ * A₂ + B₂ * Q)).trace
      = (G * V₁ * G * V₂).trace := by
    have hmid : G * (V₁ + Qᵀ * A₁ + B₁ * Q) * G = G * V₁ * G := by
      rw [hleft V₁ A₁ B₁, Matrix.add_mul,
        show G * B₁ * Q * G = (G * B₁) * (Q * G) by rw [Matrix.mul_assoc], hQG,
        Matrix.mul_zero, add_zero]
    rw [hmid, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
    have e2 : (G * V₁ * G * (B₂ * Q)).trace = 0 := by
      rw [show G * V₁ * G * (B₂ * Q) = (G * V₁ * G * B₂) * Q by simp [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show Q * (G * V₁ * G * B₂) = (Q * G) * (V₁ * G * B₂) by simp [Matrix.mul_assoc],
        hQG, Matrix.zero_mul, Matrix.trace_zero]
    have e1' : (G * V₁ * G * (Qᵀ * A₂)).trace = 0 := by
      rw [show G * V₁ * G * (Qᵀ * A₂) = (G * V₁ * (G * Qᵀ)) * A₂ by
          simp [Matrix.mul_assoc], hGQ]
      simp
    rw [e1', e2, add_zero, add_zero]
  rw [betaTrace, betaTrace, hsea, hbub]

omit [DecidableEq m] [DecidableEq n] in
/-- A purely longitudinal jet configuration contributes nothing. -/
theorem betaTrace_eq_zero_of_twoSided_longitudinal {G : Matrix n n ℝ} {Q : Matrix m n ℝ}
    (hGQ : G * Qᵀ = 0) (hQG : Q * G = 0)
    (A₁ A₂ A₃ : Matrix m n ℝ) (B₁ B₂ B₃ : Matrix n m ℝ) :
    betaTrace G (Qᵀ * A₁ + B₁ * Q) (Qᵀ * A₂ + B₂ * Q) (Qᵀ * A₃ + B₃ * Q) = 0 := by
  have h := betaTrace_ward_invariant hGQ hQG 0 0 0 A₁ A₂ A₃ B₁ B₂ B₃
  simpa [betaTrace] using h

omit [DecidableEq n] in
/-- **Ward-kernel invariance for the literal constrained propagator.**  With
`G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃`, invertibility of the reduced block is the only
hypothesis: longitudinal components of the jets may be discarded before the
matrices are multiplied. -/
theorem betaTrace_ward_invariant_constrained (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (h : (Q * Gt * Qᵀ).det ≠ 0) (V₁ V₂ S : Matrix n n ℝ)
    (A₁ A₂ A₃ : Matrix m n ℝ) (B₁ B₂ B₃ : Matrix n m ℝ) :
    betaTrace (constrainedPropagator Gt Q) (V₁ + Qᵀ * A₁ + B₁ * Q)
        (V₂ + Qᵀ * A₂ + B₂ * Q) (S + Qᵀ * A₃ + B₃ * Q)
      = betaTrace (constrainedPropagator Gt Q) V₁ V₂ S :=
  betaTrace_ward_invariant (constrainedPropagator_right_annihilates Gt Q h)
    (constrainedPropagator_left_annihilates Gt Q h) V₁ V₂ S A₁ A₂ A₃ B₁ B₂ B₃

end YangMills
