/-
# The constrained propagator and the Ward cancellation inside the trace

The block/Schur geometry of a Gaussian measure restricted by a linear constraint
`Q x = 0` produces the constrained propagator

    G = G̃ − G̃ Qᵀ (Q G̃ Qᵀ)⁻¹ Q G̃

from the unconstrained one `G̃`.  Its two defining properties are the exact
annihilation identities

    Q G = 0,        G Qᵀ = 0,

proved here (`constrainedPropagator_left_annihilates`,
`constrainedPropagator_right_annihilates`) from nothing but invertibility of the
reduced block `Q G̃ Qᵀ`.

These identities are the *cancel-first* tool for the one-loop trace: a variation
of the operator that is longitudinal, i.e. lies in the image of `Qᵀ`, is
annihilated by the propagator before any momentum-space expansion.  The
consequence for the bubble-minus-seagull functional `betaTrace` of
`TraceLogHessian` is `betaTrace_eq_zero_of_longitudinal`: the Hessian vanishes on
a pure-gauge direction, so the polarisation is transverse by construction rather
than by an a-posteriori computation.

Everything in this file is exact matrix algebra; no estimate and no analytic
hypothesis appears.  Note that the constrained `G` is *not* invertible (it kills
the constraint directions), so the Ward statement is deliberately stated for the
algebraic functional `betaTrace G V₁ V₂ S`, which needs no invertibility, rather
than through `A⁻¹`.
-/
import RequestProject.YangMills.TraceLogHessian

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The constrained (Schur-projected) propagator
`G = G̃ − G̃ Qᵀ (Q G̃ Qᵀ)⁻¹ Q G̃`. -/
noncomputable def constrainedPropagator (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) :
    Matrix n n ℝ :=
  Gt - Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt)

/-- `Q G = 0`: the constrained propagator lands in the constraint kernel. -/
theorem constrainedPropagator_left_annihilates (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (h : (Q * Gt * Qᵀ).det ≠ 0) :
    Q * constrainedPropagator Gt Q = 0 := by
  have hinv : (Q * Gt * Qᵀ) * (Q * Gt * Qᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  rw [constrainedPropagator, Matrix.mul_sub]
  have : Q * (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt))
      = ((Q * Gt * Qᵀ) * (Q * Gt * Qᵀ)⁻¹) * (Q * Gt) := by
    simp [Matrix.mul_assoc]
  rw [this, hinv, Matrix.one_mul, sub_self]

/-- `G Qᵀ = 0`: the constrained propagator annihilates the constraint image. -/
theorem constrainedPropagator_right_annihilates (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (h : (Q * Gt * Qᵀ).det ≠ 0) :
    constrainedPropagator Gt Q * Qᵀ = 0 := by
  have hinv : (Q * Gt * Qᵀ)⁻¹ * (Q * Gt * Qᵀ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)
  rw [constrainedPropagator, Matrix.sub_mul]
  have : Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * Qᵀ
      = (Gt * Qᵀ) * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt * Qᵀ)) := by
    simp [Matrix.mul_assoc]
  rw [this, hinv, Matrix.mul_one, sub_self]

/-- A longitudinal variation is killed by the constrained propagator. -/
theorem constrained_mul_longitudinal (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (h : (Q * Gt * Qᵀ).det ≠ 0) (W : Matrix m n ℝ) :
    constrainedPropagator Gt Q * (Qᵀ * W) = 0 := by
  rw [← Matrix.mul_assoc, constrainedPropagator_right_annihilates Gt Q h, Matrix.zero_mul]

omit [DecidableEq m] in
/-- **`constrainedTraceLogWard` (algebraic form).**  If both the first variation
`V₁` and the second variation `S` of the operator are longitudinal — i.e. lie in
the image of `Qᵀ`, which is what a pure-gauge background variation produces —
then the bubble-minus-seagull functional vanishes identically, for *any* second
direction `V₂`:

    ½ Tr(G V₁ G V₂) − ½ Tr(G S) = 0.

The polarisation is therefore transverse before any expansion or estimate. -/
theorem betaTrace_eq_zero_of_longitudinal {G : Matrix n n ℝ} {Q : Matrix m n ℝ}
    (hG : G * Qᵀ = 0) {V₁ S : Matrix n n ℝ} {W₁ W₂ : Matrix m n ℝ}
    (hV : V₁ = Qᵀ * W₁) (hS : S = Qᵀ * W₂) (V₂ : Matrix n n ℝ) :
    betaTrace G V₁ V₂ S = 0 := by
  have h1 : G * V₁ = 0 := by
    rw [hV, ← Matrix.mul_assoc, hG, Matrix.zero_mul]
  have h2 : G * S = 0 := by
    rw [hS, ← Matrix.mul_assoc, hG, Matrix.zero_mul]
  rw [betaTrace, h2, Matrix.mul_assoc, h1]
  simp

/-- The same statement with `G` the literal Schur-projected constrained
propagator. -/
theorem constrainedPropagator_ward (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (h : (Q * Gt * Qᵀ).det ≠ 0) {V₁ S : Matrix n n ℝ} {W₁ W₂ : Matrix m n ℝ}
    (hV : V₁ = Qᵀ * W₁) (hS : S = Qᵀ * W₂) (V₂ : Matrix n n ℝ) :
    betaTrace (constrainedPropagator Gt Q) V₁ V₂ S = 0 :=
  betaTrace_eq_zero_of_longitudinal
    (constrainedPropagator_right_annihilates Gt Q h) hV hS V₂

end YangMills
