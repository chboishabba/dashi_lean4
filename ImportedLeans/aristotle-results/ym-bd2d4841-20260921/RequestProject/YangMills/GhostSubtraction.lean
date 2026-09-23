/-
# The gauge/constraint subtraction, produced automatically

`ConstrainedDeterminant` factors the constrained (bordered) determinant as

    det Â = ± det Δ · det (Q Δ⁻¹ Qᵀ),

so at the level of the Gaussian normalisation the constraint sector contributes
its own determinant.  This module carries the same statement to the level of the
Hessian, *algebraically and unconditionally*: the bubble-minus-seagull
functional of the constrained propagator splits as

    betaTrace G V₁ V₂ S = betaTrace G̃ V₁ V₂ S + betaTrace K⁻¹ (ghost jets),

with `K = Q G̃ Qᵀ` the reduced constraint block and the ghost jets

    ghostVertex  X    = Q G̃ X G̃ Qᵀ,
    ghostVertex₂ X Y  = Q G̃ X G̃ Y G̃ Qᵀ

produced by the *same* first and second variations of the fluctuation operator.
Explicitly the constraint sector is

    ½Tr(K⁻¹ W(V₁) K⁻¹ W(V₂)) + ½Tr(K⁻¹ W(S))
      − ½Tr(K⁻¹ W₂(V₁,V₂)) − ½Tr(K⁻¹ W₂(V₂,V₁)),

which is exactly the second variation of `−½ log det K` computed from the
resolvent expansion of `K(s,t) = Q Δ(s,t)⁻¹ Qᵀ`.  So the ghost sector is not
reconstructed diagram by diagram: it is the constraint block of the same
geometric object, with the opposite (subtracting) role, and the whole
decomposition follows from cyclicity of the trace — no invertibility hypothesis
is used in the split itself.

`borderedHessian_sub_fullHessian` records the analytic corollary: the difference
between the Hessian of the constrained Gaussian normalisation and the Hessian of
the unconstrained one *is* the constraint-sector functional.
-/
import RequestProject.YangMills.ConstrainedDeterminant

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The single-insertion ghost vertex `W(X) = Q G̃ X G̃ Qᵀ`. -/
def ghostVertex (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) (X : Matrix n n ℝ) :
    Matrix m m ℝ :=
  Q * Gt * X * Gt * Qᵀ

/-- The double-insertion ghost vertex `W₂(X,Y) = Q G̃ X G̃ Y G̃ Qᵀ`. -/
def ghostVertex₂ (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) (X Y : Matrix n n ℝ) :
    Matrix m m ℝ :=
  Q * Gt * X * Gt * Y * Gt * Qᵀ

/-- The mixed second-order jet of the reduced constraint block
`K(s,t) = Q Δ(s,t)⁻¹ Qᵀ`, as produced by the resolvent expansion:
`−W(S) + W₂(V₁,V₂) + W₂(V₂,V₁)`. -/
def ghostSecondJet (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) (V₁ V₂ S : Matrix n n ℝ) :
    Matrix m m ℝ :=
  -ghostVertex Gt Q S + ghostVertex₂ Gt Q V₁ V₂ + ghostVertex₂ Gt Q V₂ V₁

omit [DecidableEq n] in
/-- Seagull term: `Tr(P S) = Tr(K⁻¹ W(S))` for the projector part
`P = G̃Qᵀ K⁻¹ Q G̃` of the constrained propagator. -/
theorem trace_proj_seagull (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) (S : Matrix n n ℝ) :
    (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * S).trace
      = ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q S).trace := by
  rw [show Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * S
        = (Gt * Qᵀ) * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * S) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  congr 1
  simp [ghostVertex, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Mixed bubble term with the projector on the left:
`Tr(P V₁ G̃ V₂) = Tr(K⁻¹ W₂(V₁,V₂))`. -/
theorem trace_proj_left_bubble (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (V₁ V₂ : Matrix n n ℝ) :
    (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₁ * Gt * V₂).trace
      = ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₁ V₂).trace := by
  rw [show Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₁ * Gt * V₂
        = (Gt * Qᵀ) * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₁ * Gt * V₂) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  congr 1
  simp [ghostVertex₂, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Mixed bubble term with the projector on the right:
`Tr(G̃ V₁ P V₂) = Tr(K⁻¹ W₂(V₂,V₁))`. -/
theorem trace_proj_right_bubble (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (V₁ V₂ : Matrix n n ℝ) :
    (Gt * V₁ * (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt)) * V₂).trace
      = ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₂ V₁).trace := by
  rw [show Gt * V₁ * (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt)) * V₂
        = (Gt * V₁ * Gt * Qᵀ) * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₂) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  congr 1
  simp [ghostVertex₂, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Pure constraint bubble: `Tr(P V₁ P V₂) = Tr(K⁻¹ W(V₁) K⁻¹ W(V₂))`. -/
theorem trace_proj_double_bubble (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (V₁ V₂ : Matrix n n ℝ) :
    (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₁
        * (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt)) * V₂).trace
      = ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q V₁ * (Q * Gt * Qᵀ)⁻¹
          * ghostVertex Gt Q V₂).trace := by
  rw [show Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) * V₁
        * (Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt)) * V₂
        = (Gt * Qᵀ) * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt * V₁ * Gt * Qᵀ)
            * ((Q * Gt * Qᵀ)⁻¹ * (Q * Gt * V₂))) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  congr 1
  simp [ghostVertex, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- **The constrained one-loop functional is the full one plus the constraint
(ghost) sector.**

    ½Tr(G V₁ G V₂) − ½Tr(G S)
      = ½Tr(G̃ V₁ G̃ V₂) − ½Tr(G̃ S)
        + [ ½Tr(K⁻¹W(V₁)K⁻¹W(V₂)) + ½Tr(K⁻¹W(S))
            − ½Tr(K⁻¹W₂(V₁,V₂)) − ½Tr(K⁻¹W₂(V₂,V₁)) ]

with `G` the Schur-projected constrained propagator, `G̃` the unconstrained one
and `K = Q G̃ Qᵀ`.  The bracket is itself a bubble-minus-seagull functional, in
the constraint sector, with propagator `K⁻¹` and the jets induced by the same
first and second variations — see `betaTrace_constrained_split`.

Only cyclicity of the trace is used: no invertibility hypothesis. -/
theorem betaTrace_constrained_eq_full_add_constraintSector
    (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ) (V₁ V₂ S : Matrix n n ℝ) :
    betaTrace (constrainedPropagator Gt Q) V₁ V₂ S
      = betaTrace Gt V₁ V₂ S
        + (1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q V₁ * (Q * Gt * Qᵀ)⁻¹
              * ghostVertex Gt Q V₂).trace
          + 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q S).trace
          - 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₁ V₂).trace
          - 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₂ V₁).trace) := by
  set P : Matrix n n ℝ := Gt * Qᵀ * (Q * Gt * Qᵀ)⁻¹ * (Q * Gt) with hP
  have hG : constrainedPropagator Gt Q = Gt - P := rfl
  have hsea : (constrainedPropagator Gt Q * S).trace
      = (Gt * S).trace - ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q S).trace := by
    rw [hG, Matrix.sub_mul, Matrix.trace_sub, hP, trace_proj_seagull]
  have hbub : (constrainedPropagator Gt Q * V₁ * constrainedPropagator Gt Q * V₂).trace
      = (Gt * V₁ * Gt * V₂).trace
        - ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₁ V₂).trace
        - ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₂ V₁).trace
        + ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q V₁ * (Q * Gt * Qᵀ)⁻¹
            * ghostVertex Gt Q V₂).trace := by
    have hexp : constrainedPropagator Gt Q * V₁ * constrainedPropagator Gt Q * V₂
        = Gt * V₁ * Gt * V₂ - P * V₁ * Gt * V₂ - Gt * V₁ * P * V₂ + P * V₁ * P * V₂ := by
      rw [hG]
      noncomm_ring
    rw [hexp]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hP,
      trace_proj_left_bubble, trace_proj_right_bubble, trace_proj_double_bubble]
  rw [betaTrace, betaTrace, hsea, hbub]
  ring

omit [DecidableEq n] in
/-- The constraint sector *is* a bubble-minus-seagull functional of the reduced
block: the same `betaTrace`, with propagator `K⁻¹`, first variations
`−W(V₁), −W(V₂)` and second variation `−W(S) + W₂(V₁,V₂) + W₂(V₂,V₁)` — exactly
the mixed jet of `K(s,t) = Q Δ(s,t)⁻¹ Qᵀ`. -/
theorem constraintSector_eq_betaTrace (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (V₁ V₂ S : Matrix n n ℝ) :
    betaTrace (Q * Gt * Qᵀ)⁻¹ (-ghostVertex Gt Q V₁) (-ghostVertex Gt Q V₂)
        (ghostSecondJet Gt Q V₁ V₂ S)
      = 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q V₁ * (Q * Gt * Qᵀ)⁻¹
            * ghostVertex Gt Q V₂).trace
        + 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex Gt Q S).trace
        - 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₁ V₂).trace
        - 1 / 2 * ((Q * Gt * Qᵀ)⁻¹ * ghostVertex₂ Gt Q V₂ V₁).trace := by
  rw [betaTrace, ghostSecondJet]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_neg, neg_neg]
  ring

omit [DecidableEq n] in
/-- **`CMP109ConstrainedDeterminantSupertraceSplit`.**  The constrained one-loop
functional is the full one plus the constraint-sector one, both written with the
*same* functional `betaTrace`:

    betaTrace G V₁ V₂ S = betaTrace G̃ V₁ V₂ S + betaTrace K⁻¹ (ghost jets).

This is the Hessian avatar of the exact determinant factorisation
`det Â = ± det Δ · det K` of `borderedOperator_det`. -/
theorem betaTrace_constrained_split (Gt : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (V₁ V₂ S : Matrix n n ℝ) :
    betaTrace (constrainedPropagator Gt Q) V₁ V₂ S
      = betaTrace Gt V₁ V₂ S
        + betaTrace (Q * Gt * Qᵀ)⁻¹ (-ghostVertex Gt Q V₁) (-ghostVertex Gt Q V₂)
            (ghostSecondJet Gt Q V₁ V₂ S) := by
  rw [constraintSector_eq_betaTrace,
    betaTrace_constrained_eq_full_add_constraintSector]

/-- **Analytic corollary.**  The Hessian of the constrained Gaussian
normalisation minus the Hessian of the unconstrained one is exactly the
constraint-sector functional: differentiating the bordered `log det` twice
produces the gauge/constraint subtraction by itself. -/
theorem borderedHessian_sub_fullHessian (D V₁ V₂ S : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) (c : ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
        -(1 / 2 : ℝ) * Real.log ((borderedOperator (D + s • V₁ + t • V₂ + (s * t) • S) Q).det)
          + c) 0) 0
      - deriv (fun s : ℝ => deriv (fun t : ℝ =>
        -(1 / 2 : ℝ) * Real.log ((D + s • V₁ + t • V₂ + (s * t) • S).det) + c) 0) 0
      = betaTrace (Q * D⁻¹ * Qᵀ)⁻¹ (-ghostVertex D⁻¹ Q V₁) (-ghostVertex D⁻¹ Q V₂)
          (ghostSecondJet D⁻¹ Q V₁ V₂ S) := by
  rw [borderedHessian_eq_betaTrace D V₁ V₂ S Q hD hK c,
    gaussianHessian_eq_betaTrace D V₁ V₂ S hD c,
    betaTrace_constrained_split D⁻¹ Q V₁ V₂ S]
  ring

end YangMills
