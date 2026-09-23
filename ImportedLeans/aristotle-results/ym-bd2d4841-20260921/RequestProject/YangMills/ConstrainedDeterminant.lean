/-
# The constrained Gaussian determinant factors exactly

This module answers, affirmatively and by machine-checked matrix algebra, the
desk-check question

    can the constrained Gaussian determinant itself be factored exactly into
    full and constraint determinants?

Write `Δ` for the (nonsingular) fluctuation operator, `Q` for the linear
constraint, and

    Â = [ Δ  Qᵀ ]
        [ Q  0  ]

for the *bordered* operator whose Gaussian normalisation is the constrained one:
the border implements the delta function `δ(Q B)` by a Lagrange multiplier.
Three theorems:

* `borderedOperator_det` — the exact factorisation

      det Â = (−1)^{#constraints} · det Δ · det (Q Δ⁻¹ Qᵀ),

  hence, up to a background-independent sign,

      log |det Â| = log |det Δ| + log |det (Q Δ⁻¹ Qᵀ)|.

  So the constraint sector contributes its own determinant — the geometric
  avatar of the ghost determinant — and it is *subtracted* rather than
  reconstructed diagram by diagram.

* `borderedOperator_inv` — the inverse of `Â` has the constrained propagator
  `G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃` of `ConstrainedPropagator` as its `(1,1)` block,
  with the reduced inverse `(QG̃Qᵀ)⁻¹` filling the border.  The Schur formula
  used elsewhere in this development is therefore *the* propagator of the
  constrained Gaussian, not a separate convention.

* `borderedHessian_eq_betaTrace` — differentiating the bordered normalisation
  twice in the background reproduces exactly the bubble-minus-seagull functional
  of `TraceLogHessian` *with the constrained propagator*:

      ∂_s∂_t ( −½ log det Â(s,t) ) |₀ = ½Tr(G V₁ G V₂) − ½Tr(G S).

Nothing here is Yang–Mills specific and nothing is estimated; it is exact finite
dimensional algebra plus the second-variation identity already proved.
-/
import RequestProject.YangMills.ConstrainedPropagator

namespace YangMills

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The bordered (Lagrange-multiplier) operator `[[Δ, Qᵀ], [Q, 0]]` whose
Gaussian normalisation is the constrained one. -/
noncomputable def borderedOperator (D : Matrix n n ℝ) (Q : Matrix m n ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks D Qᵀ Q 0

/-- A variation of the fluctuation operator, embedded in the bordered space:
the border is background independent, so only the `(1,1)` block moves. -/
def borderedVariation (X : Matrix n n ℝ) : Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks X 0 0 0

omit [DecidableEq m] [DecidableEq n] in
@[simp] theorem trace_fromBlocks (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) :
    (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- **Exact factorisation of the constrained determinant.**
`det [[Δ, Qᵀ],[Q,0]] = (−1)^{#constraints} · det Δ · det (Q Δ⁻¹ Qᵀ)`. -/
theorem borderedOperator_det (D : Matrix n n ℝ) (Q : Matrix m n ℝ) (hD : D.det ≠ 0) :
    (borderedOperator D Q).det
      = (-1) ^ Fintype.card m * (D.det * (Q * D⁻¹ * Qᵀ).det) := by
  haveI : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.2 hD)
  rw [borderedOperator, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have : (0 : Matrix m m ℝ) - Q * D⁻¹ * Qᵀ = -(Q * D⁻¹ * Qᵀ) := by
    rw [zero_sub]
  rw [this, Matrix.det_neg]
  ring

/-- **Additivity of the logarithm of the constrained determinant.**
`log |det Â| = log |det Δ| + log |det (QΔ⁻¹Qᵀ)|`: the constraint sector enters
the Gaussian normalisation as its own determinant, with the sign
`(−1)^{#constraints}` — a background-independent constant — absorbed by the
absolute value. -/
theorem log_abs_borderedOperator_det (D : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) :
    Real.log |(borderedOperator D Q).det|
      = Real.log |D.det| + Real.log |(Q * D⁻¹ * Qᵀ).det| := by
  rw [borderedOperator_det D Q hD, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_mul, Real.log_mul (abs_ne_zero.mpr hD) (abs_ne_zero.mpr hK)]

/-- The bordered operator is nonsingular as soon as the fluctuation operator and
the reduced constraint block are. -/
theorem borderedOperator_det_ne_zero (D : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) :
    (borderedOperator D Q).det ≠ 0 := by
  rw [borderedOperator_det D Q hD]
  have h1 : ((-1 : ℝ)) ^ Fintype.card m ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero h1 (mul_ne_zero hD hK)

/-- **The inverse of the bordered operator.**  Its `(1,1)` block is exactly the
constrained propagator `G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃`, and the border carries the
reduced inverse `(QG̃Qᵀ)⁻¹`. -/
theorem borderedOperator_mul_inv (D : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) :
    borderedOperator D Q *
        fromBlocks (constrainedPropagator D⁻¹ Q) (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹)
          ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹)) (-(Q * D⁻¹ * Qᵀ)⁻¹)
      = 1 := by
  have hDG : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hD)
  have hKK : (Q * D⁻¹ * Qᵀ) * (Q * D⁻¹ * Qᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hK)
  have h11 : D * constrainedPropagator D⁻¹ Q
      + Qᵀ * ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹)) = 1 := by
    rw [constrainedPropagator, Matrix.mul_sub]
    have e1 : D * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹))
        = Qᵀ * ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹)) := by
      rw [show D * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹))
            = (D * D⁻¹) * (Qᵀ * ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹))) by
          simp [Matrix.mul_assoc], hDG, Matrix.one_mul]
    rw [e1, hDG, sub_add_cancel]
  have h12 : D * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹) + Qᵀ * -(Q * D⁻¹ * Qᵀ)⁻¹ = 0 := by
    rw [show D * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹)
          = (D * D⁻¹) * (Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹) by simp [Matrix.mul_assoc], hDG,
      Matrix.one_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  have h21 : Q * constrainedPropagator D⁻¹ Q
      + (0 : Matrix m m ℝ) * ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹)) = 0 := by
    rw [constrainedPropagator_left_annihilates D⁻¹ Q hK, Matrix.zero_mul, add_zero]
  have h22 : Q * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹)
      + (0 : Matrix m m ℝ) * -(Q * D⁻¹ * Qᵀ)⁻¹ = 1 := by
    rw [Matrix.zero_mul, add_zero,
      show Q * (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹) = (Q * D⁻¹ * Qᵀ) * (Q * D⁻¹ * Qᵀ)⁻¹ by
        simp [Matrix.mul_assoc], hKK]
  simp only [borderedOperator]
  rw [Matrix.fromBlocks_multiply, h11, h12, h21, h22, Matrix.fromBlocks_one]

/-- The inverse of the bordered operator, in closed form. -/
theorem borderedOperator_inv (D : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) :
    (borderedOperator D Q)⁻¹ =
      fromBlocks (constrainedPropagator D⁻¹ Q) (D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹)
        ((Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹)) (-(Q * D⁻¹ * Qᵀ)⁻¹) :=
  Matrix.inv_eq_right_inv (borderedOperator_mul_inv D Q hD hK)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The bordered jet is the bordered operator plus the bordered variations: the
constraint block does not depend on the background. -/
theorem borderedOperator_jet (D V₁ V₂ S : Matrix n n ℝ) (Q : Matrix m n ℝ) (s t : ℝ) :
    borderedOperator (D + s • V₁ + t • V₂ + (s * t) • S) Q
      = borderedOperator D Q + s • (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
        + t • (borderedVariation V₂ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
        + (s * t) • (borderedVariation S : Matrix (n ⊕ m) (n ⊕ m) ℝ) := by
  simp only [borderedOperator, borderedVariation, Matrix.fromBlocks_add,
    Matrix.fromBlocks_smul, smul_zero, add_zero]

/-- **The Hessian of the constrained (bordered) Gaussian normalisation is the
bubble-minus-seagull functional of the constrained propagator.**

    ∂_s∂_t ( −½ log det Â(s,t) + c )|₀ = ½Tr(G V₁ G V₂) − ½Tr(G S),

with `G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃` the constrained propagator.  The Lagrange border
neither adds nor removes a term: the multiplier sector contributes exactly the
projection that turns `G̃` into `G`. -/
theorem borderedHessian_eq_betaTrace (D V₁ V₂ S : Matrix n n ℝ) (Q : Matrix m n ℝ)
    (hD : D.det ≠ 0) (hK : (Q * D⁻¹ * Qᵀ).det ≠ 0) (c : ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      -(1 / 2 : ℝ) * Real.log ((borderedOperator (D + s • V₁ + t • V₂ + (s * t) • S) Q).det)
        + c) 0) 0
      = betaTrace (constrainedPropagator D⁻¹ Q) V₁ V₂ S := by
  have hjet : ∀ s t : ℝ,
      borderedOperator (D + s • V₁ + t • V₂ + (s * t) • S) Q
        = borderedOperator D Q + s • (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
          + t • (borderedVariation V₂ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
          + (s * t) • (borderedVariation S : Matrix (n ⊕ m) (n ⊕ m) ℝ) :=
    fun s t => borderedOperator_jet D V₁ V₂ S Q s t
  have hA : (borderedOperator D Q).det ≠ 0 := borderedOperator_det_ne_zero D Q hD hK
  have hmain := gaussianHessian_eq_betaTrace (borderedOperator D Q)
    (borderedVariation V₁) (borderedVariation V₂) (borderedVariation S) hA c
  have hrw : (fun s : ℝ => deriv (fun t : ℝ =>
        -(1 / 2 : ℝ) * Real.log ((borderedOperator (D + s • V₁ + t • V₂ + (s * t) • S) Q).det)
          + c) 0)
      = fun s : ℝ => deriv (fun t : ℝ =>
        -(1 / 2 : ℝ) * Real.log ((borderedOperator D Q
          + s • (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
          + t • (borderedVariation V₂ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
          + (s * t) • (borderedVariation S : Matrix (n ⊕ m) (n ⊕ m) ℝ)).det) + c) 0 := by
    funext s
    exact congrArg (fun f : ℝ → ℝ => deriv f 0) (funext fun t => by rw [hjet s t])
  rw [hrw, hmain]
  -- now identify the bordered traces with the constrained ones
  set G := constrainedPropagator D⁻¹ Q with hG
  set X := D⁻¹ * Qᵀ * (Q * D⁻¹ * Qᵀ)⁻¹ with hX
  set Y := (Q * D⁻¹ * Qᵀ)⁻¹ * (Q * D⁻¹) with hY
  set Z := -(Q * D⁻¹ * Qᵀ)⁻¹ with hZ
  have hinv : (borderedOperator D Q)⁻¹ = fromBlocks G X Y Z :=
    borderedOperator_inv D Q hD hK
  have hprod : ∀ W : Matrix n n ℝ,
      (borderedOperator D Q)⁻¹ * (borderedVariation W : Matrix (n ⊕ m) (n ⊕ m) ℝ)
        = fromBlocks (G * W) 0 (Y * W) 0 := by
    intro W
    rw [hinv, borderedVariation, Matrix.fromBlocks_multiply]
    simp
  have hsea : ((borderedOperator D Q)⁻¹ *
      (borderedVariation S : Matrix (n ⊕ m) (n ⊕ m) ℝ)).trace = (G * S).trace := by
    rw [hprod S, trace_fromBlocks]; simp
  have hbub : ((borderedOperator D Q)⁻¹ * (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
      * (borderedOperator D Q)⁻¹ * (borderedVariation V₂ : Matrix (n ⊕ m) (n ⊕ m) ℝ)).trace
      = (G * V₁ * G * V₂).trace := by
    have : (borderedOperator D Q)⁻¹ * (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)
        * ((borderedOperator D Q)⁻¹ * (borderedVariation V₂ : Matrix (n ⊕ m) (n ⊕ m) ℝ))
        = fromBlocks (G * V₁ * (G * V₂)) 0 (Y * V₁ * (G * V₂)) 0 := by
      rw [hprod V₁, hprod V₂, Matrix.fromBlocks_multiply]
      simp
    rw [Matrix.mul_assoc ((borderedOperator D Q)⁻¹ *
      (borderedVariation V₁ : Matrix (n ⊕ m) (n ⊕ m) ℝ)), this, trace_fromBlocks]
    simp [Matrix.mul_assoc]
  rw [betaTrace, betaTrace, hsea, hbub]

end YangMills
