import Mathlib
import Integration.Experiment.Uncertainty

/-!
# Stage 4, lane 2 — sensitivities that are actually derivatives

Stage 3 carried `Law.sensitivity` and `ExperimentSpec.sensitivities` as
*declared data*: rational numbers travelling with a prediction, with nothing
proving that they are the derivatives of the law they annotate
(`TOE_EXPERIMENT_CALCULUS.md`, frontier item 1).  This file supplies the missing
notion and keeps the three layers the frontier item asks to be kept apart:

```
derivative   →   sensitivity   →   uncertainty propagation
```

## Layer 1 — the derivative

`jacobian f x` is the matrix of the Fréchet derivative of
`f : (Fin n → ℝ) → (Fin m → ℝ)` at `x`, entry `(i,j)` being `∂fᵢ/∂xⱼ`.  Proved:

* `jacobian_of_linear`, `jacobian_of_affine` — the Jacobian of `x ↦ M x (+ b)`
  is `M`;
* `jacobian_comp` — the **chain rule in matrix form**: Jacobians of a composite
  multiply, so a chain of laws in the quantity graph has one Jacobian, matching
  `Cov.push_push` at the propagation layer.

## Layer 2 — the sensitivity

`CertifiedSensitivity` is a declared sensitivity vector **together with the
proof that each entry is the corresponding partial derivative**.  It is the
Stage-3 `sensitivity` field with its obligation discharged rather than assumed.
`declared_is_the_partial_derivative` restates the field as an equation with
`deriv`, and `chargeSensitivity` is the worked instance for the coulomb-counting
edge `Q = I·t`, whose Stage-3 declared list was `(∂Q/∂I, ∂Q/∂t) = (t, I)`.

## Layer 3 — propagation

`RCov` is the real-valued analogue of `Integration.Experiment.Uncertainty.Cov`
(symmetry and positive semidefiniteness are proved preserved by `RCov.push`), so
that a *certified* Jacobian can be pushed.  The three layers are then proved not
to collapse:

* `affine_variation_is_exactly_the_jacobian` — for an affine law, first-order
  propagation is exact;
* `derivative_zero_does_not_bound_variation` — a vanishing sensitivity does not
  make the output insensitive over a finite range (`t ↦ t²` at `0`), so layer 1
  does not by itself license a layer-3 conclusion;
* `jacobian_does_not_determine_the_output_covariance` — the same Jacobian with
  two different input covariances gives two different output covariances, so a
  sensitivity list is not an uncertainty statement;
* `covariance_is_not_a_probability_statement` is deliberately absent: nothing
  here interprets `RCov` as the covariance matrix of a random vector.  It is a
  bookkeeping object with the algebra of one, exactly as in Stage 3.

**Claim boundary.** `jacobian` is Mathlib's `fderiv` in coordinates; no
probability measure appears in this file, and no claim is made that any declared
sensitivity elsewhere in the corpus is certified — only the ones carrying a
`CertifiedSensitivity` are.
-/

namespace Integration.Experiment.JacobianSensitivity

open Matrix

/-! ## §1 Layer 1: the Jacobian -/

/-- **The Jacobian matrix** of `f` at `x`: entry `(i,j)` is `∂fᵢ/∂xⱼ`, read off
Mathlib's Fréchet derivative. -/
noncomputable def jacobian {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ f x (Pi.single j 1) i

@[simp] theorem jacobian_apply {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (i : Fin m) (j : Fin n) : jacobian f x i j = fderiv ℝ f x (Pi.single j 1) i := rfl

/-- A continuous linear map in coordinates: its value is the matrix product of
its own Jacobian entries with the argument. -/
theorem clm_apply_eq_sum {n m : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ)
    (i : Fin m) : L v i = ∑ j, v j * L (Pi.single j 1) i := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [Finset.sum_apply]

/-- **The Jacobian of a linear law is its matrix.** -/
theorem jacobian_of_linear {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    jacobian (fun v => M *ᵥ v) x = M := by
  ext i j
  have hd : fderiv ℝ (fun v : Fin n → ℝ => M *ᵥ v) x
      = (Matrix.mulVecLin M).toContinuousLinearMap :=
    ((Matrix.mulVecLin M).toContinuousLinearMap.hasFDerivAt).fderiv
  simp [jacobian, hd, Matrix.mulVec_single]

/-- **The Jacobian of an affine law is its linear part**: the offset is
invisible to the derivative. -/
theorem jacobian_of_affine {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : jacobian (fun v => M *ᵥ v + b) x = M := by
  ext i j
  have hd : fderiv ℝ (fun v : Fin n → ℝ => M *ᵥ v + b) x
      = (Matrix.mulVecLin M).toContinuousLinearMap := by
    have h1 : HasFDerivAt (fun v : Fin n → ℝ => M *ᵥ v + b)
        ((Matrix.mulVecLin M).toContinuousLinearMap) x :=
      ((Matrix.mulVecLin M).toContinuousLinearMap.hasFDerivAt).add_const b
    exact h1.fderiv
  simp [jacobian, hd, Matrix.mulVec_single]

/-- **The chain rule, in matrix form.**  Jacobians of a composite multiply, so a
chain of laws has a single Jacobian — the derivative-level counterpart of
`Cov.push_push`. -/
theorem jacobian_comp {n m k : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (g : (Fin m → ℝ) → (Fin k → ℝ)) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    jacobian (g ∘ f) x = jacobian g (f x) * jacobian f x := by
  ext i j
  have hcomp : fderiv ℝ (g ∘ f) x = (fderiv ℝ g (f x)).comp (fderiv ℝ f x) :=
    fderiv_comp x hg hf
  rw [jacobian_apply, hcomp]
  have := clm_apply_eq_sum (fderiv ℝ g (f x)) (fderiv ℝ f x (Pi.single j 1)) i
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]; rfl

/-! ## §2 Layer 2: a sensitivity carrying its certificate -/

/-- **A certified sensitivity**: a declared sensitivity vector for a scalar law
at a point, *together with the proof* that each entry is the corresponding
partial derivative.  Stage 3's `sensitivity` field is the `declared` component
alone. -/
structure CertifiedSensitivity (n : ℕ) where
  /-- The scalar law. -/
  f : (Fin n → ℝ) → ℝ
  /-- The operating point. -/
  point : Fin n → ℝ
  /-- The sensitivity the analyst declares. -/
  declared : Fin n → ℝ
  /-- The obligation, discharged: entry `j` is `∂f/∂xⱼ` at the operating
  point. -/
  certificate : ∀ j, HasDerivAt (fun t => f (Function.update point j t)) (declared j) (point j)

namespace CertifiedSensitivity

variable {n : ℕ}

/-- **The declared sensitivity *is* the partial derivative.**  This is the exact
statement Stage 3 could not make about `Law.sensitivity`. -/
theorem declared_is_the_partial_derivative (S : CertifiedSensitivity n) (j : Fin n) :
    S.declared j = deriv (fun t => S.f (Function.update S.point j t)) (S.point j) :=
  (S.certificate j).deriv.symm

/-- The certified sensitivity of a law is unique: two certificates for the same
law at the same point declare the same vector. -/
theorem declared_unique (S T : CertifiedSensitivity n) (hf : S.f = T.f)
    (hp : S.point = T.point) : S.declared = T.declared := by
  funext j
  rw [declared_is_the_partial_derivative, declared_is_the_partial_derivative, hf, hp]

end CertifiedSensitivity

/-- The coulomb-counting law `Q = I · t`, as a function of the input vector
`![I, t]`. -/
def chargeLaw : (Fin 2 → ℝ) → ℝ := fun v => v 0 * v 1

/-- **The Stage-3 sensitivity list of the coulomb-counting edge, certified.**
The declared pair `(∂Q/∂I, ∂Q/∂t) = (t, I)` — the one
`Integration.Experiment.Uncertainty.charge_variance` propagates — is here proved
to be the vector of partial derivatives of `chargeLaw`. -/
noncomputable def chargeSensitivity (I t : ℝ) : CertifiedSensitivity 2 where
  f := chargeLaw
  point := ![I, t]
  declared := ![t, I]
  certificate := by
    intro j
    fin_cases j
    · have h : (fun s : ℝ => chargeLaw (Function.update ![I, t] 0 s)) = fun s => s * t := by
        funext s
        simp [chargeLaw]
      simpa [h] using (hasDerivAt_id (![I, t] 0)).mul_const t
    · have h : (fun s : ℝ => chargeLaw (Function.update ![I, t] 1 s)) = fun s => I * s := by
        funext s
        simp [chargeLaw]
      simpa [h] using (hasDerivAt_id (![I, t] 1)).const_mul I

/-- Explicitly: the certified sensitivity of `Q = I·t` is `(t, I)`. -/
@[simp] theorem chargeSensitivity_declared (I t : ℝ) :
    (chargeSensitivity I t).declared = ![t, I] := rfl

/-! ## §3 Layer 3: propagation, over the reals -/

/-- A real covariance object: symmetric and positive semidefinite, with both
conditions as fields.  This is the real-valued twin of
`Integration.Experiment.Uncertainty.Cov`, needed because a Jacobian certified by
`fderiv` is real. -/
structure RCov (n : ℕ) where
  /-- The matrix of covariances. -/
  toMatrix : Matrix (Fin n) (Fin n) ℝ
  /-- Covariance matrices are symmetric. -/
  symm : toMatrix.transpose = toMatrix
  /-- Covariance matrices are positive semidefinite. -/
  psd : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (toMatrix *ᵥ v)

namespace RCov

/-- **First-order propagation** `Σ_y = J Σ_x Jᵀ`, with symmetry and positive
semidefiniteness proved preserved. -/
def push {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (S : RCov n) : RCov m where
  toMatrix := J * S.toMatrix * J.transpose
  symm := by simp [Matrix.transpose_mul, S.symm, Matrix.mul_assoc]
  psd := by
    intro v
    have h : (J * S.toMatrix * J.transpose) *ᵥ v
        = J *ᵥ (S.toMatrix *ᵥ (J.transpose *ᵥ v)) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact S.psd _

@[simp] theorem push_toMatrix {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (S : RCov n) :
    (push J S).toMatrix = J * S.toMatrix * J.transpose := rfl

/-- Propagation composes, matching the chain rule `jacobian_comp`. -/
theorem push_push {n m k : ℕ} (J₁ : Matrix (Fin m) (Fin n) ℝ)
    (J₂ : Matrix (Fin k) (Fin m) ℝ) (S : RCov n) :
    (push J₂ (push J₁ S)).toMatrix = (push (J₂ * J₁) S).toMatrix := by
  simp [push, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The covariance of independent inputs with variances `d`. -/
def diag {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) : RCov n where
  toMatrix := Matrix.diagonal d
  symm := Matrix.diagonal_transpose d
  psd := by
    intro v
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul_diagonal, dotProduct]
    exact Finset.sum_nonneg fun i _ => by nlinarith [hd i, sq_nonneg (v i)]

end RCov

/-- **Propagating a certified Jacobian.**  The output covariance attached to a
law at an operating point is `J Σ Jᵀ` for the *certified* `J`; nothing else in
the pipeline is allowed to supply `J`. -/
noncomputable def propagate {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (S : RCov n) : RCov m := RCov.push (jacobian f x) S

/-! ## §4 The three layers do not collapse -/

/-- **Exactness for an affine law.**  For `f v = M v + b` the first-order
propagation is not an approximation: the variation of the output is exactly the
Jacobian applied to the variation of the input. -/
theorem affine_variation_is_exactly_the_jacobian {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x d : Fin n → ℝ) :
    (fun v => M *ᵥ v + b) (x + d) - (fun v => M *ᵥ v + b) x
      = jacobian (fun v => M *ᵥ v + b) x *ᵥ d := by
  rw [jacobian_of_affine]
  simp [Matrix.mulVec_add]

/-- **A vanishing sensitivity is not insensitivity.**  The derivative of `t ↦ t²`
at `0` is `0`, yet the output moves by `δ²` under a finite input change: layer 1
does not license a layer-3 conclusion, and a sensitivity list is a statement
about an infinitesimal neighbourhood of the operating point only. -/
theorem derivative_zero_does_not_bound_variation :
    deriv (fun t : ℝ => t ^ 2) 0 = 0 ∧
      ∀ δ : ℝ, δ ≠ 0 → (fun t : ℝ => t ^ 2) δ - (fun t : ℝ => t ^ 2) 0
        ≠ deriv (fun t : ℝ => t ^ 2) 0 * δ := by
  have hd : deriv (fun t : ℝ => t ^ 2) 0 = 0 := by
    simp
  refine ⟨hd, fun δ hδ hcon => ?_⟩
  rw [hd] at hcon
  simp at hcon
  exact hδ hcon

/-- **A Jacobian is not an uncertainty statement.**  With the identity Jacobian,
two different input covariances give two different output covariances, so a
certified sensitivity list does not determine the propagated uncertainty: the
input covariance is a separate declaration, and the separation of the Stage-3
budget into distinct sources survives the move to certified derivatives. -/
theorem jacobian_does_not_determine_the_output_covariance :
    ∃ (J : Matrix (Fin 1) (Fin 1) ℝ) (S T : RCov 1),
      (RCov.push J S).toMatrix ≠ (RCov.push J T).toMatrix := by
  refine ⟨1, RCov.diag ![1] (by intro i; fin_cases i; norm_num),
    RCov.diag ![2] (by intro i; fin_cases i; norm_num), ?_⟩
  intro hcon
  have := congrFun (congrFun hcon 0) 0
  simp [RCov.push, RCov.diag] at this

end Integration.Experiment.JacobianSensitivity
