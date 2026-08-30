import Spine.SchurComplement

/-!
# The Schur complement for a vector hidden block

`Spine.SchurComplement` owns the elimination of a *scalar* hidden direction from
a quadratic form.  The frontier item it left open was the block version: a
hidden space of arbitrary dimension, i.e.

```
S = D − Bᵀ A⁻¹ B
```

together with its minimum characterisation and the resulting operator-style
coercivity transfer.  This file closes that item.

Fix real inner product spaces `H` (hidden) and `V` (visible), a self-adjoint
positive semidefinite `A : H →ₗ[ℝ] H` admitting a right inverse `Ainv`, a
coupling `B : V →ₗ[ℝ] H`, and a visible form `d : V → ℝ`.  The coupled form is

```
coupledB A B d x y = ⟪A x, x⟫ + 2 ⟪B y, x⟫ + d y
```

and its Schur complement is

```
schurB Ainv B d y = d y − ⟪Ainv (B y), B y⟫ .
```

Contents.

* `coupledB_eq_schurB_add` — completing the square in the hidden *block*: the
  coupled form is the Schur complement plus `⟪A z, z⟫` for the deviation `z`
  from the optimal hidden vector `hiddenMinB = −A⁻¹ B y`;
* `coupledB_hiddenMinB`, `coupledB_ge_schurB`, `schurB_isLeast` — the Schur
  complement **is** the minimum of the coupled form over the hidden block, and
  it is attained;
* `schurB_coercive` — the quantitative transfer, `S ≥ (δ − η)` pointwise in the
  quadratic scale: a visible form bounded below by `δ‖y‖²` and a coupling
  correction bounded above by `η‖y‖²` give `S y ≥ (δ − η)‖y‖²`.  This is the
  `S ≥ (δ − η)I` inequality in its quadratic-form reading;
* `schurB_pos_of_coercive` — hence strict positivity away from `0`;
* `schurB_eq_schur` — the block owner **specialises to** the scalar owner: with
  `H = ℝ`, `A = a • id` and `B y = ⟪b, y⟫`, `schurB` is literally
  `Spine.SchurComplement.schur a b d`.  So the rank-one file is a corollary, not
  a parallel development.

Every hypothesis is stated as data the caller supplies (self-adjointness, a
right inverse, positive semidefiniteness); nothing is assumed about dimension,
completeness, or the existence of a spectral decomposition.
-/

open RealInnerProductSpace

namespace Spine
namespace SchurBlock

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coupled quadratic form on `hidden × visible`, with a vector hidden
block. -/
noncomputable def coupledB (A : H →ₗ[ℝ] H) (B : V →ₗ[ℝ] H) (d : V → ℝ) (x : H) (y : V) : ℝ :=
  ⟪A x, x⟫ + 2 * ⟪B y, x⟫ + d y

/-- The block Schur complement `D − Bᵀ A⁻¹ B`. -/
noncomputable def schurB (Ainv : H →ₗ[ℝ] H) (B : V →ₗ[ℝ] H) (d : V → ℝ) (y : V) : ℝ :=
  d y - ⟪Ainv (B y), B y⟫

/-- The hidden vector at which the coupled form is minimised. -/
noncomputable def hiddenMinB (Ainv : H →ₗ[ℝ] H) (B : V →ₗ[ℝ] H) (y : V) : H := -(Ainv (B y))

variable {A Ainv : H →ₗ[ℝ] H} {B : V →ₗ[ℝ] H} {d : V → ℝ}

/-- **Completing the square in the hidden block.** -/
theorem coupledB_eq_schurB_add (hsa : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hinv : ∀ z : H, A (Ainv z) = z) (x : H) (y : V) :
    coupledB A B d x y
      = schurB Ainv B d y
        + ⟪A (x - hiddenMinB Ainv B y), x - hiddenMinB Ainv B y⟫ := by
  have hAx₀ : A (hiddenMinB Ainv B y) = -(B y) := by
    simp [hiddenMinB, hinv]
  have hexp : ⟪A (x - hiddenMinB Ainv B y), x - hiddenMinB Ainv B y⟫
      = ⟪A x, x⟫ - ⟪A x, hiddenMinB Ainv B y⟫ - ⟪A (hiddenMinB Ainv B y), x⟫
        + ⟪A (hiddenMinB Ainv B y), hiddenMinB Ainv B y⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  have h1 : ⟪A x, hiddenMinB Ainv B y⟫ = -⟪B y, x⟫ := by
    rw [hsa, hAx₀, inner_neg_right, real_inner_comm]
  have h2 : ⟪A (hiddenMinB Ainv B y), x⟫ = -⟪B y, x⟫ := by
    rw [hAx₀, inner_neg_left]
  have h3 : ⟪A (hiddenMinB Ainv B y), hiddenMinB Ainv B y⟫ = ⟪Ainv (B y), B y⟫ := by
    rw [hAx₀]
    simp [hiddenMinB, real_inner_comm]
  rw [hexp, h1, h2, h3]
  simp only [coupledB, schurB]
  ring

/-- The coupled form at the optimal hidden vector *is* the Schur complement. -/
theorem coupledB_hiddenMinB (hsa : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hinv : ∀ z : H, A (Ainv z) = z) (y : V) :
    coupledB A B d (hiddenMinB Ainv B y) y = schurB Ainv B d y := by
  rw [coupledB_eq_schurB_add hsa hinv]
  simp

/-- **The Schur complement is a lower bound** for the coupled form, for a
positive semidefinite hidden block. -/
theorem coupledB_ge_schurB (hsa : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hinv : ∀ z : H, A (Ainv z) = z) (hpsd : ∀ z : H, 0 ≤ ⟪A z, z⟫) (x : H) (y : V) :
    schurB Ainv B d y ≤ coupledB A B d x y := by
  rw [coupledB_eq_schurB_add hsa hinv]
  exact le_add_of_nonneg_right (hpsd _)

/-- **The minimum characterisation.**  Eliminating the hidden block by
minimisation produces exactly the Schur complement. -/
theorem schurB_isLeast (hsa : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hinv : ∀ z : H, A (Ainv z) = z) (hpsd : ∀ z : H, 0 ≤ ⟪A z, z⟫) (y : V) :
    IsLeast {t : ℝ | ∃ x : H, coupledB A B d x y = t} (schurB Ainv B d y) :=
  ⟨⟨hiddenMinB Ainv B y, coupledB_hiddenMinB hsa hinv y⟩, by
    rintro t ⟨x, rfl⟩
    exact coupledB_ge_schurB hsa hinv hpsd x y⟩

/-- **The coercivity transfer, `S ≥ (δ − η)`.**  If the visible form dominates
`δ‖y‖²` and the coupling correction is dominated by `η‖y‖²`, the effective form
dominates `(δ − η)‖y‖²`. -/
theorem schurB_coercive {δ η : ℝ} (hd : ∀ y : V, δ * ‖y‖ ^ 2 ≤ d y)
    (hcoup : ∀ y : V, ⟪Ainv (B y), B y⟫ ≤ η * ‖y‖ ^ 2) (y : V) :
    (δ - η) * ‖y‖ ^ 2 ≤ schurB Ainv B d y := by
  simp only [schurB]
  nlinarith [hd y, hcoup y]

/-- And therefore strict positivity away from the origin when `η < δ`. -/
theorem schurB_pos_of_coercive {δ η : ℝ} (hd : ∀ y : V, δ * ‖y‖ ^ 2 ≤ d y)
    (hcoup : ∀ y : V, ⟪Ainv (B y), B y⟫ ≤ η * ‖y‖ ^ 2) (hlt : η < δ) {y : V} (hy : y ≠ 0) :
    0 < schurB Ainv B d y := by
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  have := schurB_coercive hd hcoup y
  nlinarith [sub_pos.mpr hlt]

/-! ## The scalar owner is the rank-one case -/

/-- **`Spine.SchurComplement.schur` is the one-dimensional hidden block.**  Take
`H = ℝ`, `A = a • id`, `Ainv = a⁻¹ • id` and `B y = ⟪b, y⟫`. -/
theorem schurB_eq_schur {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (a : ℝ) (b : W) (dv : W → ℝ) (y : W) :
    schurB (a⁻¹ • LinearMap.id) (innerSL ℝ b).toLinearMap dv y
      = SchurComplement.schur a b dv y := by
  simp only [schurB, SchurComplement.schur, LinearMap.smul_apply, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  simp only [RCLike.inner_apply, conj_trivial, div_eq_mul_inv]
  ring

end SchurBlock
end Spine
