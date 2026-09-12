/-
**The local block versus the outside world: a real Schur-complement theorem.**

The localization programme suggests replacing the principal compression
`G_H = P_H G P_H*` by the *effective* local operator

    S = D − Bᴴ A⁻¹ B ,      G = [[A, B], [Bᴴ, D]] ,

so that the influence of the discarded exterior coordinates is mediated rather
than ignored.  This file proves the quantitative statements that make that
precise over `ℝ` (the abstract order-socket version of the surrounding Agda
development assumes them; here they are theorems):

* `schur_form_le_full_form` — **the variational inequality.**  For a positive
  semidefinite exterior block `A`, the Schur form is a *lower* bound for the
  full quadratic form on every extension of the local vector:

      yᴴ S y ≤ (x ⊕ y)ᴴ G (x ⊕ y)   for all exterior `x`.

* `schur_form_eq_at_optimum` — and the bound is attained, at
  `x = −A⁻¹B y`: the Schur form *is* the minimum of the full form over
  extensions.  So `S` is the exact local observable of `G`.

* `schur_form_le_compression_form` — the honest structural consequence:
  `yᴴ S y ≤ yᴴ D y`.  The Schur complement never exceeds the plain principal
  compression, because the outside-mediated correction `Bᴴ A⁻¹ B` is positive
  semidefinite.  Hence for a *lower* bound on a local observable the plain
  compression is already the stronger object; the Schur complement is what one
  needs in the other direction, to bound the full form from below by a local
  quantity.

* `schur_coercive` — the quantitative coercivity transfer: if the local block is
  coercive with gap `δ` and the cross correction is bounded by `η`, then

      (δ − η) ‖y‖² ≤ yᴴ S y .

Nothing here refers to `ζ`.
-/
import RiemannAnalytic.LocalWindow

namespace RiemannAnalytic

open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- The Schur complement of the exterior block `A` in `[[A, B], [Bᴴ, D]]`. -/
noncomputable def schurComplement (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) : Matrix n n ℝ :=
  D - Bᴴ * A⁻¹ * B

/-- **The variational inequality.**  With a positive semidefinite exterior
block, the Schur form is a lower bound for the full quadratic form on every
extension of the local vector. -/
theorem schur_form_le_full_form (A : Matrix m m ℝ) [Invertible A] (hA : A.PosSemidef)
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) (x : m → ℝ) (y : n → ℝ) :
    y ᵥ* schurComplement A B D ⬝ᵥ y
      ≤ (Sum.elim x y) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (Sum.elim x y) := by
  have h := schur_complement_eq₁₁ (α := ℝ) B D x y hA.isHermitian
  simp only [star_trivial] at h
  have hnn : 0 ≤ (x + (A⁻¹ * B) *ᵥ y) ᵥ* A ⬝ᵥ (x + (A⁻¹ * B) *ᵥ y) := by
    have := hA.re_dotProduct_nonneg (x + (A⁻¹ * B) *ᵥ y)
    simpa [dotProduct_mulVec, dotProduct_comm] using this
  rw [schurComplement, h]
  linarith

/-- **The bound is attained.**  At the optimal extension `x = −A⁻¹B y` the full
quadratic form equals the Schur form: the Schur complement is the exact local
observable of the full matrix. -/
theorem schur_form_eq_at_optimum (A : Matrix m m ℝ) [Invertible A] (hA : A.PosSemidef)
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) (y : n → ℝ) :
    (Sum.elim (-((A⁻¹ * B) *ᵥ y)) y) ᵥ* (Matrix.fromBlocks A B Bᴴ D)
        ⬝ᵥ (Sum.elim (-((A⁻¹ * B) *ᵥ y)) y)
      = y ᵥ* schurComplement A B D ⬝ᵥ y := by
  have h := schur_complement_eq₁₁ (α := ℝ) B D (-((A⁻¹ * B) *ᵥ y)) y hA.isHermitian
  simp only [star_trivial] at h
  rw [schurComplement, h]
  simp

/-- **The Schur complement never exceeds the plain compression.**  The
outside-mediated correction is positive semidefinite, so replacing the principal
compression by the effective local operator can only lower the local observable. -/
theorem schur_form_le_compression_form (A : Matrix m m ℝ) [Invertible A] (hA : A.PosSemidef)
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) (y : n → ℝ) :
    y ᵥ* schurComplement A B D ⬝ᵥ y ≤ y ᵥ* D ⬝ᵥ y := by
  have h := schur_form_le_full_form A hA B D 0 y
  have h0 : (Sum.elim (0 : m → ℝ) y) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (Sum.elim 0 y)
      = y ᵥ* D ⬝ᵥ y := by
    simp [Matrix.vecMul_fromBlocks, sumElim_dotProduct_sumElim]
  rwa [h0] at h

/-- **Quantitative coercivity transfer.**  If the local block has gap `δ` and the
cross correction is bounded by `η`, the effective local operator retains the gap
`δ − η`.  This is the real-scalar content of the abstract Schur socket. -/
theorem schur_coercive (A : Matrix m m ℝ) [Invertible A] (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    {δ η : ℝ} (y : n → ℝ)
    (hD : δ * (y ⬝ᵥ y) ≤ y ᵥ* D ⬝ᵥ y)
    (hcross : y ᵥ* (Bᴴ * A⁻¹ * B) ⬝ᵥ y ≤ η * (y ⬝ᵥ y)) :
    (δ - η) * (y ⬝ᵥ y) ≤ y ᵥ* schurComplement A B D ⬝ᵥ y := by
  have hsub : y ᵥ* schurComplement A B D ⬝ᵥ y
      = y ᵥ* D ⬝ᵥ y - y ᵥ* (Bᴴ * A⁻¹ * B) ⬝ᵥ y := by
    rw [schurComplement, Matrix.vecMul_sub, sub_dotProduct]
  rw [hsub]
  have : (δ - η) * (y ⬝ᵥ y) = δ * (y ⬝ᵥ y) - η * (y ⬝ᵥ y) := by ring
  rw [this]
  linarith

end RiemannAnalytic
