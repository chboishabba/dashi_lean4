/-
# Row A1a — the constrained projection inherits Lorentz block diagonality

`AveragingLorentzDiagonal` proves that the literal block-averaging operator is
block diagonal in the Lorentz index: a coarse `α`-average never sees a fine
`β`-link for `β ≠ α`.  The constrained part of the piece `R` of

    V = W + Q + R

is the background derivative of the projection onto `ker Q` — the elimination of
the constrained coordinates.  This file proves that that projection, and hence
also its background derivative, is Lorentz block diagonal too, so **the whole
constrained part of `R` drops out of a mixed Lorentz component**.

The algebra is elementary but must include the *inverse*, since the projection
is `Π = 1 − Qᵀ (Q Qᵀ)⁻¹ Q`.  The inverse step is proved without any block-matrix
reindexing, by the observation that Lorentz block diagonality is exactly
commutation with the four Lorentz component projectors
(`isLorentzDiagonal_iff_commute`), a property manifestly inherited by inverses.

Main statements.

* `IsLorentzDiagonal` : `M (α,i) (β,j) = 0` whenever `α ≠ β` — stated for
  rectangular matrices, so it applies to the averaging operator itself.
* `IsLorentzDiagonal.mul`, `.transpose`, `.add`, `.sub`, `.smul`, `.inv` :
  closure properties.
* `kerProjection_mul_eq_zero`, `kerProjection_idem` : `Π` really is the
  projection annihilating the constrained directions.
* `IsLorentzDiagonal.kerProjection` : `Π` is Lorentz block diagonal.
* `deriv_kerProjection_mixed_zero` : along an arbitrary background family whose
  averaging operator stays Lorentz diagonal, every mixed entry of `Π` has
  vanishing background derivative — to all orders
  (`iteratedDeriv_kerProjection_mixed_zero`).
-/
import Mathlib

namespace YangMills

open Matrix

/-! ## 1. Lorentz block diagonal matrices -/

/-- A matrix whose row and column indices carry a Lorentz index is *Lorentz
block diagonal* when it has no entries mixing two different Lorentz indices. -/
def IsLorentzDiagonal {α β : Type*} (M : Matrix (Fin 4 × α) (Fin 4 × β) ℝ) : Prop :=
  ∀ al be : Fin 4, ∀ i j, al ≠ be → M (al, i) (be, j) = 0

namespace IsLorentzDiagonal

variable {α β γ : Type*}

theorem add {M N : Matrix (Fin 4 × α) (Fin 4 × β) ℝ}
    (hM : IsLorentzDiagonal M) (hN : IsLorentzDiagonal N) : IsLorentzDiagonal (M + N) := by
  intro al be i j h
  simp [hM al be i j h, hN al be i j h]

theorem neg {M : Matrix (Fin 4 × α) (Fin 4 × β) ℝ} (hM : IsLorentzDiagonal M) :
    IsLorentzDiagonal (-M) := by
  intro al be i j h; simp [hM al be i j h]

theorem sub {M N : Matrix (Fin 4 × α) (Fin 4 × β) ℝ}
    (hM : IsLorentzDiagonal M) (hN : IsLorentzDiagonal N) : IsLorentzDiagonal (M - N) := by
  intro al be i j h
  simp [hM al be i j h, hN al be i j h]

theorem smul {M : Matrix (Fin 4 × α) (Fin 4 × β) ℝ} (hM : IsLorentzDiagonal M) (t : ℝ) :
    IsLorentzDiagonal (t • M) := by
  intro al be i j h; simp [hM al be i j h]

theorem transpose {M : Matrix (Fin 4 × α) (Fin 4 × β) ℝ} (hM : IsLorentzDiagonal M) :
    IsLorentzDiagonal Mᵀ := by
  intro al be i j h
  exact hM be al j i (Ne.symm h)

theorem mul [Fintype γ] {M : Matrix (Fin 4 × α) (Fin 4 × γ) ℝ}
    {N : Matrix (Fin 4 × γ) (Fin 4 × β) ℝ}
    (hM : IsLorentzDiagonal M) (hN : IsLorentzDiagonal N) : IsLorentzDiagonal (M * N) := by
  intro al be i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : p.1 = al
  · have : p.1 ≠ be := by rw [hp]; exact h
    have := hN p.1 be p.2 j this
    simp [show (p.1, p.2) = p from rfl] at this
    simp [this]
  · have := hM al p.1 i p.2 (Ne.symm hp)
    simp [show (p.1, p.2) = p from rfl] at this
    simp [this]

end IsLorentzDiagonal

theorem isLorentzDiagonal_one {α : Type*} [DecidableEq α] :
    IsLorentzDiagonal (1 : Matrix (Fin 4 × α) (Fin 4 × α) ℝ) := by
  intro al be i j h
  simp [Prod.ext_iff, h]

/-- The projector onto the Lorentz component `c`. -/
def lorentzProj (α : Type*) [DecidableEq α] (c : Fin 4) :
    Matrix (Fin 4 × α) (Fin 4 × α) ℝ :=
  Matrix.diagonal fun p => if p.1 = c then 1 else 0

/-- **Lorentz block diagonality is commutation with the Lorentz projectors.** -/
theorem isLorentzDiagonal_iff_commute {α : Type*} [DecidableEq α] [Fintype α]
    (M : Matrix (Fin 4 × α) (Fin 4 × α) ℝ) :
    IsLorentzDiagonal M ↔ ∀ c, M * lorentzProj α c = lorentzProj α c * M := by
  constructor
  · intro hM c
    ext p q
    rw [lorentzProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : p.1 = q.1
    · rw [hpq]; ring
    · have h0 : M p q = 0 := by
        have := hM p.1 q.1 p.2 q.2 hpq
        simpa using this
      rw [h0]; ring
  · intro hM al be i j h
    have := congrFun (congrFun (hM be) (al, i)) (be, j)
    rw [lorentzProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simpa [h] using this

/-- **The inverse of a Lorentz block diagonal matrix is Lorentz block
diagonal.** -/
theorem IsLorentzDiagonal.inv {α : Type*} [DecidableEq α] [Fintype α]
    {M : Matrix (Fin 4 × α) (Fin 4 × α) ℝ} (hM : IsLorentzDiagonal M)
    (hdet : IsUnit M.det) : IsLorentzDiagonal M⁻¹ := by
  rw [isLorentzDiagonal_iff_commute] at hM ⊢
  intro c
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  calc M⁻¹ * lorentzProj α c
      = M⁻¹ * lorentzProj α c * (M * M⁻¹) := by rw [hMM, Matrix.mul_one]
    _ = M⁻¹ * (lorentzProj α c * M) * M⁻¹ := by simp [Matrix.mul_assoc]
    _ = M⁻¹ * (M * lorentzProj α c) * M⁻¹ := by rw [hM c]
    _ = M⁻¹ * M * lorentzProj α c * M⁻¹ := by simp [Matrix.mul_assoc]
    _ = lorentzProj α c * M⁻¹ := by rw [hMM', Matrix.one_mul]

/-! ## 2. The constrained projection -/

variable {c n : Type*} [Fintype c] [DecidableEq c] [Fintype n] [DecidableEq n]

/-- The projection eliminating the constrained coordinates,
`Π = 1 − Qᵀ (Q Qᵀ)⁻¹ Q`. -/
noncomputable def kerProjection (Q : Matrix (Fin 4 × c) (Fin 4 × n) ℝ) :
    Matrix (Fin 4 × n) (Fin 4 × n) ℝ :=
  1 - Qᵀ * (Q * Qᵀ)⁻¹ * Q

/-- `Π` annihilates the constrained directions: `Q Π = 0`. -/
theorem kerProjection_mul_eq_zero (Q : Matrix (Fin 4 × c) (Fin 4 × n) ℝ)
    (hdet : IsUnit (Q * Qᵀ).det) : Q * kerProjection Q = 0 := by
  have h : (Q * Qᵀ) * (Q * Qᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  rw [kerProjection, Matrix.mul_sub, Matrix.mul_one]
  have : Q * (Qᵀ * (Q * Qᵀ)⁻¹ * Q) = ((Q * Qᵀ) * (Q * Qᵀ)⁻¹) * Q := by
    simp [Matrix.mul_assoc]
  rw [this, h, Matrix.one_mul, sub_self]

/-- `Π` is idempotent. -/
theorem kerProjection_idem (Q : Matrix (Fin 4 × c) (Fin 4 × n) ℝ)
    (hdet : IsUnit (Q * Qᵀ).det) :
    kerProjection Q * kerProjection Q = kerProjection Q := by
  have h : (Q * Qᵀ) * (Q * Qᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have key : (Qᵀ * (Q * Qᵀ)⁻¹ * Q) * (Qᵀ * (Q * Qᵀ)⁻¹ * Q) = Qᵀ * (Q * Qᵀ)⁻¹ * Q := by
    have : (Qᵀ * (Q * Qᵀ)⁻¹ * Q) * (Qᵀ * (Q * Qᵀ)⁻¹ * Q)
        = Qᵀ * (Q * Qᵀ)⁻¹ * ((Q * Qᵀ) * (Q * Qᵀ)⁻¹) * Q := by
      simp [Matrix.mul_assoc]
    rw [this, h, Matrix.mul_one]
  rw [kerProjection, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, key]
  simp only [Matrix.one_mul]
  abel

/-- **The constrained projection is Lorentz block diagonal.**  This is the
structural reason the constrained part of `R` cannot contribute to a mixed
Lorentz component of the constrained first variation. -/
theorem IsLorentzDiagonal.kerProjection {Q : Matrix (Fin 4 × c) (Fin 4 × n) ℝ}
    (hQ : IsLorentzDiagonal Q) (hdet : IsUnit (Q * Qᵀ).det) :
    IsLorentzDiagonal (YangMills.kerProjection Q) :=
  isLorentzDiagonal_one.sub
    ((hQ.transpose.mul ((hQ.mul hQ.transpose).inv hdet)).mul hQ)

/-- Mixed entries of the constrained projection vanish. -/
theorem kerProjection_mixed_zero {Q : Matrix (Fin 4 × c) (Fin 4 × n) ℝ}
    (hQ : IsLorentzDiagonal Q) (hdet : IsUnit (Q * Qᵀ).det)
    {al be : Fin 4} (i j : n) (h : al ≠ be) :
    kerProjection Q (al, i) (be, j) = 0 :=
  hQ.kerProjection hdet al be i j h

/-! ## 3. The background derivative of the constrained projection -/

/-- **`R_constrained` vanishes on mixed Lorentz components.**  Along any
background family whose averaging operator stays Lorentz block diagonal and
nondegenerate, the mixed entries of the eliminating projection are constantly
zero. -/
theorem kerProjection_mixed_const {Qf : ℝ → Matrix (Fin 4 × c) (Fin 4 × n) ℝ}
    (hQ : ∀ t, IsLorentzDiagonal (Qf t)) (hdet : ∀ t, IsUnit ((Qf t) * (Qf t)ᵀ).det)
    {al be : Fin 4} (i j : n) (h : al ≠ be) :
    (fun t : ℝ => kerProjection (Qf t) (al, i) (be, j)) = fun _ => 0 :=
  funext fun t => kerProjection_mixed_zero (hQ t) (hdet t) i j h

theorem deriv_kerProjection_mixed_zero {Qf : ℝ → Matrix (Fin 4 × c) (Fin 4 × n) ℝ}
    (hQ : ∀ t, IsLorentzDiagonal (Qf t)) (hdet : ∀ t, IsUnit ((Qf t) * (Qf t)ᵀ).det)
    {al be : Fin 4} (i j : n) (h : al ≠ be) (t0 : ℝ) :
    deriv (fun t : ℝ => kerProjection (Qf t) (al, i) (be, j)) t0 = 0 := by
  rw [kerProjection_mixed_const hQ hdet i j h]; simp

theorem iteratedDeriv_kerProjection_mixed_zero
    {Qf : ℝ → Matrix (Fin 4 × c) (Fin 4 × n) ℝ}
    (hQ : ∀ t, IsLorentzDiagonal (Qf t)) (hdet : ∀ t, IsUnit ((Qf t) * (Qf t)ᵀ).det)
    {al be : Fin 4} (i j : n) (h : al ≠ be) {k : ℕ} (hk : 0 < k) (t0 : ℝ) :
    iteratedDeriv k (fun t : ℝ => kerProjection (Qf t) (al, i) (be, j)) t0 = 0 := by
  rw [kerProjection_mixed_const hQ hdet i j h, iteratedDeriv_const, if_neg hk.ne']

end YangMills
