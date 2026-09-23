/-
# Row A1a — the constraint-annihilator (KKT) reduction, and what it does *not* buy

A covector that annihilates the kernel of a constraint operator is longitudinal:
it lies in the range of the constraint's transpose.  In the KKT language,

    g|_{ker L} = 0  ⟹  P g = 0  ⟹  g ∈ im Lᵀ,

where `P` is the orthogonal projection onto `ker L`.  This is the machinery one
would like to apply to the coordinate-connection covectors of the restricted
Gaussian `Â = CᵀAC`: if the `C'`-connection contribution were longitudinal with
respect to the admissible carrier, it might project away instead of costing an
absolute-value error.

This file proves the reduction, in the finite-dimensional real setting where the
lattice problem lives.

* `annihilates_ker_iff_mem_range_transpose` : `(∀ x, Lx = 0 → g·x = 0)` **iff**
  `∃ y, g = Lᵀy`.  Both directions; the easy direction is what makes it a
  characterisation rather than a one-way estimate.
* `orthogonalProjection_ker_eq_zero` : the projection form `P g = 0`.

And, crucially, the honest limitation:

* `longitudinal_does_not_cancel_connection` : there are data in which the
  constraint kernel is trivial — so *every* covector is longitudinal — while the
  connection term `Cᵀ A C'` of `ConstraintCoordinateGaussian` is nonzero.  So the
  annihilator reduction alone does **not** cancel the `C'` contribution to the
  restricted Gaussian.  The weld that would be needed is an identification of the
  KKT projection with the same `CᵀAC` carrier, and that identification is not
  claimed here.
-/
import RequestProject.YangMills.ConstraintCoordinateGaussian

namespace YangMills

open Matrix
open scoped InnerProductSpace

/-- **The constraint-annihilator characterisation.**  A covector annihilates the
kernel of `L` exactly when it is longitudinal, i.e. in the range of `Lᵀ`. -/
theorem annihilates_ker_iff_mem_range_transpose {c n : Type*} [Fintype c] [Fintype n]
    (L : Matrix c n ℝ) (g : n → ℝ) :
    (∀ x : n → ℝ, L *ᵥ x = 0 → g ⬝ᵥ x = 0) ↔ ∃ y : c → ℝ, Lᵀ *ᵥ y = g := by
  classical
  constructor
  · intro h
    set T : EuclideanSpace ℝ c →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin Lᵀ with hT
    set W := LinearMap.range T with hW
    have hinner : ∀ x y : EuclideanSpace ℝ n, ⟪x, y⟫_ℝ = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
      intro x y
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    have key : ∀ (y : EuclideanSpace ℝ c) (v : EuclideanSpace ℝ n),
        ⟪T y, v⟫_ℝ = (L *ᵥ (WithLp.ofLp v)) ⬝ᵥ (WithLp.ofLp y) := by
      intro y v
      rw [hinner]
      have hTy : WithLp.ofLp (T y) = Lᵀ *ᵥ (WithLp.ofLp y) := rfl
      rw [hTy, dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
    have hperp : ∀ v : EuclideanSpace ℝ n, v ∈ Wᗮ ↔ L *ᵥ (WithLp.ofLp v) = 0 := by
      intro v
      constructor
      · intro hv
        have hall : ∀ y : EuclideanSpace ℝ c,
            (L *ᵥ (WithLp.ofLp v)) ⬝ᵥ (WithLp.ofLp y) = 0 := by
          intro y
          rw [← key y v]
          exact hv (T y) ⟨y, rfl⟩
        have hself := hall (WithLp.toLp 2 (L *ᵥ (WithLp.ofLp v)))
        simpa using dotProduct_self_eq_zero.1 hself
      · intro hv u hu
        obtain ⟨y, rfl⟩ := hu
        rw [key y v, hv, zero_dotProduct]
    have hg : (WithLp.toLp 2 g : EuclideanSpace ℝ n) ∈ Wᗮᗮ := by
      intro u hu
      have h1 : L *ᵥ (WithLp.ofLp u) = 0 := (hperp u).1 hu
      rw [hinner]
      have hcomm : (WithLp.ofLp u) ⬝ᵥ g = g ⬝ᵥ (WithLp.ofLp u) := dotProduct_comm _ _
      simpa [hcomm] using h u h1
    rw [Submodule.orthogonal_orthogonal] at hg
    obtain ⟨y, hy⟩ := hg
    refine ⟨WithLp.ofLp y, ?_⟩
    have hTy : WithLp.ofLp (T y) = Lᵀ *ᵥ (WithLp.ofLp y) := rfl
    rw [← hTy, hy]
  · rintro ⟨y, rfl⟩ x hx
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, hx, zero_dotProduct]

/-- **The projection form `P g = 0`.**  A covector annihilating the constraint
kernel has vanishing orthogonal projection onto that kernel. -/
theorem orthogonalProjection_ker_eq_zero {c n : Type*} [Fintype c] [Fintype n] [DecidableEq n]
    (L : Matrix c n ℝ) (g : n → ℝ)
    (h : ∀ x : n → ℝ, L *ᵥ x = 0 → g ⬝ᵥ x = 0) :
    (LinearMap.ker (Matrix.toEuclideanLin L)).orthogonalProjection
        (WithLp.toLp 2 g : EuclideanSpace ℝ n) = 0 := by
  classical
  refine Submodule.orthogonalProjection_eq_zero_iff.mpr ?_
  intro u hu
  have hu0 : L *ᵥ (WithLp.ofLp u) = 0 := by
    have : Matrix.toEuclideanLin L u = 0 := hu
    have h2 : WithLp.ofLp (Matrix.toEuclideanLin L u) = L *ᵥ (WithLp.ofLp u) := rfl
    rw [← h2, this]
    rfl
  have hgz : g ⬝ᵥ (WithLp.ofLp u) = 0 := h _ hu0
  have hinner : ⟪u, (WithLp.toLp 2 g : EuclideanSpace ℝ n)⟫_ℝ
      = (WithLp.ofLp u) ⬝ᵥ g := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hinner, dotProduct_comm]
  exact hgz

/-- **The reduction does not, by itself, cancel the connection term.**  Here the
constraint operator is injective, so its kernel is trivial and *every* covector
is longitudinal; nevertheless the coordinate-connection term `Cᵀ A C'` of the
restricted Gaussian is nonzero.  Identifying the KKT projection with the
`CᵀAC` carrier is therefore a further, unproved obligation. -/
theorem longitudinal_does_not_cancel_connection :
    ∃ (L : Matrix (Fin 1) (Fin 1) ℝ) (C C' A : Matrix (Fin 1) (Fin 1) ℝ),
      (∀ g : Fin 1 → ℝ, ∃ y : Fin 1 → ℝ, Lᵀ *ᵥ y = g) ∧
      connectionRight C C' A 0 0 ≠ 0 := by
  refine ⟨1, 1, 1, 1, fun g => ⟨g, by simp⟩, ?_⟩
  simp [connectionRight]

end YangMills
