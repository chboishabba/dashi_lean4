/-
# Row A1a — the fixed-constraint-coordinate Gaussian `Â(U) = C(U)ᵀ A(U) C(U)`

The block-spin Gaussian of the Bałaban step is *not* an independently moving
delta constraint on the fluctuation field.  The constrained coordinates are
eliminated by a background-dependent substitution `B' = C(U) B`, after which the
Gaussian is unconstrained in the surviving coordinates with covariance the
inverse of the **restricted operator**

    Â(U) = C(U)ᵀ A(U) C(U).

This file fixes that object and proves the two things the Row A1a Gaussian datum
needs.

## 1. The floor

`restricted_quadForm` : the restricted quadratic form is the ambient form
evaluated on the substituted coordinates, `x·Â x = (Cx)·A(Cx)`.  Hence

* `restricted_floor` : an ambient coercivity `a` for `A` together with a
  lower bound `σ` for the substitution (`‖Cx‖² ≥ σ‖x‖²`) gives the restricted
  floor `a·σ`;
* `restricted_pos` : with `a, σ > 0` the restricted form is strictly positive on
  every nonzero vector — this is the shape of the datum `b_patch > 0`;
* `restricted_floor_needs_injectivity` : if `C` kills a vector the restricted
  form degenerates there whatever `A` is, so the substitution bound is
  load-bearing.

## 2. The first variation

`hasMatDerivAt_restricted` : for differentiable background families,

    D Â = C'ᵀ A C + Cᵀ A' C + Cᵀ A C'.

`restrictedVariation_eq_W_add_Q_add_R` identifies this with the `V = W + Q + R`
decomposition used throughout Row A1a:

    W = Cᵀ A' C   (the genuine operator variation),
    Q = C'ᵀ A C,  R = Cᵀ A C'   (the two coordinate-connection terms).

`connection_transpose` proves `Q = Rᵀ` whenever `A` is symmetric — so the two
connection terms are *not* independent, and on the diagonal `V_ii = W_ii + 2R_ii`
(`restrictedVariation_diag`).  This halves the error budget the patch producer
must control, and `restrictedVariation_entry_lower_bound` is the resulting
compiler: `W_ii ≥ c` and `|R_ii| ≤ e` on a patch give `V_ii ≥ c − 2e`.

**Honest status.**  Nothing here computes `A'` or `C'` for Bałaban's
construction, and nothing asserts a value for `a`, `σ` or `b_patch`.  What is
proved is the algebra and the calculus that the source data feed into.
-/
import RequestProject.YangMills.MatrixFamilyDerivative

namespace YangMills

open Matrix

variable {n m : Type*} [Fintype n]

/-- The quadratic form of a matrix. -/
def quadForm (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

/-- The restricted (fixed-constraint-coordinate) operator `Â = CᵀAC`. -/
def restricted (C : Matrix n m ℝ) (A : Matrix n n ℝ) : Matrix m m ℝ := Cᵀ * A * C

theorem restricted_transpose (C : Matrix n m ℝ) {A : Matrix n n ℝ} (hA : Aᵀ = A) :
    (restricted C A)ᵀ = restricted C A := by
  unfold restricted
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
    Matrix.mul_assoc]

/-- **The restricted form is the ambient form on the substituted coordinates.** -/
theorem restricted_quadForm [Fintype m] (C : Matrix n m ℝ) (A : Matrix n n ℝ) (x : m → ℝ) :
    quadForm (restricted C A) x = quadForm A (C *ᵥ x) := by
  unfold quadForm restricted
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **The restricted floor.**  Ambient coercivity `a` plus a substitution lower
bound `σ` give the restricted floor `a·σ`. -/
theorem restricted_floor [Fintype m] {C : Matrix n m ℝ} {A : Matrix n n ℝ} {a sigma : ℝ}
    (ha : 0 ≤ a)
    (hA : ∀ y : n → ℝ, a * (y ⬝ᵥ y) ≤ quadForm A y)
    (hC : ∀ x : m → ℝ, sigma * (x ⬝ᵥ x) ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x))
    (x : m → ℝ) :
    a * sigma * (x ⬝ᵥ x) ≤ quadForm (restricted C A) x := by
  rw [restricted_quadForm]
  have h1 : a * ((C *ᵥ x) ⬝ᵥ (C *ᵥ x)) ≤ quadForm A (C *ᵥ x) := hA _
  have h2 : a * (sigma * (x ⬝ᵥ x)) ≤ a * ((C *ᵥ x) ⬝ᵥ (C *ᵥ x)) :=
    mul_le_mul_of_nonneg_left (hC x) ha
  calc a * sigma * (x ⬝ᵥ x) = a * (sigma * (x ⬝ᵥ x)) := by ring
    _ ≤ a * ((C *ᵥ x) ⬝ᵥ (C *ᵥ x)) := h2
    _ ≤ quadForm A (C *ᵥ x) := h1

/-- With strictly positive ambient coercivity and substitution bound, the
restricted form is strictly positive on nonzero vectors. -/
theorem restricted_pos [Fintype m] {C : Matrix n m ℝ} {A : Matrix n n ℝ} {a sigma : ℝ}
    (ha : 0 < a) (hs : 0 < sigma)
    (hA : ∀ y : n → ℝ, a * (y ⬝ᵥ y) ≤ quadForm A y)
    (hC : ∀ x : m → ℝ, sigma * (x ⬝ᵥ x) ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x))
    {x : m → ℝ} (hx : x ≠ 0) :
    0 < quadForm (restricted C A) x := by
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
  have hxx : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne hnn (fun h => hx (dotProduct_self_eq_zero.1 h.symm))
  have hfloor := restricted_floor (le_of_lt ha) hA hC x
  have hpos : 0 < a * sigma * (x ⬝ᵥ x) := mul_pos (mul_pos ha hs) hxx
  linarith

/-- **The substitution bound is load-bearing.**  If `C` annihilates a nonzero
vector then the restricted form vanishes there for *every* ambient operator, no
matter how coercive. -/
theorem restricted_floor_needs_injectivity [Fintype m] {C : Matrix n m ℝ} (A : Matrix n n ℝ)
    {x : m → ℝ} (hx : C *ᵥ x = 0) :
    quadForm (restricted C A) x = 0 := by
  rw [restricted_quadForm, hx]
  simp [quadForm]

/-! ## The first variation of the restricted operator -/

/-- **`D Â = C'ᵀ A C + Cᵀ A' C + Cᵀ A C'`.** -/
theorem hasMatDerivAt_restricted {C : ℝ → Matrix n m ℝ} {A : ℝ → Matrix n n ℝ}
    {C' : Matrix n m ℝ} {A' : Matrix n n ℝ} {t : ℝ}
    (hC : HasMatDerivAt C C' t) (hA : HasMatDerivAt A A' t) :
    HasMatDerivAt (fun s => restricted (C s) (A s))
      (C'ᵀ * A t * C t + (C t)ᵀ * A' * C t + (C t)ᵀ * A t * C') t :=
  HasMatDerivAt.mul₃ hC.transpose hA hC

/-- The three source-native pieces of the restricted first variation. -/
def opVariation (C : Matrix n m ℝ) (A' : Matrix n n ℝ) : Matrix m m ℝ := Cᵀ * A' * C

/-- The first connection term `Q = C'ᵀ A C`. -/
def connectionLeft (C C' : Matrix n m ℝ) (A : Matrix n n ℝ) : Matrix m m ℝ := C'ᵀ * A * C

/-- The second connection term `R = Cᵀ A C'`. -/
def connectionRight (C C' : Matrix n m ℝ) (A : Matrix n n ℝ) : Matrix m m ℝ := Cᵀ * A * C'

/-- **`V = W + Q + R` for the restricted Gaussian.** -/
theorem restrictedVariation_eq_W_add_Q_add_R {C : ℝ → Matrix n m ℝ} {A : ℝ → Matrix n n ℝ}
    {C' : Matrix n m ℝ} {A' : Matrix n n ℝ} {t : ℝ}
    (hC : HasMatDerivAt C C' t) (hA : HasMatDerivAt A A' t) :
    HasMatDerivAt (fun s => restricted (C s) (A s))
      (opVariation (C t) A' + connectionLeft (C t) C' (A t)
        + connectionRight (C t) C' (A t)) t := by
  have h := hasMatDerivAt_restricted hC hA
  have hval : C'ᵀ * A t * C t + (C t)ᵀ * A' * C t + (C t)ᵀ * A t * C'
      = opVariation (C t) A' + connectionLeft (C t) C' (A t)
        + connectionRight (C t) C' (A t) := by
    unfold opVariation connectionLeft connectionRight
    abel
  rwa [hval] at h

/-- **The two connection terms are transposes of one another** when the ambient
operator is symmetric.  So they are not independent error sources. -/
theorem connection_transpose (C C' : Matrix n m ℝ) {A : Matrix n n ℝ} (hA : Aᵀ = A) :
    connectionLeft C C' A = (connectionRight C C' A)ᵀ := by
  unfold connectionLeft connectionRight
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
    Matrix.mul_assoc]

/-- Consequently the diagonal entries of the restricted first variation are
`V_ii = W_ii + 2·R_ii`. -/
theorem restrictedVariation_diag (C C' : Matrix n m ℝ) {A : Matrix n n ℝ} (hA : Aᵀ = A)
    (A' : Matrix n n ℝ) (i : m) :
    (opVariation C A' + connectionLeft C C' A + connectionRight C C' A) i i
      = opVariation C A' i i + 2 * connectionRight C C' A i i := by
  have h : connectionLeft C C' A i i = connectionRight C C' A i i := by
    rw [connection_transpose C C' hA]; rfl
  simp only [Matrix.add_apply, h]
  ring

/-- **The patch compiler on the restricted symbol.**  On a set of background
data where the genuine operator variation entry is at least `c` and the
connection entry is at most `e` in absolute value, the full restricted variation
entry is at least `c − 2e`.  This is the `V ≥ c − (|Q| + |R|)` estimate with the
`Q = Rᵀ` improvement. -/
theorem restrictedVariation_entry_lower_bound (C C' : Matrix n m ℝ) {A : Matrix n n ℝ}
    (hA : Aᵀ = A) (A' : Matrix n n ℝ) (i : m) {c e : ℝ}
    (hW : c ≤ opVariation C A' i i)
    (hR : |connectionRight C C' A i i| ≤ e) :
    c - 2 * e ≤ (opVariation C A' + connectionLeft C C' A + connectionRight C C' A) i i := by
  rw [restrictedVariation_diag C C' hA A' i]
  have := neg_abs_le (connectionRight C C' A i i)
  linarith

/-- **A Wilson-only certificate is still not a certificate.**  Even with
`Q = Rᵀ`, there are data whose operator-variation entry is strictly positive
while the full restricted variation entry vanishes: the connection term must be
bounded, not ignored. -/
theorem wilsonOnly_not_sufficient :
    ∃ (C C' : Matrix (Fin 1) (Fin 1) ℝ) (A A' : Matrix (Fin 1) (Fin 1) ℝ),
      Aᵀ = A ∧ 0 < opVariation C A' 0 0 ∧
      (opVariation C A' + connectionLeft C C' A + connectionRight C C' A) 0 0 = 0 := by
  refine ⟨1, Matrix.of fun _ _ => -(1 : ℝ) / 2, 1, 1, by simp, ?_, ?_⟩
  · simp [opVariation]
  · simp [opVariation, connectionLeft, connectionRight]
    norm_num

end YangMills
