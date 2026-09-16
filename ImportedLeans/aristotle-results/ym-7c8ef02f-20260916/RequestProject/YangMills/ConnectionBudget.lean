/-
# Row A1a — the connection budget `e` reduced to pivot-solve source data

`RestrictedSymbolPatch` leaves the candidate patch hanging on one number: the
entry budget `e` for the coordinate-connection term `R = CᵀAC'`, which has to
beat `√2/4`.  Until now `e` was an abstract hypothesis.  This file *derives* it
from the data the Bałaban source actually supplies, using the exact pivot solve
of `EliminatedCoordinateDerivative`:

    Q C' = −Q' C,   C' = E·X,   X = −P⁻¹(Q' C),

so that `C'` — and therefore the whole connection term — is controlled by
`(‖E‖, ‖P⁻¹‖, ‖Q'‖, ‖C‖)` together with the ambient operator bound `‖A‖`.

## Contents

* `EntryBound` : the entrywise sup bound, with `transpose`, `neg` and the
  product rule `entryBound_mul` (dimension factor `#γ`, which
  `entryBound_mul_needs_dimension_factor` shows cannot be dropped).
* `connectionBudget` : `#n² · b_C · b_A · b_{C'}`, proved to bound every entry
  of `R = CᵀAC'` (`entryBound_connectionRight`).
* `pivotBudget` : `#c² · #n · b_E · b_{P⁻¹} · b_{Q'} · b_C`, proved to bound the
  substitution derivative `C'` produced by the pivot solve
  (`entryBound_eliminated_derivative`) — no norm of `C'` is assumed, it is
  computed from `Q'`.
* `sourceConnectionBudget` : the composite number, and
  `entryBound_connectionRight_of_source` : every entry of `R` is bounded by it.
* **`connection_budget_certifies_patch`** : if the composite source budget is
  `< √2/4`, the quarter-slab certificate for the *full* restricted symbol
  survives.  This is the exact inequality the `A'`/`Q'` producer now has to meet.
* `pivotBudget_unbounded_in_pivot` : the pivot bound is load-bearing — with a
  degenerating pivot the composite budget exceeds any target, so no patch can be
  certified without pivot control.

**Honest status.**  Nothing here supplies numerical values for `b_A`, `b_C`,
`b_E`, `b_{P⁻¹}` or `b_{Q'}`; those are exactly the literal source data still
missing.  Row A1 is not closed.  What is closed is the reduction of the abstract
budget `e` to those five numbers plus two dimension counts.
-/
import RequestProject.YangMills.ConstraintCoordinateGaussian
import RequestProject.YangMills.EliminatedCoordinateDerivative
import RequestProject.YangMills.RestrictedSymbolPatch

namespace YangMills

open Matrix

/-- The entrywise sup bound on a matrix. -/
def EntryBound {α β : Type*} (M : Matrix α β ℝ) (b : ℝ) : Prop := ∀ i j, |M i j| ≤ b

theorem entryBound_transpose {α β : Type*} {M : Matrix α β ℝ} {b : ℝ} (h : EntryBound M b) :
    EntryBound Mᵀ b := fun i j => h j i

theorem entryBound_neg {α β : Type*} {M : Matrix α β ℝ} {b : ℝ} (h : EntryBound M b) :
    EntryBound (-M) b := by
  intro i j
  simpa using h i j

theorem entryBound_nonneg {α β : Type*} [Nonempty α] [Nonempty β] {M : Matrix α β ℝ} {b : ℝ}
    (h : EntryBound M b) : 0 ≤ b :=
  le_trans (abs_nonneg _) (h (Classical.arbitrary α) (Classical.arbitrary β))

/-- **The entrywise product rule.**  Each entry of a product is a sum of `#γ`
products, so the bound carries a dimension factor. -/
theorem entryBound_mul {α β γ : Type*} [Fintype γ] {M : Matrix α γ ℝ} {N : Matrix γ β ℝ}
    {bM bN : ℝ} (hM : EntryBound M bM) (hN : EntryBound N bN) (h0 : 0 ≤ bM) :
    EntryBound (M * N) (Fintype.card γ * bM * bN) := by
  intro i j
  have hval : (M * N) i j = ∑ k, M i k * N k j := by simp [Matrix.mul_apply]
  rw [hval]
  calc |∑ k, M i k * N k j| ≤ ∑ k, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : γ, bM * bN := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) h0
    _ = Fintype.card γ * bM * bN := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **The dimension factor is not an artefact.**  Two matrices with all entries
of modulus `1` have a product entry of modulus `2` in dimension two, so the naive
bound `bM · bN` is false. -/
theorem entryBound_mul_needs_dimension_factor :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ,
      EntryBound M 1 ∧ EntryBound N 1 ∧ ¬ EntryBound (M * N) 1 := by
  refine ⟨Matrix.of fun _ _ => 1, Matrix.of fun _ _ => 1, fun i j => by simp,
    fun i j => by simp, ?_⟩
  intro h
  have := h 0 0
  simp [Matrix.mul_apply] at this

/-! ## The connection term -/

/-- The entry budget for `R = CᵀAC'` from entry bounds on `C`, `A` and `C'`. -/
def connectionBudget (cardn : ℕ) (bC bA bC' : ℝ) : ℝ := (cardn : ℝ) ^ 2 * bC * bA * bC'

/-- **Every entry of the coordinate-connection term is bounded by the
connection budget.** -/
theorem entryBound_connectionRight {n m : Type*} [Fintype n]
    {C C' : Matrix n m ℝ} {A : Matrix n n ℝ} {bC bA bC' : ℝ}
    (hC : EntryBound C bC) (hA : EntryBound A bA) (hC' : EntryBound C' bC')
    (h0 : 0 ≤ bC) (h1 : 0 ≤ bA) :
    EntryBound (connectionRight C C' A) (connectionBudget (Fintype.card n) bC bA bC') := by
  have h2 : EntryBound (Cᵀ * A) (Fintype.card n * bC * bA) :=
    entryBound_mul (entryBound_transpose hC) hA h0
  have h3 : EntryBound ((Cᵀ * A) * C')
      (Fintype.card n * (Fintype.card n * bC * bA) * bC') :=
    entryBound_mul h2 hC' (by positivity)
  intro i j
  have := h3 i j
  have hb : (Fintype.card n : ℝ) * (Fintype.card n * bC * bA) * bC'
      = connectionBudget (Fintype.card n) bC bA bC' := by
    unfold connectionBudget; ring
  rw [hb] at this
  exact this

/-! ## The substitution derivative from the pivot solve -/

/-- The entry budget for the substitution derivative `C' = E·X` with
`X = −P⁻¹(Q'C)`. -/
def pivotBudget (cardc cardn : ℕ) (bE bPinv bQ' bC : ℝ) : ℝ :=
  (cardc : ℝ) ^ 2 * (cardn : ℝ) * bE * bPinv * bQ' * bC

/-- **The substitution derivative is bounded by the pivot data.**  No norm of
`C'` is assumed: `C'` is the matrix produced by the exact pivot solve of
`eliminated_derivative_solve`, and its size is computed from `Q'`. -/
theorem entryBound_eliminated_derivative {c n m : Type*} [Fintype c] [Fintype n] [DecidableEq c]
    {Q : ℝ → Matrix c n ℝ} {C : ℝ → Matrix n m ℝ} {Q' : Matrix c n ℝ} {C' : Matrix n m ℝ}
    {t : ℝ} {E : Matrix n c ℝ} {X : Matrix c m ℝ} {P Pinv : Matrix c c ℝ}
    {bE bPinv bQ' bC : ℝ}
    (hQd : HasMatDerivAt Q Q' t) (hCd : HasMatDerivAt C C' t)
    (hconstr : ∀ s, Q s * C s = 0)
    (hsupp : C' = E * X) (hP : Q t * E = P) (hPinv : Pinv * P = 1)
    (hE : EntryBound E bE) (hPi : EntryBound Pinv bPinv) (hQ' : EntryBound Q' bQ')
    (hC : EntryBound (C t) bC)
    (h0 : 0 ≤ bE) (h1 : 0 ≤ bPinv) (h2 : 0 ≤ bQ') :
    EntryBound C' (pivotBudget (Fintype.card c) (Fintype.card n) bE bPinv bQ' bC) := by
  have hX : X = -(Pinv * (Q' * C t)) :=
    eliminated_derivative_solve hQd hCd hconstr hsupp hP hPinv
  have hb1 : EntryBound (Q' * C t) (Fintype.card n * bQ' * bC) := entryBound_mul hQ' hC h2
  have hb2 : EntryBound (Pinv * (Q' * C t))
      (Fintype.card c * bPinv * (Fintype.card n * bQ' * bC)) := entryBound_mul hPi hb1 h1
  have hb3 : EntryBound X (Fintype.card c * bPinv * (Fintype.card n * bQ' * bC)) := by
    rw [hX]; exact entryBound_neg hb2
  have hb4 : EntryBound (E * X)
      (Fintype.card c * bE * (Fintype.card c * bPinv * (Fintype.card n * bQ' * bC))) :=
    entryBound_mul hE hb3 h0
  intro i j
  have := hb4 i j
  rw [← hsupp] at this
  refine le_trans this (le_of_eq ?_)
  unfold pivotBudget; ring

/-! ## The composite source budget -/

/-- The connection budget expressed entirely in source data: the ambient
operator bound, the substitution bound, and the pivot-solve data. -/
def sourceConnectionBudget (cardc cardn : ℕ) (bC bA bE bPinv bQ' : ℝ) : ℝ :=
  connectionBudget cardn bC bA (pivotBudget cardc cardn bE bPinv bQ' bC)

/-- **The connection entry is bounded by the composite source budget.** -/
theorem entryBound_connectionRight_of_source
    {c n m : Type*} [Fintype c] [Fintype n] [DecidableEq c]
    {Q : ℝ → Matrix c n ℝ} {C : ℝ → Matrix n m ℝ} {Q' : Matrix c n ℝ} {C' : Matrix n m ℝ}
    {A : Matrix n n ℝ} {t : ℝ} {E : Matrix n c ℝ} {X : Matrix c m ℝ} {P Pinv : Matrix c c ℝ}
    {bC bA bE bPinv bQ' : ℝ}
    (hQd : HasMatDerivAt Q Q' t) (hCd : HasMatDerivAt C C' t)
    (hconstr : ∀ s, Q s * C s = 0)
    (hsupp : C' = E * X) (hP : Q t * E = P) (hPinv : Pinv * P = 1)
    (hC : EntryBound (C t) bC) (hA : EntryBound A bA)
    (hE : EntryBound E bE) (hPi : EntryBound Pinv bPinv) (hQ' : EntryBound Q' bQ')
    (h0 : 0 ≤ bC) (h1 : 0 ≤ bA) (h2 : 0 ≤ bE) (h3 : 0 ≤ bPinv) (h4 : 0 ≤ bQ') :
    EntryBound (connectionRight (C t) C' A)
      (sourceConnectionBudget (Fintype.card c) (Fintype.card n) bC bA bE bPinv bQ') :=
  entryBound_connectionRight hC hA
    (entryBound_eliminated_derivative hQd hCd hconstr hsupp hP hPinv hE hPi hQ' hC h2 h3 h4)
    h0 h1

/-- **The patch certificate in source data.**  If the composite source budget is
below `√2/4`, then the candidate quarter-slab floor for the *full* restricted
symbol — Wilson component `√2/2`, half-width `1/8` — is strictly positive, for
every connection entry the source can produce. -/
theorem connection_budget_certifies_patch
    {c n m : Type*} [Fintype c] [Fintype n] [DecidableEq c]
    {Q : ℝ → Matrix c n ℝ} {C : ℝ → Matrix n m ℝ} {Q' : Matrix c n ℝ} {C' : Matrix n m ℝ}
    {A : Matrix n n ℝ} {t : ℝ} {E : Matrix n c ℝ} {X : Matrix c m ℝ} {P Pinv : Matrix c c ℝ}
    {bC bA bE bPinv bQ' : ℝ}
    (hQd : HasMatDerivAt Q Q' t) (hCd : HasMatDerivAt C C' t)
    (hconstr : ∀ s, Q s * C s = 0)
    (hsupp : C' = E * X) (hP : Q t * E = P) (hPinv : Pinv * P = 1)
    (hC : EntryBound (C t) bC) (hA : EntryBound A bA)
    (hE : EntryBound E bE) (hPi : EntryBound Pinv bPinv) (hQ' : EntryBound Q' bQ')
    (h0 : 0 ≤ bC) (h1 : 0 ≤ bA) (h2 : 0 ≤ bE) (h3 : 0 ≤ bPinv) (h4 : 0 ≤ bQ')
    (hbudget :
      sourceConnectionBudget (Fintype.card c) (Fintype.card n) bC bA bE bPinv bQ'
        < Real.sqrt 2 / 4)
    (i j : m) :
    |connectionRight (C t) C' A i j| < Real.sqrt 2 / 4 ∧
      0 < ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2 - 2 *
        sourceConnectionBudget (Fintype.card c) (Fintype.card n) bC bA bE bPinv bQ') := by
  refine ⟨lt_of_le_of_lt
    (entryBound_connectionRight_of_source hQd hCd hconstr hsupp hP hPinv hC hA hE hPi hQ'
      h0 h1 h2 h3 h4 i j) hbudget, ?_⟩
  exact (restricted_patch_survives_iff _).2 hbudget

/-- **The pivot hypotheses are jointly satisfiable with a nondegenerate
substitution.**  So the source-budget theorems are not vacuous: there are data
with `QC = 0`, an invertible pivot, and `C ≠ 0`. -/
theorem pivot_hypotheses_satisfiable :
    ∃ (Q : ℝ → Matrix (Fin 1) (Fin 2) ℝ) (C : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
      (Q' : Matrix (Fin 1) (Fin 2) ℝ) (C' : Matrix (Fin 2) (Fin 1) ℝ)
      (E : Matrix (Fin 2) (Fin 1) ℝ) (X P Pinv : Matrix (Fin 1) (Fin 1) ℝ),
      HasMatDerivAt Q Q' 0 ∧ HasMatDerivAt C C' 0 ∧ (∀ s, Q s * C s = 0) ∧
        C' = E * X ∧ Q 0 * E = P ∧ Pinv * P = 1 ∧ C 0 ≠ 0 := by
  refine ⟨fun _ => !![1, 0], fun _ => !![0; 1], 0, 0, !![1; 0], 0, 1, 1,
    HasMatDerivAt.const _ _, HasMatDerivAt.const _ _, ?_, by simp, ?_, by simp, ?_⟩
  · intro s
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrFun (congrFun h 1) 0
    simp at this

/-- **Pivot control is load-bearing.**  With a degenerating pivot (large
`P⁻¹`) the composite budget exceeds any prescribed target, so the patch cannot be
certified from the operator data alone. -/
theorem pivotBudget_unbounded_in_pivot (M : ℝ) :
    ∃ bPinv : ℝ, 0 ≤ bPinv ∧ M < sourceConnectionBudget 1 1 1 1 1 bPinv 1 := by
  refine ⟨max 0 M + 1, le_trans (le_max_left 0 M) (by linarith), ?_⟩
  have h : sourceConnectionBudget 1 1 1 1 1 (max 0 M + 1) 1 = max 0 M + 1 := by
    unfold sourceConnectionBudget connectionBudget pivotBudget
    norm_num
  rw [h]
  have := le_max_right 0 M
  linarith

end YangMills
