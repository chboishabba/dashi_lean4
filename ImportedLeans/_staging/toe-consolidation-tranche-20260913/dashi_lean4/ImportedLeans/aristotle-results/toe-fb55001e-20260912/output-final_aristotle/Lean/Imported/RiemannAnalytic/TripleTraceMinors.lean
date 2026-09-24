/-
**Higher traces do carry higher Gram minors: the rank-three identity.**

`HigherTraceMinors.lean` proves the rank-two statement

    ∑_{i,j} (2 × 2 principal minor) = (tr A)² − tr (A²)

and observes that the corresponding rank-`r` formula "would need Newton's
identities".  This file supplies the next case outright, by direct expansion of
the `3 × 3` determinant and Fubini on the resulting six triple sums:

    ∑_{i,j,k} det (A restricted to i,j,k) = (tr A)³ − 3 (tr A)(tr A²) + 2 tr A³.

(The six permutations of `S₃` contribute according to their cycle type: the
identity gives `(tr A)³`, the three transpositions give `−tr A · tr A²`, and the
two three-cycles give `+tr A³`.)

Specialised to a Gram matrix, every summand on the left is a squared exterior
`3`-volume `‖v_i ∧ v_j ∧ v_k‖² ≥ 0`, so:

* `sum_tripleGramDet_nonneg`: `(tr G)³ − 3 (tr G)(tr G²) + 2 tr G³ ≥ 0`;
* `tripleGramDet_le_trace_combination`: each individual triple exterior volume
  is bounded above by that same combination of traces.

This answers the rank-three instance of the question "does `tr G^{2r}` contain
`r × r` Gram minors?" affirmatively, and in the precise form: the third trace
enters the total exterior `3`-volume with coefficient `+2`, but only in
combination with the lower traces.
-/
import RiemannAnalytic.HigherTraceMinors

namespace RiemannAnalytic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The `3 × 3` principal minor of `A` on the (not necessarily distinct) index
triple `i, j, k`, expanded. -/
theorem det_submatrix_three (A : Matrix n n ℝ) (i j k : n) :
    (A.submatrix ![i, j, k] ![i, j, k]).det
      = A i i * A j j * A k k - A i i * A j k * A k j - A i j * A j i * A k k
        + A i j * A j k * A k i + A i k * A j i * A k j - A i k * A j j * A k i := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

omit [DecidableEq n] in
/-- `tr (A · A)` as an explicit double sum. -/
theorem trace_sq_sum (A : Matrix n n ℝ) : (A * A).trace = ∑ i, ∑ j, A i j * A j i := by
  rw [Matrix.trace]
  simp [Matrix.diag_apply, Matrix.mul_apply]

omit [DecidableEq n] in
/-- `tr (A · A · A)` as an explicit triple sum. -/
theorem trace_cube_sum (A : Matrix n n ℝ) :
    (A * A * A).trace = ∑ i, ∑ j, ∑ k, A i j * A j k * A k i := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
/-- `tr A` as an explicit sum. -/
theorem trace_sum (A : Matrix n n ℝ) : A.trace = ∑ i, A i i := rfl

omit [DecidableEq n] in
/-- **The rank-three trace identity.**  Summing the `3 × 3` principal minors of
an arbitrary square matrix over *all* ordered index triples gives

    (tr A)³ − 3 (tr A)(tr A²) + 2 tr A³.

Triples with a repeated index contribute zero (two equal rows), so each
three-element subset is counted `3! = 6` times. -/
theorem sum_tripleMinor_eq_trace_combination (A : Matrix n n ℝ) :
    ∑ i, ∑ j, ∑ k, (A.submatrix ![i, j, k] ![i, j, k]).det
      = A.trace ^ 3 - 3 * A.trace * (A * A).trace + 2 * (A * A * A).trace := by
  have hexp : ∀ i j k : n, (A.submatrix ![i, j, k] ![i, j, k]).det
      = A i i * A j j * A k k - A i i * A j k * A k j - A i j * A j i * A k k
        + A i j * A j k * A k i + A i k * A j i * A k j - A i k * A j j * A k i :=
    det_submatrix_three A
  -- the six constituent triple sums
  have hS1 : ∑ i, ∑ j, ∑ k, A i i * A j j * A k k = A.trace ^ 3 := by
    have : ∀ i j : n, ∑ k, A i i * A j j * A k k = A i i * A j j * A.trace := by
      intro i j; rw [← Finset.mul_sum]; rfl
    simp only [this]
    have h2 : ∀ i : n, ∑ j, A i i * A j j * A.trace = A i i * A.trace * A.trace := by
      intro i
      rw [show (fun j => A i i * A j j * A.trace) = (fun j => (A i i * A.trace) * A j j) by
        funext j; ring, ← Finset.mul_sum]
      rw [← trace_sum]
    simp only [h2]
    rw [show (fun i => A i i * A.trace * A.trace) = (fun i => A i i * (A.trace * A.trace)) by
      funext i; ring, ← Finset.sum_mul, ← trace_sum]
    ring
  have hS2 : ∑ i, ∑ j, ∑ k, A i i * A j k * A k j = A.trace * (A * A).trace := by
    have h1 : ∀ i : n, ∑ j, ∑ k, A i i * A j k * A k j = A i i * (A * A).trace := by
      intro i
      rw [trace_sq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [h1]
    rw [← Finset.sum_mul, ← trace_sum]
  have hS3 : ∑ i, ∑ j, ∑ k, A i j * A j i * A k k = (A * A).trace * A.trace := by
    have h1 : ∀ i j : n, ∑ k, A i j * A j i * A k k = A i j * A j i * A.trace := by
      intro i j; rw [← Finset.mul_sum]; rfl
    simp only [h1]
    rw [trace_sq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  have hS4 : ∑ i, ∑ j, ∑ k, A i j * A j k * A k i = (A * A * A).trace := (trace_cube_sum A).symm
  have hS5 : ∑ i, ∑ j, ∑ k, A i k * A j i * A k j = (A * A * A).trace := by
    rw [trace_cube_sum]
    -- swap the roles of the second and third summation index
    rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset n))]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun j _ => by ring
  have hS6 : ∑ i, ∑ j, ∑ k, A i k * A j j * A k i = (A * A).trace * A.trace := by
    have h1 : ∀ i j : n, ∑ k, A i k * A j j * A k i = A j j * ∑ k, A i k * A k i := by
      intro i j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [h1]
    have h2 : ∀ i : n, ∑ j, A j j * ∑ k, A i k * A k i
        = A.trace * ∑ k, A i k * A k i := by
      intro i; rw [← Finset.sum_mul, ← trace_sum]
    simp only [h2]
    rw [← Finset.mul_sum, ← trace_sq_sum]
    ring
  -- assemble
  calc ∑ i, ∑ j, ∑ k, (A.submatrix ![i, j, k] ![i, j, k]).det
      = (∑ i, ∑ j, ∑ k, A i i * A j j * A k k)
        - (∑ i, ∑ j, ∑ k, A i i * A j k * A k j)
        - (∑ i, ∑ j, ∑ k, A i j * A j i * A k k)
        + (∑ i, ∑ j, ∑ k, A i j * A j k * A k i)
        + (∑ i, ∑ j, ∑ k, A i k * A j i * A k j)
        - (∑ i, ∑ j, ∑ k, A i k * A j j * A k i) := by
        simp only [hexp]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = A.trace ^ 3 - 3 * A.trace * (A * A).trace + 2 * (A * A * A).trace := by
        rw [hS1, hS2, hS3, hS4, hS5, hS6]; ring

end Matrices

/-! ### Consequences for Gram matrices -/

section Gram

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The triple principal minors of a Gram matrix are exactly the squared
exterior `3`-volumes of the corresponding triples. -/
theorem tripleGramDet_eq (v : n → E) (i j k : n) :
    (((Matrix.gram ℝ v).submatrix ![i, j, k] ![i, j, k])).det
      = gramDet ![v i, v j, v k] := by
  have : ((Matrix.gram ℝ v).submatrix ![i, j, k] ![i, j, k])
      = Matrix.gram ℝ ![v i, v j, v k] := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [this, gramDet]

omit [DecidableEq n] in
/-- **The total exterior `3`-volume of a family, in traces.** -/
theorem sum_tripleGramDet_eq_trace_combination (v : n → E) :
    ∑ i, ∑ j, ∑ k, gramDet ![v i, v j, v k]
      = (Matrix.gram ℝ v).trace ^ 3
        - 3 * (Matrix.gram ℝ v).trace * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace
        + 2 * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace := by
  rw [← sum_tripleMinor_eq_trace_combination (Matrix.gram ℝ v)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => (tripleGramDet_eq v i j k).symm

omit [DecidableEq n] in
/-- Since every triple minor of a Gram matrix is a squared exterior volume, the
trace combination is nonnegative. -/
theorem sum_tripleGramDet_nonneg (v : n → E) :
    0 ≤ (Matrix.gram ℝ v).trace ^ 3
        - 3 * (Matrix.gram ℝ v).trace * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace
        + 2 * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace := by
  rw [← sum_tripleGramDet_eq_trace_combination v]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  exact gramDet_nonneg _

omit [DecidableEq n] in
/-- **Each individual exterior `3`-volume is controlled by the traces.**  A
single triple's squared exterior volume is at most the whole trace
combination. -/
theorem tripleGramDet_le_trace_combination (v : n → E) (i j k : n) :
    gramDet ![v i, v j, v k]
      ≤ (Matrix.gram ℝ v).trace ^ 3
        - 3 * (Matrix.gram ℝ v).trace * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace
        + 2 * ((Matrix.gram ℝ v) * (Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace := by
  rw [← sum_tripleGramDet_eq_trace_combination v]
  have hinner : ∀ a : n, 0 ≤ ∑ b, ∑ c, gramDet ![v a, v b, v c] := fun a =>
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => gramDet_nonneg _
  calc gramDet ![v i, v j, v k]
      ≤ ∑ c, gramDet ![v i, v j, v c] := by
        refine Finset.single_le_sum (f := fun c => gramDet ![v i, v j, v c])
          (fun c _ => gramDet_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ b, ∑ c, gramDet ![v i, v b, v c] := by
        refine Finset.single_le_sum (f := fun b => ∑ c, gramDet ![v i, v b, v c])
          (fun b _ => Finset.sum_nonneg fun c _ => gramDet_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ∑ c, gramDet ![v a, v b, v c] := by
        refine Finset.single_le_sum (f := fun a => ∑ b, ∑ c, gramDet ![v a, v b, v c])
          (fun a _ => hinner a) (Finset.mem_univ i)

end Gram

end RiemannAnalytic
