/-
**Do higher traces carry higher Gram minors?**

`PairExpansion.lean` observes that the Gram defect enters `c·tr − ‖·‖_F²` with
the *opposite* sign to `‖·‖_F²`, so the second Frobenius moment alone does not
carry the transverse area as positive signal.  This file makes the exact
relation explicit, at rank two and in general.

* `sum_pairMinor_eq_trace_sq_sub_trace_mul_self`: for **any** square matrix,

      ∑_{i,j} (A i i · A j j − A i j · A j i) = (tr A)² − tr (A · A).

* `sum_pair_gramDefect_eq`: for a Gram matrix `G` of vectors `v`, this reads

      ∑_{i,j} (‖vᵢ‖²‖vⱼ‖² − ⟪vᵢ,vⱼ⟫²) = (∑ᵢ ‖vᵢ‖²)² − ‖G‖_F²,

  the diagonal terms contributing zero, so each unordered pair is counted twice.
  The total pairwise transverse area is therefore exactly the *difference*
  `(tr G)² − tr G²`: the second trace alone carries it with the wrong sign, and
  only the squared first trace restores it.  In particular a bound on `‖G‖_F²`
  from below is a bound on the total pairwise area from above
  (`sum_pair_gramDefect_le_of_frobSq_ge`).

* `det_submatrix_gram_eq_gramDet`: the `r × r` principal minors of `G` are
  exactly the squared exterior `r`-volumes of the corresponding subfamilies, so
  higher exterior information *is* present in `G` — as principal minors.  The
  rank-three formula expressing those minors through the traces
  `tr G, tr G², tr G³` is proved in `TripleTraceMinors.lean`; a general rank-`r`
  version (Newton's identities) is not proved anywhere in this development.
-/
import RiemannAnalytic.AnchoredExterior

namespace RiemannAnalytic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The rank-two identity -/

/-- For any square matrix, the sum over ordered pairs of the `2 × 2` principal
minors is `(tr A)² − tr (A · A)`.  (Diagonal pairs contribute zero, so every
unordered pair is counted twice.) -/
theorem sum_pairMinor_eq_trace_sq_sub_trace_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    ∑ i, ∑ j, (A i i * A j j - A i j * A j i)
      = A.trace ^ 2 - (A * A).trace := by
  have hdiag : ∑ i, ∑ j, A i i * A j j = A.trace ^ 2 := by
    rw [sq, Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_mul_sum]
  have hoff : ∑ i, ∑ j, A i j * A j i = (A * A).trace := by
    rw [Matrix.trace]
    simp [Matrix.diag_apply, Matrix.mul_apply]
  calc ∑ i, ∑ j, (A i i * A j j - A i j * A j i)
      = (∑ i, ∑ j, A i i * A j j) - ∑ i, ∑ j, A i j * A j i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_sub_distrib]
    _ = A.trace ^ 2 - (A * A).trace := by rw [hdiag, hoff]

/-- **The total pairwise transverse area of a family is `(tr G)² − tr G².**

For vectors `v` with Gram matrix `G`,

    ∑_{i,j} (‖vᵢ‖² ‖vⱼ‖² − ⟪vᵢ, vⱼ⟫²) = (tr G)² − tr (G · G),

the left side being twice the sum of the pairwise Gram defects.  The second
trace enters with a minus sign: `tr G²` alone does not carry the area. -/
theorem sum_pair_gramDefect_eq {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    ∑ i, ∑ j, (‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2)
      = (Matrix.gram ℝ v).trace ^ 2 - ((Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace := by
  rw [← sum_pairMinor_eq_trace_sq_sub_trace_mul_self (Matrix.gram ℝ v)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.gram_apply]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (v j) (v i)]
  ring

/-- `tr (G · G)` is the squared Frobenius norm of the Gram matrix. -/
theorem trace_gram_mul_self {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    ((Matrix.gram ℝ v) * (Matrix.gram ℝ v)).trace = ∑ i, ∑ j, ⟪v i, v j⟫_ℝ ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.gram_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (v j) (v i)]
  ring

/-- `tr G` is the total squared length of the family. -/
theorem trace_gram {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    (Matrix.gram ℝ v).trace = ∑ i, ‖v i‖ ^ 2 := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Matrix.diag_apply, Matrix.gram_apply]
    exact real_inner_self_eq_norm_sq (v i)

/-- **A Frobenius lower bound is an upper bound on the total pairwise area.**

If `‖G‖_F² ≥ B` then the total pairwise transverse area is at most
`(∑ᵢ ‖vᵢ‖²)² − B`.  This is the shape in which a prime-side bound on the
Frobenius norm transports to the Gram-defect side. -/
theorem sum_pair_gramDefect_le_of_frobSq_ge {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) {B : ℝ} (hB : B ≤ ∑ i, ∑ j, ⟪v i, v j⟫_ℝ ^ 2) :
    ∑ i, ∑ j, (‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2) ≤ (∑ i, ‖v i‖ ^ 2) ^ 2 - B := by
  rw [sum_pair_gramDefect_eq v, trace_gram v, trace_gram_mul_self v]
  linarith

/-! ### Higher minors are higher exterior volumes -/

/-- The `r × r` principal minors of a Gram matrix are the squared exterior
volumes of the corresponding subfamilies: higher exterior information is present
in `G`, as principal minors. -/
theorem det_submatrix_gram_eq_gramDet {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (v : n → E) (f : m → n) :
    ((Matrix.gram ℝ v).submatrix f f).det = gramDet (v ∘ f) := rfl

/-- The anchored coercivity theorem in minor form: an anchor bounds the
principal minor of the whole family below by the transverse principal minor. -/
theorem det_gram_anchored_minor_ge {r : ℕ} (v : Fin (r + 1) → E) (e : E) (he : ‖e‖ = 1)
    (hperp : ∀ j : Fin r, ⟪e, v j.succ⟫_ℝ = 0) :
    ⟪e, v 0⟫_ℝ ^ 2 * ((Matrix.gram ℝ v).submatrix Fin.succ Fin.succ).det
      ≤ (Matrix.gram ℝ v).det := by
  have h := gramDet_anchored_ge v e he hperp
  have hsub : ((Matrix.gram ℝ v).submatrix Fin.succ Fin.succ).det
      = gramDet (fun j : Fin r => v j.succ) := rfl
  rw [hsub]
  exact h

end RiemannAnalytic
