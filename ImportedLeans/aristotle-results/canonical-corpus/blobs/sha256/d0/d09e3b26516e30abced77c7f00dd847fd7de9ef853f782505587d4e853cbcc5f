/-
# The fixed ⊕ mean-zero splitting, in any dimension

The first sentence of the spine: *a carrier with a distinguished constant mode
splits as fixed ⊕ mean-zero*.  Here that is proved once, for
`EuclideanSpace ℝ (Fin n)` with `n ≠ 0`:

* `Spine.MeanSplit.meanPart_add_fluct` — every vector is (constant part) +
  (mean-zero part);
* `Spine.MeanSplit.inner_ones_fluct`, `Spine.MeanSplit.inner_meanPart_fluct` —
  the two parts are orthogonal, for any two vectors;
* `Spine.MeanSplit.norm_sq_meanPart` — `‖mean part‖² = n · avg²`;
* `Spine.MeanSplit.det_gram_mean_anchored_ge` — the spine's coercivity theorem
  transported to this splitting: a vector with nonzero mean, together with the
  mean-zero parts of any other vectors, sweeps at least `‖mean part‖²` times the
  transverse volume.

The `C₃` case (`Spine.RealC3`) is `n = 3`; the cuisine instance in
`Spine.Observer` is `n = 5`.  The point of proving it here is that the two are
then literally the same theorem, not two hand-rolled encodings.
-/
import Mathlib
import Spine.AnchoredGram

open Matrix RealInnerProductSpace

namespace Spine
namespace MeanSplit

variable {n : ℕ} [NeZero n]

/-- The constant vector, spanning the fixed sector. -/
noncomputable def ones (n : ℕ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))

omit [NeZero n] in
@[simp] theorem ones_apply (i : Fin n) : ones n i = 1 := rfl

/-- The mean of the coordinates. -/
noncomputable def avg (x : EuclideanSpace ℝ (Fin n)) : ℝ := (∑ i, x i) / n

/-- The fixed (constant) component. -/
noncomputable def meanPart (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  avg x • ones n

/-- The transverse (mean-zero) component. -/
noncomputable def fluct (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - meanPart x

omit [NeZero n] in
@[simp] theorem meanPart_apply (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    meanPart x i = avg x := by simp [meanPart]

omit [NeZero n] in
@[simp] theorem fluct_apply (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fluct x i = x i - avg x := by simp [fluct]

omit [NeZero n] in
/-- The splitting. -/
theorem meanPart_add_fluct (x : EuclideanSpace ℝ (Fin n)) : meanPart x + fluct x = x := by
  ext i; simp

omit [NeZero n] in
theorem inner_eq_sum (x y : EuclideanSpace ℝ (Fin n)) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The mean-zero part really has mean zero. -/
theorem sum_fluct (x : EuclideanSpace ℝ (Fin n)) : ∑ i, fluct x i = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [fluct_apply, Finset.sum_sub_distrib, avg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The fixed direction is orthogonal to every mean-zero part. -/
theorem inner_ones_fluct (x : EuclideanSpace ℝ (Fin n)) : ⟪ones n, fluct x⟫ = 0 := by
  rw [inner_eq_sum]
  simpa using sum_fluct x

/-- Any constant vector is orthogonal to any mean-zero part: the splitting is an
orthogonal one. -/
theorem inner_meanPart_fluct (x y : EuclideanSpace ℝ (Fin n)) : ⟪meanPart x, fluct y⟫ = 0 := by
  rw [meanPart, real_inner_smul_left, inner_ones_fluct, mul_zero]

omit [NeZero n] in
theorem norm_sq_ones : ‖ones n‖ ^ 2 = (n : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  simp

omit [NeZero n] in
theorem norm_sq_meanPart (x : EuclideanSpace ℝ (Fin n)) :
    ‖meanPart x‖ ^ 2 = (n : ℝ) * avg x ^ 2 := by
  rw [meanPart, norm_smul, mul_pow]
  rw [norm_sq_ones]
  simp [Real.norm_eq_abs, sq_abs]
  ring

/-- The mean part is nonzero exactly when the mean is. -/
theorem meanPart_ne_zero_iff (x : EuclideanSpace ℝ (Fin n)) : meanPart x ≠ 0 ↔ avg x ≠ 0 := by
  constructor
  · intro h hz; exact h (by simp [meanPart, hz])
  · intro h hz
    apply h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) hz
    simpa using this

/-- The transverse part vanishes exactly on the constant vectors. -/
theorem fluct_eq_zero_iff (x : EuclideanSpace ℝ (Fin n)) : fluct x = 0 ↔ ∀ i j, x i = x j := by
  constructor
  · intro h i j
    have hi : x i - avg x = 0 := by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    have hj : x j - avg x = 0 := by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) h
    linarith
  · intro h
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have h0 : ∀ i, x i = x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ := fun i => h i _
    have havg : avg x = x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ := by
      simp only [avg]
      rw [Finset.sum_congr rfl (fun i _ => h0 i)]
      simp
      field_simp
    ext i
    simp [havg, h0 i]

/-- **The spine theorem in the mean splitting.**  A vector with a nonzero
constant mode, together with the mean-zero parts of any family of vectors,
sweeps at least `‖mean part‖²` times the transverse exterior volume. -/
theorem det_gram_mean_anchored_ge {r : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (y : Fin r → EuclideanSpace ℝ (Fin n)) :
    ‖meanPart x‖ ^ 2 * (Matrix.gram ℝ (fun j => fluct (y j))).det
      ≤ (Matrix.gram ℝ (Fin.cons x (fun j => fluct (y j)))).det := by
  have hx : (Fin.cons x (fun j => fluct (y j)) : Fin (r + 1) → EuclideanSpace ℝ (Fin n))
      = Fin.cons (meanPart x + fluct x) (fun j => fluct (y j)) := by
    rw [meanPart_add_fluct]
  rw [hx]
  exact det_gram_anchored_ge (meanPart x) (fluct x) (fun j => fluct (y j))
    (inner_meanPart_fluct x x) (fun j => inner_meanPart_fluct x (y j))

/-- **Nondegeneracy in the mean splitting.**  Nonzero mean plus independent
mean-zero directions gives a genuine `(r+1)`-dimensional sector. -/
theorem det_gram_mean_anchored_pos {r : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (y : Fin r → EuclideanSpace ℝ (Fin n)) (hx : avg x ≠ 0)
    (hy : LinearIndependent ℝ (fun j => fluct (y j))) :
    0 < (Matrix.gram ℝ (Fin.cons x (fun j => fluct (y j)))).det := by
  have hx' : (Fin.cons x (fun j => fluct (y j)) : Fin (r + 1) → EuclideanSpace ℝ (Fin n))
      = Fin.cons (meanPart x + fluct x) (fun j => fluct (y j)) := by
    rw [meanPart_add_fluct]
  rw [hx']
  exact det_gram_anchored_pos (meanPart x) (fluct x) (fun j => fluct (y j))
    (inner_meanPart_fluct x x) (fun j => inner_meanPart_fluct x (y j))
    ((meanPart_ne_zero_iff x).mpr hx) hy

/-- The rank-one instance: a vector with nonzero mean and a nonzero mean-zero
direction span a genuine plane, with an explicit area floor. -/
theorem anchored_plane_area (x y : EuclideanSpace ℝ (Fin n)) :
    (n : ℝ) * avg x ^ 2 * ‖fluct y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖fluct y‖ ^ 2 - ⟪x, fluct y⟫ ^ 2 := by
  have h := anchored_area_ge (meanPart x) (fluct x) (fluct y) (inner_meanPart_fluct x x)
    (inner_meanPart_fluct x y)
  rw [meanPart_add_fluct, norm_sq_meanPart] at h
  exact h

end MeanSplit
end Spine
