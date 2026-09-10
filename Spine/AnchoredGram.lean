/-
# Anchored exterior coercivity

The spine theorem of this tranche, stated and proved in arbitrary rank over an
arbitrary real inner product space.

Setting.  A carrier `V` with a distinguished *fixed* direction `f` orthogonal to
a *transverse* sector.  One anchored vector `v₀ = f + t₀` has a component in the
fixed direction; the remaining vectors `v₁ … v_r = t₁ … t_r` are purely
transverse (they, and `t₀`, are orthogonal to `f`).  Then

    det Gram(v₀, …, v_r) = det Gram(t₀, …, t_r) + ‖f‖² · det Gram(t₁, …, t_r)

(`Spine.det_gram_anchored_eq`), and therefore

    det Gram(v₀, …, v_r) ≥ ‖f‖² · det Gram(t₁, …, t_r)

(`Spine.det_gram_anchored_ge`), since a Gram determinant is non-negative.
Because `det Gram = ‖v₀ ∧ ⋯ ∧ v_r‖²`, this is exactly the statement that the two
summands `f ∧ t₁ ∧ ⋯ ∧ t_r` and `t₀ ∧ t₁ ∧ ⋯ ∧ t_r` of the wedge lie in
orthogonal exterior sectors; the proof below avoids exterior algebra and works
directly with the determinant, so it needs no finite-dimensionality hypothesis.

The `r = 1` case (`Spine.anchored_area_ge`) is the two-dimensional "a fixed
anchor forces a genuinely transverse vector to sweep positive area" statement:
`‖a‖²‖b‖² − ⟪a,b⟫² ≥ ‖f‖²‖b‖²`.

Nothing here is specific to any domain: it is ordinary real linear algebra.  Its
role in this corpus is as the *nondegeneracy gate* — a pair of labelled
directions is only a plane once the Gram determinant is positive.
-/
import Mathlib

open Matrix RealInnerProductSpace

namespace Spine

/-! ## A determinant lemma: bumping the `(0,0)` entry -/

/-- Adding `c` to the `(0,0)` entry of a square matrix adds `c` times the
`(0,0)` minor to the determinant.  (Cofactor expansion along the first row.) -/
theorem det_add_single_zero_zero {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (c : ℝ) :
    (M + Matrix.single 0 0 c).det = M.det + c * (M.submatrix Fin.succ Fin.succ).det := by
  have hsub : ∀ j : Fin (r + 1), ((M + Matrix.single 0 0 c).submatrix Fin.succ j.succAbove)
      = M.submatrix Fin.succ j.succAbove := by
    intro j; ext a b
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.single_apply, add_eq_left,
      ite_eq_right_iff, and_imp]
    intro h _; exact absurd h.symm (Fin.succ_ne_zero a)
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero M]
  simp only [hsub, Matrix.add_apply, Matrix.single_apply, true_and]
  have key : ∀ j : Fin (r + 1),
      (-1 : ℝ) ^ (j : ℕ) * (M 0 j + (if (0 : Fin (r + 1)) = j then c else 0)) *
        (M.submatrix Fin.succ j.succAbove).det
      = (-1 : ℝ) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det
        + (if (0 : Fin (r + 1)) = j then
            c * (M.submatrix Fin.succ (Fin.succAbove 0)).det else 0) := by
    intro j
    by_cases h : (0 : Fin (r + 1)) = j
    · subst h; simp [add_mul]
    · simp [h]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [Fin.succAbove_zero]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The anchored Gram matrix -/

/-- The Gram matrix of an anchored family `(f + t₀, t₁, …, t_r)` differs from the
Gram matrix of the purely transverse family `(t₀, t₁, …, t_r)` exactly by `‖f‖²`
in the `(0,0)` slot. -/
theorem gram_anchored_eq {r : ℕ} (f t₀ : V) (t : Fin r → V)
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0) :
    Matrix.gram ℝ (Fin.cons (f + t₀) t) =
      Matrix.gram ℝ (Fin.cons t₀ t) + Matrix.single 0 0 (‖f‖ ^ 2) := by
  have hft' : ∀ j, ⟪t j, f⟫ = 0 := fun j => by rw [real_inner_comm]; exact hft j
  have hne : ∀ (k : Fin r) (P : Prop), (0 : Fin (r + 1)) = k.succ → P :=
    fun k P h => absurd h.symm (Fin.succ_ne_zero k)
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Matrix.gram_apply, Fin.cons_zero, Matrix.add_apply, Matrix.single_apply,
        and_self, if_true, real_inner_self_eq_norm_sq]
      rw [norm_add_sq_real, hf₀]; ring
    · simp only [Matrix.gram_apply, Fin.cons_zero, Fin.cons_succ, Matrix.add_apply,
        Matrix.single_apply, inner_add_left, hft, zero_add]
      rw [if_neg (by rintro ⟨-, h⟩; exact hne j' False h)]; ring
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Matrix.gram_apply, Fin.cons_zero, Fin.cons_succ, Matrix.add_apply,
        Matrix.single_apply, inner_add_right, hft', zero_add]
      rw [if_neg (by rintro ⟨h, -⟩; exact hne i' False h)]; ring
    · simp only [Matrix.gram_apply, Fin.cons_succ, Matrix.add_apply, Matrix.single_apply]
      rw [if_neg (by rintro ⟨h, -⟩; exact hne i' False h)]; ring

/-- Deleting the anchored row and column of a Gram matrix leaves the Gram matrix
of the remaining vectors. -/
theorem gram_cons_submatrix {r : ℕ} (x : V) (t : Fin r → V) :
    (Matrix.gram ℝ (Fin.cons x t)).submatrix Fin.succ Fin.succ = Matrix.gram ℝ t := by
  ext i j; simp [Matrix.gram_apply, Fin.cons_succ]

/-! ## Anchored exterior coercivity -/

/-- **Anchored exterior coercivity, exact form.**  With `V ⊇ ℝ·f ⊥ T`, an
anchored vector `f + t₀` and transverse vectors `t₁ … t_r`,

`det Gram(f + t₀, t₁, …, t_r) = det Gram(t₀, t₁, …, t_r) + ‖f‖² det Gram(t₁, …, t_r)`. -/
theorem det_gram_anchored_eq {r : ℕ} (f t₀ : V) (t : Fin r → V)
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0) :
    (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det
      = (Matrix.gram ℝ (Fin.cons t₀ t)).det + ‖f‖ ^ 2 * (Matrix.gram ℝ t).det := by
  rw [gram_anchored_eq f t₀ t hf₀ hft, det_add_single_zero_zero, gram_cons_submatrix]

/-- **Anchored exterior coercivity.**  A nonzero component in the fixed sector
forces the exterior volume of the anchored family to dominate `‖f‖²` times the
exterior volume of the transverse family. -/
theorem det_gram_anchored_ge {r : ℕ} (f t₀ : V) (t : Fin r → V)
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0) :
    ‖f‖ ^ 2 * (Matrix.gram ℝ t).det ≤ (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det := by
  rw [det_gram_anchored_eq f t₀ t hf₀ hft]
  have h : (0 : ℝ) ≤ (Matrix.gram ℝ (Fin.cons t₀ t)).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  linarith

/-- **The nondegeneracy gate.**  If the anchor is nonzero and the transverse
channels are independent, the anchored family has strictly positive exterior
volume — so it spans a genuine `(r+1)`-dimensional sector, not merely `r + 1`
labels. -/
theorem det_gram_anchored_pos {r : ℕ} (f t₀ : V) (t : Fin r → V)
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0)
    (hf : f ≠ 0) (ht : LinearIndependent ℝ t) :
    0 < (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det := by
  have h1 : 0 < ‖f‖ ^ 2 := by positivity
  have h2 : 0 < (Matrix.gram ℝ t).det :=
    (Matrix.posDef_gram_of_linearIndependent ht).det_pos
  have := det_gram_anchored_ge f t₀ t hf₀ hft
  nlinarith

/-- Anchoring also yields linear independence of the whole family. -/
theorem linearIndependent_anchored {r : ℕ} (f t₀ : V) (t : Fin r → V)
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0)
    (hf : f ≠ 0) (ht : LinearIndependent ℝ t) :
    LinearIndependent ℝ (Fin.cons (f + t₀) t) := by
  classical
  by_contra hdep
  have hdet : (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det = 0 := by
    by_contra hne
    refine hdep (Matrix.linearIndependent_of_posDef_gram ?_)
    rw [(Matrix.posSemidef_gram ℝ _).posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hne
  exact absurd hdet (ne_of_gt (det_gram_anchored_pos f t₀ t hf₀ hft hf ht))

/-! ## The rank-two case: anchored area -/

/-- The Gram determinant of a pair is the squared area `‖a‖²‖b‖² − ⟪a,b⟫²`. -/
theorem det_gram_pair (a b : V) :
    (Matrix.gram ℝ ![a, b]).det = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm b a]; ring

/-- **Anchored area (the `r = 1` case).**  If `a = f + t₀` with `f` orthogonal to
both `t₀` and `b`, then the area swept by `a` and `b` is at least `‖f‖ ‖b‖`. -/
theorem anchored_area_ge (f t₀ b : V) (hf₀ : ⟪f, t₀⟫ = 0) (hfb : ⟪f, b⟫ = 0) :
    ‖f‖ ^ 2 * ‖b‖ ^ 2 ≤ ‖f + t₀‖ ^ 2 * ‖b‖ ^ 2 - ⟪f + t₀, b⟫ ^ 2 := by
  have hcons : Fin.cons (f + t₀) ![b] = ![f + t₀, b] := rfl
  have h := det_gram_anchored_ge f t₀ ![b] hf₀ (by
    intro j; fin_cases j; simpa using hfb)
  rw [hcons, det_gram_pair] at h
  have hb : (Matrix.gram ℝ ![b]).det = ‖b‖ ^ 2 := by
    simp [Matrix.det_unique, Matrix.gram_apply]
  rwa [hb] at h

/-! ## The degeneracy warning

A map that sends all of its input data to zero satisfies every hypothesis above
and proves nothing: its exterior volume is `0`, and the coercive bound reads
`0 ≤ 0`.  This is the exact sense in which "the X of Y" needs a nondegeneracy
witness and not only a structure map. -/

/-- A family of zero vectors has vanishing exterior volume. -/
theorem det_gram_zero_family {r : ℕ} :
    (Matrix.gram ℝ (fun _ : Fin (r + 1) => (0 : V))).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero (i := (0 : Fin (r + 1))) (by simp [Matrix.gram_apply])

/-- Degenerate anchoring: with `f = 0` the coercive bound is vacuous. -/
theorem anchored_bound_vacuous_of_anchor_zero {r : ℕ} (t : Fin r → V) :
    ‖(0 : V)‖ ^ 2 * (Matrix.gram ℝ t).det = 0 := by simp

end Spine
