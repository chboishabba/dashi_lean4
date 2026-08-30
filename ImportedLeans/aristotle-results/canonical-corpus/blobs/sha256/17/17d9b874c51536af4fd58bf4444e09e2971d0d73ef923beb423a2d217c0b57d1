/-
**Anchored exterior coercivity: the `k`-dimensional Gram-minor theorem.**

`OneSidedGram.lean` proves the rank-two ("area") case on the concrete one-sided
window: a fixed source coordinate `a₀ > 0` at which the transverse vector
vanishes forces `AB − C² ≥ a₀² B`.  This file proves the general statement
behind it, for an arbitrary finite family in an arbitrary real inner product
space:

  if `e` is a unit vector orthogonal to `v₁, …, v_r`, then

      det Gram(v₀, v₁, …, v_r) ≥ ⟪e, v₀⟫² · det Gram(v₁, …, v_r).

(`gramDet_anchored_ge`.)  The mechanism is exact and elementary: subtracting the
`e`-components turns the Gram matrix into `Gram(t) + ⟪e, v₀⟫² E₀₀`, and expanding
the determinant along the anchored row splits it as

      det Gram(v) = det Gram(t) + ⟪e, v₀⟫² · det Gram(v₁, …, v_r)

(`gramDet_anchored_eq`), whose first summand is nonnegative because Gram
matrices are positive semidefinite.

Consequences: an anchor promotes transverse nondegeneracy to a strict positive
exterior volume (`gramDet_anchored_pos`, `linearIndependent_of_anchored`), and
in the rank-two case one recovers exactly the inequality used on the source
window (`gramDefect_ge_anchor_sq_mul`).
-/
import Mathlib
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant of a finite family of vectors: the squared exterior
volume they span. -/
noncomputable def gramDet {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) : ℝ :=
  (Matrix.gram ℝ v).det

theorem gramDet_nonneg {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    0 ≤ gramDet v :=
  (Matrix.posSemidef_gram ℝ v).det_nonneg

/-- Removing the `e`-component of each vector subtracts the rank-one correction
`⟪e, vᵢ⟫⟪e, vⱼ⟫` from the Gram matrix. -/
theorem inner_sub_proj {e : E} (he : ‖e‖ = 1) (x y : E) :
    ⟪x - ⟪e, x⟫_ℝ • e, y - ⟪e, y⟫_ℝ • e⟫_ℝ = ⟪x, y⟫_ℝ - ⟪e, x⟫_ℝ * ⟪e, y⟫_ℝ := by
  have hee : ⟪e, e⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hxe : ⟪x, e⟫_ℝ = ⟪e, x⟫_ℝ := real_inner_comm _ _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hee,
    hxe]
  ring

/-- **The exact anchored splitting of the Gram determinant.**

If the unit vector `e` is orthogonal to `v₁, …, v_r`, then

    det Gram(v₀, …, v_r) = det Gram(t₀, …, t_r) + ⟪e, v₀⟫² · det Gram(v₁, …, v_r),

where `tᵢ = vᵢ − ⟪e, vᵢ⟫ e` is the component of `vᵢ` transverse to the anchor. -/
theorem gramDet_anchored_eq {r : ℕ} (v : Fin (r + 1) → E) (e : E) (he : ‖e‖ = 1)
    (hperp : ∀ j : Fin r, ⟪e, v j.succ⟫_ℝ = 0) :
    gramDet v
      = gramDet (fun i : Fin (r + 1) => v i - ⟪e, v i⟫_ℝ • e)
        + ⟪e, v 0⟫_ℝ ^ 2 * gramDet (fun j : Fin r => v j.succ) := by
  classical
  set t : Fin (r + 1) → E := fun i => v i - ⟪e, v i⟫_ℝ • e with ht
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.gram ℝ t with hM
  set c : ℝ := ⟪e, v 0⟫_ℝ with hc
  -- entrywise: the Gram matrix of `v` is that of `t` plus `c²` in the corner
  have hentry : ∀ i j, Matrix.gram ℝ v i j = M i j + (if i = 0 then (if j = 0 then c ^ 2 else 0)
      else 0) := by
    intro i j
    have hij : M i j = ⟪v i, v j⟫_ℝ - ⟪e, v i⟫_ℝ * ⟪e, v j⟫_ℝ := by
      rw [hM, ht]; exact inner_sub_proj he _ _
    rcases eq_or_ne i 0 with rfl | hi
    · rcases eq_or_ne j 0 with rfl | hj
      · rw [hij]; simp [hc]; ring
      · obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = j'.succ := by
          rcases Fin.eq_zero_or_eq_succ j with h | h
          · exact absurd h hj
          · exact h
        rw [hij, hperp j']
        simp [Matrix.gram_apply]
    · obtain ⟨i', rfl⟩ : ∃ i' : Fin r, i = i'.succ := by
        rcases Fin.eq_zero_or_eq_succ i with h | h
        · exact absurd h hi
        · exact h
      rw [hij, hperp i']
      simp [Matrix.gram_apply, Fin.succ_ne_zero]
  have hkey : Matrix.gram ℝ v = M.updateRow 0 (M 0 + Pi.single 0 (c ^ 2)) := by
    ext i j
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Matrix.updateRow_self, hentry]
      simp [Pi.single_apply]
    · rw [Matrix.updateRow_ne hi, hentry]
      simp [hi]
  -- the corner term contributes `c²` times the transverse minor
  have hsingle : (Pi.single 0 (c ^ 2) : Fin (r + 1) → ℝ)
      = c ^ 2 • (Pi.single 0 1 : Fin (r + 1) → ℝ) := by
    funext j
    by_cases hj : j = 0 <;> simp [Pi.single_apply, hj]
  have hminor : (M.updateRow 0 (Pi.single 0 1 : Fin (r + 1) → ℝ)).det
      = (M.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (0 : Fin (r + 1))]
    · have hsub : (M.updateRow 0 (Pi.single 0 1 : Fin (r + 1) → ℝ)).submatrix Fin.succ Fin.succ
          = M.submatrix Fin.succ Fin.succ := by
        ext i j
        simp [Matrix.submatrix_apply]
      simp [Matrix.updateRow_self, hsub]
    · intro j _ hj
      simp [Matrix.updateRow_self, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have htrans : M.submatrix Fin.succ Fin.succ = Matrix.gram ℝ (fun j : Fin r => v j.succ) := by
    ext i j
    have hij : M i.succ j.succ = ⟪v i.succ, v j.succ⟫_ℝ - ⟪e, v i.succ⟫_ℝ * ⟪e, v j.succ⟫_ℝ := by
      rw [hM, ht]; exact inner_sub_proj he _ _
    simp only [Matrix.submatrix_apply, hij, hperp i, hperp j, Matrix.gram_apply]
    ring
  have hfinal : (Matrix.gram ℝ v).det = M.det + c ^ 2 * (M.submatrix Fin.succ Fin.succ).det := by
    rw [hkey, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, hsingle,
      Matrix.det_updateRow_smul, hminor]
  show (Matrix.gram ℝ v).det
      = (Matrix.gram ℝ t).det + c ^ 2 * (Matrix.gram ℝ (fun j : Fin r => v j.succ)).det
  rw [hfinal, htrans]

/-- **Anchored exterior coercivity (the general `k`-dimensional Gram-minor
theorem).**

If `e` is a unit vector orthogonal to `v₁, …, v_r`, then the squared exterior
volume of `v₀, …, v_r` is at least the squared anchor length times the squared
exterior volume of the transverse family:

    det Gram(v₀, …, v_r) ≥ ⟪e, v₀⟫² · det Gram(v₁, …, v_r). -/
theorem gramDet_anchored_ge {r : ℕ} (v : Fin (r + 1) → E) (e : E) (he : ‖e‖ = 1)
    (hperp : ∀ j : Fin r, ⟪e, v j.succ⟫_ℝ = 0) :
    ⟪e, v 0⟫_ℝ ^ 2 * gramDet (fun j : Fin r => v j.succ) ≤ gramDet v := by
  have hsplit := gramDet_anchored_eq v e he hperp
  have hnn := gramDet_nonneg (fun i : Fin (r + 1) => v i - ⟪e, v i⟫_ℝ • e)
  linarith

/-- A nonzero anchor together with a nondegenerate transverse family forces a
strictly positive exterior volume. -/
theorem gramDet_anchored_pos {r : ℕ} (v : Fin (r + 1) → E) (e : E) (he : ‖e‖ = 1)
    (hperp : ∀ j : Fin r, ⟪e, v j.succ⟫_ℝ = 0) (hanchor : ⟪e, v 0⟫_ℝ ≠ 0)
    (htrans : 0 < gramDet (fun j : Fin r => v j.succ)) :
    0 < gramDet v := by
  have hge := gramDet_anchored_ge v e he hperp
  have : 0 < ⟪e, v 0⟫_ℝ ^ 2 * gramDet (fun j : Fin r => v j.succ) := by
    have : 0 < ⟪e, v 0⟫_ℝ ^ 2 := by positivity
    exact mul_pos this htrans
  linarith

/-- A family whose Gram determinant is nonzero is linearly independent. -/
theorem linearIndependent_of_gramDet_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (h : gramDet v ≠ 0) : LinearIndependent ℝ v := by
  classical
  by_contra hdep
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨x, hx, i, hi⟩ := hdep
  refine h ?_
  rw [gramDet]
  refine (Matrix.exists_mulVec_eq_zero_iff).1 ⟨x, ?_, ?_⟩
  · intro hx0
    exact hi (by rw [hx0]; rfl)
  · funext j
    have : (Matrix.gram ℝ v).mulVec x j = ⟪v j, ∑ i, x i • v i⟫_ℝ := by
      simp [Matrix.mulVec, dotProduct, Matrix.gram_apply, inner_sum, real_inner_smul_right,
        mul_comm]
    rw [this, hx]
    simp

/-- Under the same anchoring hypotheses, transverse linear independence upgrades
to linear independence of the whole family. -/
theorem linearIndependent_of_anchored {r : ℕ} (v : Fin (r + 1) → E) (e : E) (he : ‖e‖ = 1)
    (hperp : ∀ j : Fin r, ⟪e, v j.succ⟫_ℝ = 0) (hanchor : ⟪e, v 0⟫_ℝ ≠ 0)
    (htrans : LinearIndependent ℝ (fun j : Fin r => v j.succ)) :
    LinearIndependent ℝ v := by
  have hpos : 0 < gramDet (fun j : Fin r => v j.succ) :=
    (Matrix.posDef_gram_of_linearIndependent htrans).det_pos
  exact linearIndependent_of_gramDet_ne_zero v
    (ne_of_gt (gramDet_anchored_pos v e he hperp hanchor hpos))

/-! ### The rank-two case: the area inequality on the source window -/

/-- **The `k = 2` case**: with a unit anchor `e` orthogonal to `b`,

    ‖a‖²‖b‖² − ⟪a, b⟫² ≥ ⟪e, a⟫² ‖b‖²,

which is precisely the inequality used on the one-sided source window. -/
theorem gramDefect_ge_anchor_sq_mul (a b e : E) (he : ‖e‖ = 1) (hperp : ⟪e, b⟫_ℝ = 0) :
    ⟪e, a⟫_ℝ ^ 2 * ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 := by
  have hv : ∀ j : Fin 1, ⟪e, (![a, b] : Fin 2 → E) j.succ⟫_ℝ = 0 := by
    intro j
    fin_cases j
    simpa using hperp
  have hge := gramDet_anchored_ge (![a, b] : Fin 2 → E) e he hv
  have h2 : gramDet (![a, b] : Fin 2 → E) = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 := by
    rw [gramDet, Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm b a]
    ring
  have h1 : gramDet (fun j : Fin 1 => (![a, b] : Fin 2 → E) j.succ) = ‖b‖ ^ 2 := by
    rw [gramDet, Matrix.det_unique]
    simp [Matrix.gram_apply]
  have h0 : ⟪e, (![a, b] : Fin 2 → E) 0⟫_ℝ = ⟪e, a⟫_ℝ := by simp
  rw [h2, h1, h0] at hge
  exact hge

end RiemannAnalytic
