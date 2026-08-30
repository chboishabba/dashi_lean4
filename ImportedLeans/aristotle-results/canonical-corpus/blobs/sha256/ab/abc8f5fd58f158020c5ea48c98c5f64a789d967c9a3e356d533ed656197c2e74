import RequestProject.CenterRetraction
import RequestProject.GeneralLinearCenterRetraction

/-!
# When `GLₙ` *does* retract onto its center

`GeneralLinearCenterRetraction.lean` shows that `GL₂(R)` never retracts onto its center once
`2 ≠ 0` in `R`, because the central involution `-I` is a commutator.  That obstruction is
special to the size `2`: the center of `GL n R` is the group of scalars `Rˣ`, on which the
determinant is the `n`-th power map, so as soon as `n`-th powers are *bijective* on `Rˣ` the
determinant can be undone and

`A ↦ (det A)^{1/n} · I`

is a retraction onto the center.

* `hasCenterRetraction_generalLinear_of_bijective_pow` : the general criterion.
* `hasCenterRetraction_GL3_zmod_five` : `GL₃(𝔽₅)` retracts onto its center — while `GL₂(𝔽₅)`
  does not (`GL2.not_hasCenterRetraction_zmod`).  The obstruction really is about the size of
  the matrices, not about the ring.
* `hasCenterRetraction_GL3_real` : likewise `GL₃(ℝ)` retracts onto its center, by the real cube
  root, while `GL₂(ℝ)` does not.
-/

open Matrix Subgroup

namespace GLPositive

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The determinant of a scalar matrix is the `card n`-th power of the scalar. -/
theorem det_scalar (u : Rˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar n u) = u ^ Fintype.card n := by
  ext
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.det, Matrix.scalar,
    Matrix.det_diagonal, Units.val_pow_eq_pow_val]

/-- **`GLₙ(R)` retracts onto its center whenever `u ↦ uⁿ` is bijective on `Rˣ`** (`n` the
number of rows).  The retraction is `A ↦ (det A)^{1/n} · I`. -/
theorem hasCenterRetraction_generalLinear_of_bijective_pow
    (hbij : Function.Bijective fun u : Rˣ => u ^ Fintype.card n) :
    HasCenterRetraction (GL n R) := by
  set e : Rˣ ≃* Rˣ := MulEquiv.ofBijective (powMonoidHom (Fintype.card n)) hbij with he
  have hepow : ∀ u : Rˣ, e u = u ^ Fintype.card n := fun u => rfl
  set f : GL n R →* GL n R :=
    (GeneralLinearGroup.scalar n).comp
      ((e.symm : Rˣ →* Rˣ).comp (GeneralLinearGroup.det)) with hf
  have hmem : ∀ A : GL n R, f A ∈ center (GL n R) := by
    intro A
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  refine ⟨f.codRestrict (center (GL n R)) hmem, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨u, rfl⟩ := (GeneralLinearGroup.center_eq_range_scalar (n := n) (R := R) ▸ hz :
    z ∈ (GeneralLinearGroup.scalar n).range)
  have hdet : e.symm (GeneralLinearGroup.det (GeneralLinearGroup.scalar n u)) = u := by
    rw [det_scalar, ← hepow u, MulEquiv.symm_apply_apply]
  refine Subtype.ext ?_
  show f (GeneralLinearGroup.scalar n u) = GeneralLinearGroup.scalar n u
  rw [hf]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe]
  rw [hdet]

end GLPositive

section Examples

open GLPositive

/-- **`GL₃(𝔽₅)` retracts onto its center**: cubing is bijective on `𝔽₅ˣ ≅ ℤ/4`.  Contrast
`GL2.not_hasCenterRetraction_zmod`: `GL₂(𝔽₅)` does not. -/
theorem hasCenterRetraction_GL3_zmod_five :
    HasCenterRetraction (GL (Fin 3) (ZMod 5)) := by
  refine hasCenterRetraction_generalLinear_of_bijective_pow ?_
  simpa using (by decide : Function.Bijective fun u : (ZMod 5)ˣ => u ^ 3)

/-- Every nonnegative real has a nonnegative cube root. -/
theorem exists_cube_root_nonneg {y : ℝ} (hy : 0 ≤ y) : ∃ x : ℝ, 0 ≤ x ∧ x ^ 3 = y := by
  refine ⟨y ^ ((1 : ℝ) / 3), Real.rpow_nonneg hy _, ?_⟩
  rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hy]
  norm_num

/-- Every real has a cube root. -/
theorem exists_cube_root (y : ℝ) : ∃ x : ℝ, x ^ 3 = y := by
  rcases le_or_gt 0 y with hy | hy
  · obtain ⟨x, -, hx⟩ := exists_cube_root_nonneg hy
    exact ⟨x, hx⟩
  · obtain ⟨x, -, hx⟩ := exists_cube_root_nonneg (y := -y) (by linarith)
    refine ⟨-x, ?_⟩
    have hneg : (-x) ^ 3 = -(x ^ 3) := by ring
    rw [hneg, hx, neg_neg]

/-- Cubing is bijective on `ℝˣ`. -/
theorem bijective_cube_realUnits : Function.Bijective fun u : ℝˣ => u ^ 3 := by
  constructor
  · intro u v huv
    have h : (u : ℝ) ^ 3 = (v : ℝ) ^ 3 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg (fun w : ℝˣ => (w : ℝ)) huv
    exact Units.ext (Odd.pow_injective (by decide) h)
  · intro u
    obtain ⟨r, hr⟩ := exists_cube_root (u : ℝ)
    have hr0 : r ≠ 0 := by
      intro h
      exact u.ne_zero (by simp [← hr, h])
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa [Units.val_pow_eq_pow_val] using hr)⟩

/-- **`GL₃(ℝ)` retracts onto its center**, by the real cube root — while `GL₂(ℝ)` does not
(`GL2.not_hasCenterRetraction_real`). -/
theorem hasCenterRetraction_GL3_real : HasCenterRetraction (GL (Fin 3) ℝ) := by
  refine hasCenterRetraction_generalLinear_of_bijective_pow ?_
  simpa using bijective_cube_realUnits

/-- The size, not the ring, is what obstructs: over `𝔽₅` and over `ℝ` the group `GL₂` has no
retraction onto its center and `GL₃` has one. -/
theorem generalLinear_obstruction_depends_on_size :
    (¬ HasCenterRetraction (GL (Fin 2) (ZMod 5)) ∧ HasCenterRetraction (GL (Fin 3) (ZMod 5))) ∧
      (¬ HasCenterRetraction (GL (Fin 2) ℝ) ∧ HasCenterRetraction (GL (Fin 3) ℝ)) :=
  ⟨⟨GL2.not_hasCenterRetraction_zmod (by norm_num) (by norm_num),
      hasCenterRetraction_GL3_zmod_five⟩,
    ⟨GL2.not_hasCenterRetraction_real, hasCenterRetraction_GL3_real⟩⟩

end Examples
