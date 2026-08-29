import RequestProject.DihedralCenterRetraction

/-!
# The infinite dihedral group, and the dihedral classification for all `n`

`DihedralCenterRetraction.lean` classified the finite dihedral groups: for `n ≠ 0`, `D_n` retracts
onto its center iff `4 ∤ n`.  The remaining case is `n = 0`, the *infinite* dihedral group
`DihedralGroup 0` (rotations indexed by `ZMod 0 = ℤ`).

* `DihedralGroup.center_zero_eq_bot` : the infinite dihedral group is centerless — a rotation
  `r i` commutes with the reflection `sr 0` only if `2i = 0`, i.e. `i = 0`, and a reflection
  `sr j` never commutes with `r 1`;
* `DihedralGroup.hasCenterRetraction_zero` : hence it retracts (trivially) onto its center;
* `DihedralGroup.hasCenterRetraction_dihedral_iff_all` : **the classification for every `n`**:
  `D_n` retracts onto its center iff `n = 0` or `4 ∤ n`.
-/

open Subgroup

namespace DihedralGroup

/-- **The infinite dihedral group is centerless.** -/
theorem center_zero_eq_bot : center (DihedralGroup 0) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  match x with
  | r i =>
    have h := hx (sr 0)
    simp only [r_mul_sr, sr_mul_r] at h
    have h2 : (0 : ZMod 0) + i = 0 - i := by injection h
    have h3 : (2 : ZMod 0) * i = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 two_ne_zero
    · simp [h4]
  | sr j =>
    have h := hx (r 1)
    simp only [r_mul_sr, sr_mul_r] at h
    have h2 : j - 1 = j + 1 := by injection h
    have h3 : (2 : ZMod 0) = 0 := by linear_combination -h2
    exact absurd h3 two_ne_zero

/-- The infinite dihedral group retracts onto its (trivial) center. -/
theorem hasCenterRetraction_zero : HasCenterRetraction (DihedralGroup 0) :=
  hasCenterRetraction_of_center_eq_bot center_zero_eq_bot

/-- **Complete classification of the dihedral family.**  `D_n` retracts onto its center if and
only if `n = 0` (the infinite dihedral group, which is centerless) or `4` does not divide `n`. -/
theorem hasCenterRetraction_dihedral_iff_all (n : ℕ) :
    HasCenterRetraction (DihedralGroup n) ↔ (n = 0 ∨ ¬ (4 ∣ n)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨fun _ => Or.inl rfl, fun _ => hasCenterRetraction_zero⟩
  · rw [hasCenterRetraction_dihedral_iff n hn0]
    exact ⟨fun h => Or.inr h, fun h => h.resolve_left hn0⟩

end DihedralGroup
