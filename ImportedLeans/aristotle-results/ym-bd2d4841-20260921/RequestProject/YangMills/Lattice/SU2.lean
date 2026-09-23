/-
# `SU(2)` as the gauge group of the literal lattice construction

The lattice construction of `Lattice/Wilson.lean` is stated for a compact
Hausdorff second-countable gauge group together with a continuous
conjugation-invariant character.  This file supplies the actual gauge group of
the `N = 2` Yang–Mills theory in the quaternion model already used elsewhere in
this development (`SU2QuaternionOperatorNorm`): unit quaternions, with the
character `χ(g) = Re tr ρ(g)` of the defining two-dimensional representation.

Proved here:

* `SU2` is a compact Hausdorff second-countable topological group, and carries
  its Borel σ-algebra;
* `chiSU2 g = Re tr ρ(g) = 2 Re g` — the Wilson character of the defining
  representation, computed from the literal `2 × 2` matrix model;
* `chiSU2` is continuous and invariant under conjugation, which are exactly the
  two hypotheses the Wilson–Gibbs construction consumes.
-/
import Mathlib
import RequestProject.YangMills.SU2QuaternionOperatorNorm

namespace RequestProject.YangMills.Lattice

open RequestProject.YangMills.SU2QuaternionOperatorNorm

/-- The gauge group `SU(2)`, realised as the unit quaternions. -/
abbrev SU2 : Type := Metric.sphere (0 : Quaternion ℝ) 1

noncomputable instance : MeasurableSpace SU2 := borel _

instance : BorelSpace SU2 := ⟨rfl⟩

/-- The Wilson character of the defining representation of `SU(2)`: the real part
of the trace of the `2 × 2` matrix representing the group element. -/
noncomputable def chiSU2 (g : SU2) : ℝ := (Matrix.trace (su2 (g : Quaternion ℝ))).re

/-- The character is twice the real part of the quaternion. -/
theorem chiSU2_eq (g : SU2) : chiSU2 g = 2 * (g : Quaternion ℝ).re := by
  simp [chiSU2, su2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

theorem continuous_chiSU2 : Continuous chiSU2 := by
  have : Continuous fun g : SU2 => 2 * (g : Quaternion ℝ).re :=
    continuous_const.mul (Quaternion.continuous_re.comp continuous_subtype_val)
  exact this.congr fun g => (chiSU2_eq g).symm

/-- The real part of a quaternion product is symmetric in its two factors. -/
theorem quaternion_re_mul_comm (x y : Quaternion ℝ) : (x * y).re = (y * x).re := by
  simp [Quaternion.re_mul]
  ring

/-- **The Wilson character is a class function**: it is invariant under
conjugation, which is what gauge invariance of the plaquette action needs. -/
theorem chiSU2_conj (a g : SU2) : chiSU2 (a * g * a⁻¹) = chiSU2 g := by
  have ha : (a : Quaternion ℝ) ≠ 0 := by
    intro h
    have := a.2
    rw [mem_sphere_iff_norm, h] at this
    simp at this
  have hcoe : ((a * g * a⁻¹ : SU2) : Quaternion ℝ)
      = (a : Quaternion ℝ) * (g : Quaternion ℝ) * (a : Quaternion ℝ)⁻¹ := rfl
  rw [chiSU2_eq, chiSU2_eq, hcoe]
  rw [quaternion_re_mul_comm ((a : Quaternion ℝ) * (g : Quaternion ℝ)) (a : Quaternion ℝ)⁻¹]
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end RequestProject.YangMills.Lattice
