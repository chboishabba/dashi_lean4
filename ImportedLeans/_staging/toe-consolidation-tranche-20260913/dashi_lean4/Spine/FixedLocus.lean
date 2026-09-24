/-
# One involution theorem, three costumes

The generic statement: on a real vector space, an involution `σ` splits every
vector as a fixed part plus an anti-fixed part,

    x = ½(x + σx) + ½(x − σx),

uniquely, with `σ` acting trivially on the first summand and by `−1` on the
second (`Spine.Involution.*`).  Real observables are then functions of the
transverse part.

Three instances, each an actual theorem rather than a shared word:

* complex conjugation, whose fixed locus is `ℝ` (`Spine.conj_fixed_iff_real`);
* the map `s ↦ −conj s`, whose fixed locus is the imaginary axis — so the
  Riemann critical line is exactly the coset `½ + Fix(−conj)`
  (`Spine.criticalLine_eq_half_add_fixed`), equivalently
  `Re s = ½ ↔ 1 − s = conj s` (`Spine.re_eq_half_iff`);
* the `C₃` inversion, already treated in `Spine.TernaryPhase` (the fixed locus of
  the shift on `ℝ[C₃]` is the constants) and in `Spine.TraceNorm` (the fixed
  locus of conjugation on `ℚ(ζ₃)` is `ℚ`).

The Riemann statement is an identification of a *fixed locus*, nothing more: it
says the critical line is the fixed set of an explicit involution.  No claim
about the zeros of any `L`-function is made or used.
-/
import Mathlib
import Spine.TernaryPhase

open Complex ComplexConjugate

namespace Spine
namespace Involution

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : V →ₗ[ℝ] V)

/-- The fixed component of `x` under an involution. -/
noncomputable def symmPart (x : V) : V := (2 : ℝ)⁻¹ • (x + σ x)

/-- The transverse (anti-fixed) component. -/
noncomputable def antiPart (x : V) : V := (2 : ℝ)⁻¹ • (x - σ x)

theorem symm_add_anti (x : V) : symmPart σ x + antiPart σ x = x := by
  simp only [symmPart, antiPart, ← smul_add]
  rw [show x + σ x + (x - σ x) = (2 : ℝ) • x by module]
  rw [smul_smul]
  norm_num

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

/-- `σ` fixes the fixed component. -/
theorem σ_symmPart (x : V) : σ (symmPart σ x) = symmPart σ x := by
  simp only [symmPart, map_smul, map_add, hσ]
  rw [add_comm]

/-- `σ` acts by `−1` on the transverse component. -/
theorem σ_antiPart (x : V) : σ (antiPart σ x) = -antiPart σ x := by
  simp only [antiPart, map_smul, map_sub, hσ]
  module

/-- A vector is fixed exactly when its transverse component vanishes. -/
theorem fixed_iff_antiPart_zero (x : V) : σ x = x ↔ antiPart σ x = 0 := by
  constructor
  · intro h; simp [antiPart, h]
  · intro h
    have := symm_add_anti σ x
    rw [h, add_zero] at this
    rw [← this]
    exact σ_symmPart σ hσ x

end Involution

/-! ## Instance: complex conjugation -/

/-- The fixed locus of complex conjugation is `ℝ`. -/
theorem conj_fixed_iff_real (s : ℂ) : conj s = s ↔ s.im = 0 := by
  rw [Complex.ext_iff]
  simp [Complex.conj_re, Complex.conj_im]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Instance: the critical line as a fixed locus -/

/-- The `ℝ`-linear involution `s ↦ −conj s`. -/
noncomputable def negConj : ℂ →ₗ[ℝ] ℂ where
  toFun s := -conj s
  map_add' _ _ := by simp; ring
  map_smul' c s := by
    simp

@[simp] theorem negConj_apply (s : ℂ) : negConj s = -conj s := rfl

theorem negConj_involutive (s : ℂ) : negConj (negConj s) = s := by simp

/-- Its fixed locus is the imaginary axis. -/
theorem negConj_fixed_iff (s : ℂ) : negConj s = s ↔ s.re = 0 := by
  simp only [negConj_apply, Complex.ext_iff, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im, neg_neg]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, trivial⟩

/-- **The critical line is a fixed locus.**  `Re s = ½` exactly when `1 − s` and
`conj s` agree; equivalently `s` lies in the coset `½ + Fix(−conj)`. -/
theorem re_eq_half_iff (s : ℂ) : s.re = 1 / 2 ↔ 1 - s = conj s := by
  simp only [Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  constructor
  · intro h; exact ⟨by linarith, by ring⟩
  · rintro ⟨h, -⟩; linarith

/-- The same statement as a coset of the fixed subspace of an involution. -/
theorem criticalLine_eq_half_add_fixed (s : ℂ) :
    s.re = 1 / 2 ↔ negConj (s - 1 / 2) = s - 1 / 2 := by
  rw [negConj_fixed_iff]
  simp only [Complex.sub_re]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [this] at h
    linarith

end Spine
