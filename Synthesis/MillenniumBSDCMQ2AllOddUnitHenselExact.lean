import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic

/-!
BSD K1: genuine Q₂ square root of every integer u ≡ 1 (mod 8).
This generalizes the x=39/3705 Hensel candidate to all eight
dyadic square-class calculations. Not merely modular residues.
Source-written candidate; requires pinned Lean/Mathlib kernel.
-/

noncomputable section
namespace Synthesis.Millennium.BSD

private def dyadicOddUnitPolynomial (u : ℤ) : Polynomial ℤ_[2] :=
  Polynomial.X^2 - Polynomial.C (u : ℤ_[2])

/-- 1-u divisible by 8 is the sharp odd-unit square criterion at p=2.
    This is a true field-valued existential statement, conditional
    only on the displayed integer divisibility (not a free root axiom). -/
theorem cmQ2SquareRootOfOneModEight (u : ℤ)
    (hu : (2 : ℤ)^3 ∣ 1 - u) :
    ∃ z : ℚ_[2], z^2 = (u : ℚ_[2]) := by
  have hnorm :
      ‖((1 - u : ℤ) : ℤ_[2])‖ ≤
        (2 : ℝ)^(-(3 : ℤ)) := by
    exact (PadicInt.norm_int_le_pow_iff_dvd
      (p := 2) (k := 1-u) (n := 3)).2 hu
  have htwo : ‖(2 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using (PadicInt.norm_p (p := 2))
  have heval :
      (Polynomial.aeval (1 : ℤ_[2]))
        (dyadicOddUnitPolynomial u) = ((1-u : ℤ) : ℤ_[2]) := by
    simp [dyadicOddUnitPolynomial]
    ring
  have hderiv :
      (Polynomial.aeval (1 : ℤ_[2]))
        (dyadicOddUnitPolynomial u).derivative = (2 : ℤ_[2]) := by
    simp [dyadicOddUnitPolynomial]
  have hsmall :
      ‖((1-u : ℤ) : ℤ_[2])‖ ≤ (1 / 8 : ℝ) := by
    convert hnorm using 1 <;> norm_num
  have hHensel :
      ‖(Polynomial.aeval (1 : ℤ_[2]))
          (dyadicOddUnitPolynomial u)‖ <
      ‖(Polynomial.aeval (1 : ℤ_[2]))
          (dyadicOddUnitPolynomial u).derivative‖^2 := by
    rw [heval, hderiv, htwo]
    linarith
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 2) (R := ℤ_[2])
      (F := dyadicOddUnitPolynomial u) (a := 1) hHensel
  have hzSq : z^2 = (u : ℤ_[2]) := by
    have hzero : z^2 - (u : ℤ_[2]) = 0 := by
      simpa [dyadicOddUnitPolynomial] using hz
    exact sub_eq_zero.mp hzero
  refine ⟨(z : ℚ_[2]), ?_⟩
  exact_mod_cast hzSq

/-- The original x=39 source unit, now from the uniform Hensel
    constructor rather than an isolated lucky square. -/
theorem cmQ2SquareRoot3705FromUniform :
    ∃ z : ℚ_[2], z^2 = (3705 : ℚ_[2]) := by
  exact cmQ2SquareRootOfOneModEight 3705 (by norm_num)

/-- All six actual integer-x local unit witnesses are covered by
    the same source Hensel producer. -/
theorem cmQ2SixSampleUnitRoots :
    (∃ z : ℚ_[2], z^2 = (5481 : ℚ_[2])) ∧
    (∃ z : ℚ_[2], z^2 = (465 : ℚ_[2])) ∧
    (∃ z : ℚ_[2], z^2 = (561 : ℚ_[2])) ∧
    (∃ z : ℚ_[2], z^2 = (3705 : ℚ_[2])) ∧
    (∃ z : ℚ_[2], z^2 = (4305 : ℚ_[2])) ∧
    (∃ z : ℚ_[2], z^2 = (87801 : ℚ_[2])) := by
  exact ⟨cmQ2SquareRootOfOneModEight 5481 (by norm_num),
    cmQ2SquareRootOfOneModEight 465 (by norm_num),
    cmQ2SquareRootOfOneModEight 561 (by norm_num),
    cmQ2SquareRootOfOneModEight 3705 (by norm_num),
    cmQ2SquareRootOfOneModEight 4305 (by norm_num),
    cmQ2SquareRootOfOneModEight 87801 (by norm_num)⟩

end Synthesis.Millennium.BSD
