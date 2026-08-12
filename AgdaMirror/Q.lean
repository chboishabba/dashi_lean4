import Mathlib

/-!
# Lean mirror of `DASHI/Core/Q.agda` (genuine, fully proved)

The project's canonical rational layer.  Mathlib's `ℚ` is the canonical field;
we expose the small numerals `twoℚ`, `threeℚ`, `fourℚ` built from `1 + 1` and
prove the genuine rational identities that the numeral layer unlocks.
-/

namespace AgdaMirror.Q

/-- `2 : ℚ` built as `1 + 1`. -/
def twoℚ : ℚ := 1 + 1
/-- `3 : ℚ` built as `2 + 1`. -/
def threeℚ : ℚ := twoℚ + 1
/-- `4 : ℚ` built as `2 + 2`. -/
def fourℚ : ℚ := twoℚ + twoℚ

theorem twoℚ_eq : twoℚ = 2 := by norm_num [twoℚ]
theorem threeℚ_eq : threeℚ = 3 := by norm_num [threeℚ, twoℚ]
theorem fourℚ_eq : fourℚ = 4 := by norm_num [fourℚ, twoℚ]

/-- `2 · 2 = 4` over `ℚ`. -/
theorem twoℚ_mul_twoℚ : twoℚ * twoℚ = fourℚ := by norm_num [twoℚ, fourℚ]

/-- A genuine rational identity unlocked by the numeral layer. -/
theorem half_add_half : (1 / twoℚ) + (1 / twoℚ) = 1 := by norm_num [twoℚ]

end AgdaMirror.Q
