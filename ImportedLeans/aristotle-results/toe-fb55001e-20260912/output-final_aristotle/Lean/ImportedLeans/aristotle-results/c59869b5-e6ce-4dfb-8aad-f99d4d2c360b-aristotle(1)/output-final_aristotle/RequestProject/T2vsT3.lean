import Mathlib
import RequestProject.DeltaWordGraphs

/-!
# `T₂` against `T₃`, pointwise

`RequestProject/DeltaWordGraphs.lean` draws the two words `T₂` and `T₃` as modular forms in
their own right: `wordT2 m` is the coefficient of `qᵐ` in `T₂ Δ` and `wordT3 m` the coefficient
of `qᵐ` in `T₃ Δ`. On the verified range `1 ≤ m ≤ 20` they are

`wordT2 m = -24 · τ(m) = τ(2) · τ(m)`,   `wordT3 m = 252 · τ(m) = τ(3) · τ(m)`.

This file compares the two sequences **pointwise**, in the five ways asked for: product,
difference, quotient, power and remainder. Because both are the same sequence `τ` rescaled, every
comparison collapses to a statement about a single constant, and each of those constants is a
number the earlier sections already know:

| operation           | value at `m`                            | constant                              |
| ------------------- | --------------------------------------- | ------------------------------------- |
| `t₂ · t₃`           | `-6048 · τ(m)²`                         | `τ(6) = τ(2)τ(3)`, the `T₂T₃` scale   |
| `t₂ - t₃`           | `-276 · τ(m)`                           | `τ(2) - τ(3)`, digital root `6`       |
| `t₂ / t₃` in `ℚ`    | `-2/21`                                 | `τ(2)/τ(3)`, independent of `m`       |
| `t₂ / t₃` in `ℤ`    | `-1` or `0`, by the sign of `τ(m)`      | the rounding of `-2/21`               |
| `t₂ ^ t₃`           | positive, divisible by `3` to the height of the exponent | astronomically large |
| `t₂ % t₃`           | `228 · τ(m)` or `-24 · τ(m)`            | `τ(3) - τ(2)`, resp. `-τ(2)`          |

The two graphs are *anti*-parallel: `τ(2) < 0 < τ(3)`, so `t₂ m` and `t₃ m` always have opposite
signs (`prodT_neg`), their ratio is negative and constant (`ratioT_eq`), and `t₃` is `10.5` times
as tall as `t₂` everywhere (`abs_ratio_21_2`).

The trinity survives all of it: `3` divides the pointwise product, the pointwise difference and
the pointwise remainder, so each has digital root in `{3, 6, 9}` wherever it is nonzero
(`prodT_mem_trinity`, `diffT_mem_trinity`, `modT_mem_trinity`); the integer quotient is the one
comparison that leaves the trinity (`quotT_notMem_trinity`), because it forgets the scale in
which the trinity lives.

Everything is stated on `1 ≤ m ≤ 20`, the range on which `DeltaWordGraphs.wordT3_eq` is verified.
-/

namespace T2vsT3

open DeltaGraph DeltaWordGraphs

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

/-! ## The two sequences on the common range -/

/-- `T₂ Δ` has `m`-th coefficient `τ(2) τ(m) = -24 τ(m)`. -/
theorem t2_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : wordT2 m = -24 * tauT m := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  exact wordT2_eq m (Finset.mem_Icc.mpr ⟨h1, by omega⟩)

/-- `T₃ Δ` has `m`-th coefficient `τ(3) τ(m) = 252 τ(m)`. -/
theorem t3_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : wordT3 m = 252 * tauT m :=
  wordT3_eq m hm

/-- No coefficient of `Δ` vanishes on the compared range. (Whether that holds for every `m` is
Lehmer's question; here it is a finite check.) -/
theorem tauT_ne_zero {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : tauT m ≠ 0 := by
  revert m hm; decide

theorem wordT2_ne_zero {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : wordT2 m ≠ 0 := by
  rw [t2_eq hm]; exact mul_ne_zero (by norm_num) (tauT_ne_zero hm)

theorem wordT3_ne_zero {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : wordT3 m ≠ 0 := by
  rw [t3_eq hm]; exact mul_ne_zero (by norm_num) (tauT_ne_zero hm)

/-! ## The five pointwise comparisons -/

/-- Pointwise product `t₂ · t₃`. -/
def prodT (m : ℕ) : ℤ := wordT2 m * wordT3 m

/-- Pointwise difference `t₂ - t₃`. -/
def diffT (m : ℕ) : ℤ := wordT2 m - wordT3 m

/-- Pointwise quotient `t₂ / t₃`, as a rational number. -/
def ratioT (m : ℕ) : ℚ := (wordT2 m : ℚ) / (wordT3 m : ℚ)

/-- Pointwise quotient `t₂ / t₃` inside `ℤ`. Lean's integer division rounds so that the
remainder is nonnegative. -/
def quotT (m : ℕ) : ℤ := wordT2 m / wordT3 m

/-- Pointwise power `t₂ ^ t₃`, the exponent being the size `|t₃ m|`. -/
def powT (m : ℕ) : ℤ := wordT2 m ^ (wordT3 m).natAbs

/-- Pointwise remainder `t₂ % t₃`. -/
def modT (m : ℕ) : ℤ := wordT2 m % wordT3 m

/-! ### Product: `τ(2)τ(3) = τ(6)` times `τ(m)²` -/

/-- **The pointwise product.** `t₂ · t₃ = -6048 τ(m)²`. -/
theorem prodT_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : prodT m = -6048 * tauT m ^ 2 := by
  rw [prodT, t2_eq hm, t3_eq hm]; ring

/-- The constant of the product is `τ(6) = τ(2)τ(3)`, i.e. the multiplier of the word `T₂T₃`:
multiplying the two graphs pointwise reproduces the multiplier of their composition. -/
theorem prodT_eq_tau_six {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    prodT m = tauT 6 * tauT m ^ 2 ∧ tauT 6 = -6048 ∧ tauT 6 = tauT 2 * tauT 3 := by
  have h6 : tauT 6 = -6048 := by decide
  exact ⟨by rw [prodT_eq hm, h6], h6, by decide⟩

/-- **The two graphs point opposite ways.** The pointwise product is strictly negative, so
`t₂ m` and `t₃ m` have opposite signs at every compared `m`. -/
theorem prodT_neg {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : prodT m < 0 := by
  have hne := tauT_ne_zero hm
  have hsq : 0 < tauT m ^ 2 := by positivity
  rw [prodT_eq hm]
  exact mul_neg_of_neg_of_pos (by norm_num) hsq

/-! ### Difference: `τ(2) - τ(3)` times `τ(m)` -/

/-- **The pointwise difference.** `t₂ - t₃ = -276 τ(m)`, and `-276 = τ(2) - τ(3)`. -/
theorem diffT_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    diffT m = -276 * tauT m ∧ (-276 : ℤ) = tauT 2 - tauT 3 := by
  refine ⟨?_, by decide⟩
  rw [diffT, t2_eq hm, t3_eq hm]; ring

/-- The difference never vanishes on the compared range: the two graphs never meet. -/
theorem diffT_ne_zero {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : diffT m ≠ 0 := by
  rw [(diffT_eq hm).1]
  exact mul_ne_zero (by norm_num) (tauT_ne_zero hm)

/-! ### Quotient in `ℚ`: the constant `-2/21` -/

/-- **The pointwise quotient is constant.** `t₂ m / t₃ m = -2/21 = τ(2)/τ(3)` for every compared
`m`: comparing the two graphs by division carries no information beyond the two eigenvalues. -/
theorem ratioT_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : ratioT m = -2 / 21 := by
  have h : (tauT m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (tauT_ne_zero hm)
  rw [ratioT, t2_eq hm, t3_eq hm]
  push_cast
  field_simp
  ring

/-- The two heights compare as `2 : 21` everywhere: `|t₃|` is `10.5` times `|t₂|`. -/
theorem abs_ratio_21_2 {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    21 * |wordT2 m| = 2 * |wordT3 m| := by
  rw [t2_eq hm, t3_eq hm, abs_mul, abs_mul, show |(-24 : ℤ)| = 24 from by norm_num,
    show |(252 : ℤ)| = 252 from by norm_num]
  ring

/-! ### Remainder: `τ(3) - τ(2)` or `-τ(2)`, by the sign of `τ(m)` -/

/-- **The pointwise remainder.** `t₂ % t₃` is `228 τ(m) = (τ(3) - τ(2)) τ(m)` where `τ(m) > 0`,
and `-24 τ(m) = -τ(2) τ(m)` where `τ(m) < 0`. -/
theorem modT_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    modT m = if 0 < tauT m then 228 * tauT m else -24 * tauT m := by
  rw [modT, t2_eq hm, t3_eq hm]
  rcases lt_trichotomy (tauT m) 0 with h1 | h1 | h1
  · rw [if_neg (not_lt.mpr h1.le)]
    have hneg : (252 : ℤ) * tauT m = -(252 * -tauT m) := by ring
    have h24 : (-24 : ℤ) * tauT m = 24 * -tauT m := by ring
    rw [hneg, h24, Int.emod_neg]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact absurd h1 (tauT_ne_zero hm)
  · rw [if_pos h1]
    have hrw : (-24 : ℤ) * tauT m = 228 * tauT m + 252 * tauT m * (-1) := by ring
    rw [hrw, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The remainder is nonnegative, as Lean's `%` on `ℤ` always is. -/
theorem modT_nonneg {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : 0 ≤ modT m := by
  rw [modT_eq hm]
  rcases lt_trichotomy (tauT m) 0 with h1 | h1 | h1
  · rw [if_neg (not_lt.mpr h1.le)]; omega
  · exact absurd h1 (tauT_ne_zero hm)
  · rw [if_pos h1]; omega

/-- The remainder is smaller than `|t₃ m|`, as a remainder must be. -/
theorem modT_lt {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : modT m < |wordT3 m| := by
  rw [modT_eq hm, t3_eq hm, abs_mul, show |(252 : ℤ)| = 252 from by norm_num]
  rcases lt_trichotomy (tauT m) 0 with h1 | h1 | h1
  · rw [if_neg (not_lt.mpr h1.le), abs_of_neg h1]; omega
  · exact absurd h1 (tauT_ne_zero hm)
  · rw [if_pos h1, abs_of_pos h1]; omega

/-- The remainder never vanishes: `t₃ m` never divides `t₂ m`. -/
theorem modT_ne_zero {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : modT m ≠ 0 := by
  rw [modT_eq hm]
  split <;> exact mul_ne_zero (by norm_num) (tauT_ne_zero hm)

/-! ### Quotient in `ℤ`: the rounding of `-2/21` -/

/-- **The pointwise quotient inside `ℤ`.** Rounding makes it `-1` where `τ(m) > 0` and `0` where
`τ(m) < 0`. -/
theorem quotT_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    quotT m = if 0 < tauT m then -1 else 0 := by
  have hb : wordT3 m ≠ 0 := wordT3_ne_zero hm
  refine mul_left_cancel₀ hb ?_
  have hdm := Int.mul_ediv_add_emod (wordT2 m) (wordT3 m)
  have hmod : wordT2 m % wordT3 m = if 0 < tauT m then 228 * tauT m else -24 * tauT m :=
    modT_eq hm
  have hkey : wordT3 m * quotT m = wordT2 m - wordT2 m % wordT3 m := by
    rw [quotT]; omega
  rw [hkey, hmod, t2_eq hm, t3_eq hm]
  rcases lt_trichotomy (tauT m) 0 with h1 | h1 | h1
  · rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h1.le)]; ring
  · exact absurd h1 (tauT_ne_zero hm)
  · rw [if_pos h1, if_pos h1]; ring

/-! ### Power: astronomically large, positive, and full of threes -/

/-- The exponent `|t₃ m| = 252 |τ(m)|` is even, so the pointwise power is positive even where
`t₂ m` is negative. -/
theorem powT_pos {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : 0 < powT m := by
  have heven : Even (wordT3 m).natAbs := by
    rw [t3_eq hm, Int.natAbs_mul]
    exact Even.mul_right (by decide) _
  exact heven.pow_pos (wordT2_ne_zero hm)

/-- `t₂ m` is three times something, so `t₂ ^ t₃` is divisible by `3` to the full height of the
exponent: the trinity is present in the pointwise power `252|τ(m)|` times over. -/
theorem three_pow_dvd_powT {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    (3 : ℤ) ^ (wordT3 m).natAbs ∣ powT m := by
  refine ⟨(-8 * tauT m) ^ (wordT3 m).natAbs, ?_⟩
  rw [powT, t2_eq hm, ← mul_pow]
  congr 1
  ring

/-- The first entry: `t₂ ^ t₃` at `m = 1` is `(-24) ^ 252`, a number of more than three hundred
digits. -/
theorem powT_one : powT 1 = (-24 : ℤ) ^ 252 ∧ (10 : ℤ) ^ 300 < powT 1 := by
  have h : powT 1 = (-24 : ℤ) ^ 252 := by
    rw [powT, show wordT2 1 = -24 from by decide, show wordT3 1 = 252 from by decide]
    norm_num
  refine ⟨h, ?_⟩
  have he : ((-24 : ℤ)) ^ 252 = 24 ^ 252 := Even.neg_pow (by decide) 24
  rw [h, he]
  norm_num

/-! ## The trinity, through every comparison

`τ(2) = -24` and `τ(3) = 252` are both divisible by three, so the product, the difference and the
remainder are too, and each therefore has digital root `3`, `6` or `9`. The integer quotient is
the exception, and for the obvious reason: it is `-1` or `0`. -/

theorem three_dvd_prodT {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : (3 : ℤ) ∣ prodT m := by
  rw [prodT_eq hm]; exact Dvd.dvd.mul_right ⟨-2016, by ring⟩ _

theorem three_dvd_diffT {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : (3 : ℤ) ∣ diffT m := by
  rw [(diffT_eq hm).1]; exact Dvd.dvd.mul_right ⟨-92, by ring⟩ _

theorem three_dvd_modT {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : (3 : ℤ) ∣ modT m := by
  rw [modT_eq hm]
  split
  · exact Dvd.dvd.mul_right ⟨76, by ring⟩ _
  · exact Dvd.dvd.mul_right ⟨-8, by ring⟩ _

/-- The pointwise product has digital root in the trinity. -/
theorem prodT_mem_trinity {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    Tesla369.digitalRoot (prodT m).natAbs ∈ Tesla369.trinity :=
  coeff_mem_trinity (ne_of_lt (prodT_neg hm)) (three_dvd_prodT hm)

/-- The pointwise difference has digital root in the trinity. -/
theorem diffT_mem_trinity {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    Tesla369.digitalRoot (diffT m).natAbs ∈ Tesla369.trinity :=
  coeff_mem_trinity (diffT_ne_zero hm) (three_dvd_diffT hm)

/-- The pointwise remainder has digital root in the trinity. -/
theorem modT_mem_trinity {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    Tesla369.digitalRoot (modT m).natAbs ∈ Tesla369.trinity :=
  coeff_mem_trinity (modT_ne_zero hm) (three_dvd_modT hm)

/-- **The exception.** The integer quotient never has digital root in the trinity: it is `-1` or
`0`, and neither `1` nor `0` lies in `{3, 6, 9}`. Dividing the two graphs throws away exactly the
scale in which the trinity lives. -/
theorem quotT_notMem_trinity {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    Tesla369.digitalRoot (quotT m).natAbs ∉ Tesla369.trinity := by
  rw [quotT_eq hm]
  split <;> decide

/-! ## The comparison, tabulated -/

/-- The two sequences and their comparisons at `m = 1, 2, 3`, as one kernel computation: the
numbers printed under the plate. -/
theorem comparison_table :
    [wordT2 1, wordT3 1, prodT 1, diffT 1, quotT 1, modT 1] =
        [(-24 : ℤ), 252, -6048, -276, -1, 228] ∧
      [wordT2 2, wordT3 2, prodT 2, diffT 2, quotT 2, modT 2] =
        [(576 : ℤ), -6048, -3483648, 6624, 0, 576] ∧
      [wordT2 3, wordT3 3, prodT 3, diffT 3, quotT 3, modT 3] =
        [(-6048 : ℤ), 63504, -384072192, -69552, -1, 57456] ∧
      [ratioT 1, ratioT 2, ratioT 3] = [(-2 / 21 : ℚ), -2 / 21, -2 / 21] := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [ratioT_eq (by decide), ratioT_eq (by decide), ratioT_eq (by decide)]

end T2vsT3
