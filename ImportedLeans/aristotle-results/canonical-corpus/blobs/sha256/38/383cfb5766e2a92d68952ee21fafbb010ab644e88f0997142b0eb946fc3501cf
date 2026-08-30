/-
**The `C₃` phase carrier and its discrete Fourier matrix.**

This file makes explicit, over the actual complex numbers, the phase algebra
that has so far been used only in a semantic (label-level) form:

* `zeta3 = (-1 + √3 i)/2`, a primitive cube root of unity;
* `zeta3_pow_three`, `zeta3_ne_one`, `one_add_zeta3_add_sq` (`1 + ζ + ζ² = 0`);
* `zeta3_inv_eq_sq` (`ζ⁻¹ = ζ²`) and `conj_zeta3` (`conj ζ = ζ²`), i.e. the two
  nontrivial phases form a single conjugate/inverse pair;
* the `3 × 3` discrete Fourier matrix

      F₃ = ![![1, 1, 1], ![1, ζ, ζ²], ![1, ζ², ζ]]

  (`fourier3`), its character description `fourier3_apply` (`F₃ i j = ζ^(i*j)`),
  the conjugation swap of its two nontrivial rows (`fourier3_conj_row`), and the
  orthogonality relations `fourier3_row_orthogonal`, `fourier3_mul_conjTranspose`
  (`F₃ F₃ᴴ = 3 • 1`), hence `fourier3_det_ne_zero`;
* the trace/norm bridge from cyclotomic data to real observables:
  `trace_cyclotomic_real`, `norm_cyclotomic_real` and its nonnegativity
  `norm_cyclotomic_nonneg` (the norm form `a² + b² + c² - ab - bc - ca`).

Nothing here is used by the analytic Riemann files; it is a self-contained
algebraic layer.
-/
import Mathlib

namespace RiemannAnalytic

open Complex

/-! ### A primitive cube root of unity -/

/-- The primitive cube root of unity `ζ = e^{2πi/3} = -1/2 + (√3/2) i`. -/
noncomputable def zeta3 : ℂ := (-1 + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  have h : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [← Complex.ofReal_pow, h]
  norm_num

/-- `ζ² = -1/2 - (√3/2) i`. -/
theorem zeta3_sq : zeta3 ^ 2 = (-1 - (Real.sqrt 3 : ℝ) * Complex.I) / 2 := by
  have hs := sqrt_three_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [zeta3]
  linear_combination (Complex.I ^ 2 / 4) * hs + (3 / 4 : ℂ) * hI

/-- `1 + ζ + ζ² = 0`: both nontrivial characters are orthogonal to the constant mode. -/
theorem one_add_zeta3_add_sq : 1 + zeta3 + zeta3 ^ 2 = 0 := by
  rw [zeta3_sq, zeta3]
  ring

/-- `ζ³ = 1`. -/
theorem zeta3_pow_three : zeta3 ^ 3 = 1 := by
  have hs := sqrt_three_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hcube : zeta3 ^ 3 = zeta3 ^ 2 * zeta3 := by ring
  rw [hcube, zeta3_sq, zeta3]
  linear_combination (-(Complex.I ^ 2) / 4) * hs - (3 / 4 : ℂ) * hI

theorem zeta3_ne_one : zeta3 ≠ 1 := by
  intro h
  have hsum := one_add_zeta3_add_sq
  rw [h] at hsum
  norm_num at hsum

theorem zeta3_ne_zero : zeta3 ≠ 0 := by
  intro h
  have := zeta3_pow_three
  rw [h] at this
  simp at this

/-- `ζ⁻¹ = ζ²`: inversion and squaring are the same operation on the `C₃` carrier. -/
theorem zeta3_inv_eq_sq : zeta3⁻¹ = zeta3 ^ 2 := by
  have h3 := zeta3_pow_three
  have hne := zeta3_ne_zero
  field_simp
  first
    | linear_combination h3
    | linear_combination -h3

/-- `conj ζ = ζ²`: the two nontrivial phases are a complex-conjugate pair. -/
theorem conj_zeta3 : (starRingEnd ℂ) zeta3 = zeta3 ^ 2 := by
  rw [zeta3_sq, zeta3]
  simp only [map_div₀, map_add, map_mul, map_neg, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

/-- `ζ + ζ⁻¹ = -1`: the cyclotomic trace of the phase. -/
theorem zeta3_add_inv : zeta3 + zeta3⁻¹ = -1 := by
  rw [zeta3_inv_eq_sq]
  have := one_add_zeta3_add_sq
  linear_combination this

/-- `ζ · ζ⁻¹ = 1`: the cyclotomic norm of the phase. -/
theorem zeta3_mul_inv : zeta3 * zeta3⁻¹ = 1 := mul_inv_cancel₀ zeta3_ne_zero

/-! ### The discrete Fourier matrix of `C₃` -/

/-- The `C₃` discrete Fourier matrix

    F₃ = ![![1, 1, 1], ![1, ζ, ζ²], ![1, ζ², ζ]].

Row `0` is the trivial character, rows `1` and `2` the conjugate pair of
nontrivial characters. -/
noncomputable def fourier3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, zeta3, zeta3 ^ 2; 1, zeta3 ^ 2, zeta3]

/-- `F₃ i j = ζ^{ij}`: the matrix really is the character table of `C₃`. -/
theorem fourier3_apply (i j : Fin 3) : fourier3 i j = zeta3 ^ ((i : ℕ) * (j : ℕ)) := by
  have h3 := zeta3_pow_three
  have h4 : zeta3 ^ 4 = zeta3 := by
    calc zeta3 ^ 4 = zeta3 ^ 3 * zeta3 := by ring
      _ = zeta3 := by rw [h3]; ring
  fin_cases i <;> fin_cases j <;> simp [fourier3, h4]

/-- The two nontrivial rows are complex conjugates of each other. -/
theorem fourier3_conj_row (j : Fin 3) :
    (starRingEnd ℂ) (fourier3 1 j) = fourier3 2 j := by
  have hc := conj_zeta3
  have hc2 : (starRingEnd ℂ) (zeta3 ^ 2) = zeta3 := by
    have : (starRingEnd ℂ) (zeta3 ^ 2) = ((starRingEnd ℂ) zeta3) ^ 2 := by
      simp
    rw [this, hc, ← pow_mul]
    have h3 := zeta3_pow_three
    calc zeta3 ^ (2 * 2) = zeta3 ^ 3 * zeta3 := by ring
      _ = zeta3 := by rw [h3]; ring
  fin_cases j <;> simp [fourier3, hc, hc2]

/-- Orthogonality of the Fourier rows: `∑ₖ conj(F₃ i k) · F₃ j k = 3` if `i = j`
and `0` otherwise. -/
theorem fourier3_row_orthogonal (i j : Fin 3) :
    ∑ k : Fin 3, (starRingEnd ℂ) (fourier3 i k) * fourier3 j k
      = if i = j then (3 : ℂ) else 0 := by
  have h3 := zeta3_pow_three
  have hsum := one_add_zeta3_add_sq
  have hc := conj_zeta3
  have hc2 : (starRingEnd ℂ) (zeta3 ^ 2) = zeta3 := by
    have : (starRingEnd ℂ) (zeta3 ^ 2) = ((starRingEnd ℂ) zeta3) ^ 2 := by simp
    rw [this, hc, ← pow_mul]
    calc zeta3 ^ (2 * 2) = zeta3 ^ 3 * zeta3 := by ring
      _ = zeta3 := by rw [h3]; ring
  fin_cases i <;> fin_cases j <;>
    simp [fourier3, Fin.sum_univ_three, hc, hc2] <;>
    first
      | ring1
      | linear_combination hsum
      | linear_combination -hsum
      | linear_combination (zeta3 - 2) * h3
      | linear_combination (2 - zeta3) * h3
      | linear_combination (-2 : ℂ) * h3
      | linear_combination (2 : ℂ) * h3
      | linear_combination zeta3 * h3
      | linear_combination -(zeta3 * h3)
      | linear_combination hsum + h3
      | linear_combination -hsum - h3
      | linear_combination hsum + zeta3 * h3

/-- `F₃ F₃ᴴ = 3 • 1`: the `C₃` Fourier matrix is unitary up to the factor `√3`. -/
theorem fourier3_mul_conjTranspose :
    fourier3 * fourier3.conjTranspose = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  have h := fourier3_row_orthogonal j i
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, hstar]
  have hcomm : ∑ k : Fin 3, fourier3 i k * (starRingEnd ℂ) (fourier3 j k)
      = ∑ k : Fin 3, (starRingEnd ℂ) (fourier3 j k) * fourier3 i k := by
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hcomm, h]
  by_cases hij : j = i
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem fourier3_det_ne_zero : fourier3.det ≠ 0 := by
  intro h
  have hmul := fourier3_mul_conjTranspose
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h, zero_mul] at this
  have hdet : ((3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = 27 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    norm_num
  rw [hdet] at this
  norm_num at this

/-! ### From conjugate phases to real observables -/

/-- The cyclotomic trace `z + conj z` of `z = a + bζ + cζ⁻¹` is the real number
`2a - b - c`. -/
theorem trace_cyclotomic_real (a b c : ℝ) :
    ((a : ℂ) + b * zeta3 + c * zeta3⁻¹)
        + (starRingEnd ℂ) ((a : ℂ) + b * zeta3 + c * zeta3⁻¹)
      = ((2 * a - b - c : ℝ) : ℂ) := by
  have hinv := zeta3_inv_eq_sq
  have hc := conj_zeta3
  have hc2 : (starRingEnd ℂ) (zeta3 ^ 2) = zeta3 := by
    have h3 := zeta3_pow_three
    have : (starRingEnd ℂ) (zeta3 ^ 2) = ((starRingEnd ℂ) zeta3) ^ 2 := by simp
    rw [this, hc, ← pow_mul]
    calc zeta3 ^ (2 * 2) = zeta3 ^ 3 * zeta3 := by ring
      _ = zeta3 := by rw [h3]; ring
  rw [hinv]
  simp only [map_add, map_mul, Complex.conj_ofReal, hc, hc2]
  have hsum := one_add_zeta3_add_sq
  push_cast
  linear_combination ((b : ℂ) + c) * hsum

/-- The cyclotomic norm `z · conj z` of `z = a + bζ + cζ⁻¹` is the real number
`a² + b² + c² - ab - bc - ca`. -/
theorem norm_cyclotomic_real (a b c : ℝ) :
    ((a : ℂ) + b * zeta3 + c * zeta3⁻¹)
        * (starRingEnd ℂ) ((a : ℂ) + b * zeta3 + c * zeta3⁻¹)
      = ((a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a : ℝ) : ℂ) := by
  have hinv := zeta3_inv_eq_sq
  have hc := conj_zeta3
  have h3 := zeta3_pow_three
  have hc2 : (starRingEnd ℂ) (zeta3 ^ 2) = zeta3 := by
    have : (starRingEnd ℂ) (zeta3 ^ 2) = ((starRingEnd ℂ) zeta3) ^ 2 := by simp
    rw [this, hc, ← pow_mul]
    calc zeta3 ^ (2 * 2) = zeta3 ^ 3 * zeta3 := by ring
      _ = zeta3 := by rw [h3]; ring
  rw [hinv]
  simp only [map_add, map_mul, Complex.conj_ofReal, hc, hc2]
  have hsum := one_add_zeta3_add_sq
  push_cast
  linear_combination ((a : ℂ) * b + (a : ℂ) * c + (b : ℂ) * c) * hsum
      + ((b : ℂ) ^ 2 + (c : ℂ) ^ 2 + (b : ℂ) * (c : ℂ) * zeta3) * h3

/-- The cyclotomic norm form is nonnegative: it is half a sum of squares. -/
theorem norm_cyclotomic_nonneg (a b c : ℝ) :
    0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

end RiemannAnalytic
