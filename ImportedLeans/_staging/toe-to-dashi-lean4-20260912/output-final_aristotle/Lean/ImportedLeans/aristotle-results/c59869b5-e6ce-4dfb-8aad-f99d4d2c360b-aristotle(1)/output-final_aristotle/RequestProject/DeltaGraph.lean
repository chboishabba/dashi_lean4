import Mathlib
import RequestProject.Tesla369
import RequestProject.Hecke23

/-!
# The actual modular form, and the actual graph

Everything about Hecke operators in this project so far has been about *one* eigenform in the
abstract: an unknown system `a : ℕ → R` satisfying the multiplicative axioms of
`Hecke23.HeckeSystem`. This file replaces the unknown by the smallest concrete example, the
discriminant form of weight `12`,

`Δ(z) = q ∏_{m ≥ 1} (1 - q^m)^24 = ∑_{n ≥ 1} τ(n) q^n`,  `q = e^{2πi z}`,

computes its coefficients `τ(n)` inside Lean, and proves the facts that the pictures
`paper/delta_coefficients.svg`, `paper/delta_domain.svg` and `paper/delta_imaginary_axis.svg`
display.

* `deltaCoeffs`, `tau` : the eta product, expanded by truncated polynomial arithmetic.
  `tau n` is the coefficient of `q ^ n`.
* `tau_table` : the thirty numbers `τ(1), …, τ(30)` that the coefficient plot draws.
* `tau_four`, `tau_six`, `tau_nine`, `tau_twelve`, `tau_twentyseven` : the five Hecke words of
  `RequestProject/HeckeWords.lean`, checked on the real form. `τ(6) = τ(2)τ(3)`,
  `τ(9) = τ(3)² - 3¹¹`, `τ(12) = τ(2)²τ(3) - 2¹¹τ(3)`, `τ(27) = τ(3)³ - 2·3¹¹τ(3)`: the abstract
  identities and the actual integers agree.
* `tau_ramanujan_bound` : `|τ(n)| ≤ d(n) · n^{11/2}` for every `n ≤ 30`, in the equivalent
  integral form. This is the vertical scale of the coefficient plot.
* `tau_congr_mod_27`, `three_dvd_tau_iff_three_dvd_sigma` : the three-adic face of `Δ`. For
  `n ≤ 30` prime to three, `τ(n) ≡ n² σ₇(n) (mod 27)`, and consequently `3 ∣ τ(n)` exactly when
  `3 ∣ σ(n)`. (Both are checked on that range here, not proved for all `n`.)
* `digitalRoot_natAbs_mem_trinity_iff` : for a nonzero integer, the digital-root trinity
  `{3, 6, 9}` of `Tesla369` detects divisibility by three — so the highlighted bars of the
  coefficient plot are exactly the coefficients whose digital root is `3`, `6` or `9`.
* `qParam`, `deltaApprox`, `deltaApprox_periodic`, `abs_qParam` : the function actually plotted
  on the upper half plane, its horizontal period `1`, and the modulus `|q| = e^{-2π y}` that
  makes the picture converge and fade to zero at the cusp.

Not proved here: that these `τ(n)` satisfy the Hecke relations for *all* `n` (Mordell), and the
`S`-invariance `Δ(-1/z) = z¹² Δ(z)` that the domain picture displays. The identities above are
verified on the plotted range only, and the file says so.
-/

namespace DeltaGraph

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## The coefficients -/

/-- Multiply a truncated power series (coefficient list, lowest degree first) by `1 - q ^ n`. -/
def mulOneSub (n : ℕ) (p : List ℤ) : List ℤ :=
  List.zipWith (· - ·) p (List.replicate n 0 ++ p)

/-- The first `N` coefficients of `∏_{m = 1}^{N} (1 - q ^ m) ^ 24`, lowest degree first. -/
def deltaCoeffs (N : ℕ) : List ℤ :=
  (List.range' 1 N).foldl
    (fun p n => (List.replicate 24 ()).foldl (fun q _ => mulOneSub n q) p)
    (1 :: List.replicate (N - 1) 0)

/-- **Ramanujan's `τ`.** `tau n` is the coefficient of `q ^ n` in
`Δ = q ∏_{m ≥ 1} (1 - q ^ m) ^ 24`, i.e. the coefficient of `q ^ (n-1)` in the product; the
factors with `m ≥ n` do not affect it, so truncating the product at `m = n` is harmless. -/
def tau (n : ℕ) : ℤ := (deltaCoeffs n).getD (n - 1) 0

/-- **The plotted data.** The thirty coefficients drawn in `paper/delta_coefficients.svg`. -/
theorem tau_table : (List.range' 1 30).map tau =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
     534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
     10661420, -7109760, -4219488, -12830688, 18643272, 21288960, -25499225,
     13865712, -73279080, 24647168, 128406630, -29211840] := by decide

theorem tau_one : tau 1 = 1 := by decide

theorem tau_two : tau 2 = -24 := by decide

theorem tau_three : tau 3 = 252 := by decide

/-! ## The five Hecke words, on the real form

`Δ` has weight `k = 12`, so the factors `p ^ (k - 1)` of `Hecke23.HeckeSystem` are `p ^ 11`. -/

/-- `T₂ T₂`: `τ(4) = τ(2)² - 2¹¹`. -/
theorem tau_four : tau 4 = tau 2 ^ 2 - 2 ^ 11 := by decide

/-- `T₂ T₃ = T₆`: `τ(6) = τ(2) τ(3)`. -/
theorem tau_six : tau 6 = tau 2 * tau 3 := by decide

/-- `T₃ T₃ = T₉ + 3¹¹ T₁`: `τ(9) = τ(3)² - 3¹¹`. -/
theorem tau_nine : tau 9 = tau 3 ^ 2 - 3 ^ 11 := by decide

/-- `T₂ T₃ T₂ = T₁₂ + 2¹¹ T₃`: `τ(12) = τ(2)² τ(3) - 2¹¹ τ(3)`. -/
theorem tau_twelve : tau 12 = tau 2 ^ 2 * tau 3 - 2 ^ 11 * tau 3 := by decide

/-- `T₃ T₃ T₃ = T₂₇ + 2·3¹¹ T₃`: `τ(27) = τ(3)³ - 2·3¹¹ τ(3)`. -/
theorem tau_twentyseven : tau 27 = tau 3 ^ 3 - 2 * 3 ^ 11 * tau 3 := by decide

/-- The five multipliers of `HeckeWords.delta_values`, on the actual form:
`τ(2), τ(3), τ(6), τ(12) + 2¹¹ τ(3), τ(27) + 2·3¹¹ τ(3)`. -/
theorem tau_word_values :
    (tau 2, tau 3, tau 6, tau 12 + 2 ^ 11 * tau 3, tau 27 + 2 * 3 ^ 11 * tau 3) =
      ((-24 : ℤ), 252, -6048, 145152, 16003008) := by decide

/-! ## The vertical scale of the coefficient plot -/

/-- **Ramanujan–Petersson, on the plotted range.** For `n ≤ 30`, `|τ(n)| ≤ d(n) · n^{11/2}`,
written without square roots as `τ(n)² ≤ d(n)² n¹¹`. This is why the normalised coefficients
`τ(n) / n^{11/2}` of the plot stay inside the envelope `±d(n)`, and the prime ones inside `±2`. -/
theorem tau_ramanujan_bound :
    ∀ n ∈ Finset.Icc 1 30, (tau n) ^ 2 ≤ ((n.divisors.card : ℤ)) ^ 2 * (n : ℤ) ^ 11 := by
  decide

/-! ## The three-adic face of `Δ` -/

/-- `σ₇ n = ∑_{d ∣ n} d ^ 7`, as an integer. -/
def sigma7 (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) ^ 7

/-- `σ n = ∑_{d ∣ n} d`, as an integer. -/
def sigma1 (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ)

/-- **Checked for `n ≤ 30` prime to three:** `τ(n) ≡ n² σ₇(n) (mod 27)`. -/
theorem tau_congr_mod_27 :
    ∀ n ∈ Finset.Icc 1 30, ¬ (3 ∣ n) → (27 : ℤ) ∣ (tau n - (n : ℤ) ^ 2 * sigma7 n) := by
  decide

/-- **Checked for `n ≤ 30` prime to three:** three divides `τ(n)` exactly when it divides
`σ(n)`. (A consequence of the congruence above, since `d ^ 7 ≡ d` and `n ^ 2 ≡ 1` mod three.) -/
theorem three_dvd_tau_iff_three_dvd_sigma :
    ∀ n ∈ Finset.Icc 1 30, ¬ (3 ∣ n) → ((3 : ℤ) ∣ tau n ↔ (3 : ℤ) ∣ sigma1 n) := by
  decide

/-- **The trinity reads off divisibility by three of an integer.** For `m ≠ 0`, the digital root
of `|m|` lies in `{3, 6, 9}` exactly when `3 ∣ m`; the highlighted bars of the coefficient plot
are exactly the `τ(n)` with digital root `3`, `6` or `9`. -/
theorem digitalRoot_natAbs_mem_trinity_iff {m : ℤ} (hm : m ≠ 0) :
    Tesla369.digitalRoot m.natAbs ∈ Tesla369.trinity ↔ (3 : ℤ) ∣ m := by
  rw [Tesla369.digitalRoot_mem_trinity_iff (Int.natAbs_pos.mpr hm)]
  omega

/-- The digital roots of the first thirty coefficients — the colouring of the bars. -/
theorem digitalRoot_tau_table :
    (List.range' 1 30).map (fun n => Tesla369.digitalRoot (tau n).natAbs) =
      [1, 6, 9, 5, 6, 9, 4, 6, 9, 9, 3, 9, 1, 6, 9, 7, 9, 9, 2, 3, 9, 9, 6, 9, 2, 6, 9, 2, 3, 9] := by
  decide

/-! ## The function plotted on the upper half plane -/

open Complex in
/-- The nome `q = e^{2πi z}`. -/
noncomputable def qParam (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

/-- The partial sum `∑_{n = 1}^{N} τ(n) q^n` of the `q`-expansion: the function whose modulus and
argument are drawn in `paper/delta_domain.svg`. -/
noncomputable def deltaApprox (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (tau (n + 1) : ℂ) * qParam z ^ (n + 1)

/-- `q` is invariant under `z ↦ z + 1`. -/
theorem qParam_add_one (z : ℂ) : qParam (z + 1) = qParam z := by
  have h : (2 : ℂ) * Real.pi * Complex.I * (z + 1)
      = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I := by ring
  rw [qParam, qParam, h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Horizontal period one** — the left-right repetition visible in the domain picture. -/
theorem deltaApprox_periodic (N : ℕ) (z : ℂ) : deltaApprox N (z + 1) = deltaApprox N z := by
  simp [deltaApprox, qParam_add_one]

/-- `|q| = e^{-2π y}`: the picture converges, and fades to zero at the cusp `y → ∞`. -/
theorem abs_qParam (z : ℂ) : ‖qParam z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [qParam, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The plotted approximation vanishes at the cusp: as `y → ∞` every term `τ(n) q^n` does. -/
theorem abs_qParam_lt_one {z : ℂ} (hz : 0 < z.im) : ‖qParam z‖ < 1 := by
  rw [abs_qParam]
  rw [Real.exp_lt_one_iff]
  have : 0 < 2 * Real.pi * z.im := by positivity
  linarith

end DeltaGraph
