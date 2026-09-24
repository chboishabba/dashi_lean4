/-
Hermitian specialisation of the complex bilinear Poisson identity, and the
resulting transverse energy floor on the centred grid.

`ComplexPoisson.lean` proves, for a `C¹` real even taper supported in `[-R,R]`
with `2R ≤ L` and *arbitrary complex* `z, w`,

  `∑_{n ∈ ℤ} φ̂(z + n·2π/L) φ̂(w + n·2π/L) = L · Φ(z - w)`.

Setting `w = conj z` and using the reflection law `conj (φ̂ z) = φ̂ (conj z)`
turns the left side into a sum of squared moduli.  For the zero coordinate
`z = γ - iα` one has `z - conj z = -2iα`, so the identity reads

  `∑_{n ∈ ℤ} |φ̂(γ - iα + n·2π/L)|² = L · Φ(-2iα)`.

Combining this with `TaperCoercivity.lean` gives the literal transverse
energy floor

  `gridEnergy(α) - gridEnergy(0) = L · ∫ φ(u)² (cosh(2αu) - 1) du
                                 ≥ (9/128) · L⁴ · α²`

in the source regime `a ≥ 3L/8`.
-/
import RiemannAnalytic.ComplexPoisson

namespace RiemannAnalytic

open MeasureTheory Complex

/-! ### The Hermitian Poisson identity -/

/-- **Hermitian Poisson identity.**  Specialising the complex bilinear Poisson
identity at `w = conj z` turns the grid sum into a sum of squared moduli:

  `∑_{n ∈ ℤ} |φ̂(z + n·2π/L)|² = L · Φ(z - conj z)`. -/
theorem hermitian_poisson {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (z : ℂ) :
    ((∑' n : ℤ, ‖PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))‖ ^ 2 : ℝ) : ℂ)
      = (L : ℂ) * PhiExt (fun t => φ t ^ 2) (z - (starRingEnd ℂ) z) := by
  have hpoisson := complex_bilinear_poisson hφ hev hL h2R z ((starRingEnd ℂ) z)
  rw [← hpoisson, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hconj : (starRingEnd ℂ) z + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (L : ℂ))
      = (starRingEnd ℂ) (z + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (L : ℂ))) := by
    simp [Complex.ext_iff]
  rw [hconj, ← PhiExt_conj_even φ hev, Complex.mul_conj']
  push_cast
  ring

/-! ### Transverse energy of the centred grid -/

/-- The **transverse energy** of the grid of spacing `2π/L` centred at the
zero coordinate `z = γ - iα`:  `∑_{n ∈ ℤ} |φ̂(γ - iα + n·2π/L)|²`. -/
noncomputable def gridEnergy (φ : ℝ → ℝ) (L γ α : ℝ) : ℝ :=
  ∑' n : ℤ, ‖PhiExt φ ((γ : ℂ) - Complex.I * (α : ℂ)
      + ((n : ℝ) : ℂ) * ((2 * Real.pi / L : ℝ) : ℂ))‖ ^ 2

/-- The zero coordinate minus its conjugate is the purely imaginary point
`-2iα`. -/
theorem zeroCoord_sub_conj (γ α : ℝ) :
    ((γ : ℂ) - Complex.I * (α : ℂ)) - (starRingEnd ℂ) ((γ : ℂ) - Complex.I * (α : ℂ))
      = -(2 * α : ℝ) * Complex.I := by
  simp [Complex.ext_iff]
  ring

/-- **The transverse energy is the exponential moment of the squared taper.**
`∑_{n ∈ ℤ} |φ̂(γ - iα + n·2π/L)|² = L · ∫ φ(u)² cosh(2αu) du`. -/
theorem gridEnergy_eq_cosh_moment {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (γ α : ℝ) :
    gridEnergy φ L γ α = L * ∫ u : ℝ, φ u ^ 2 * Real.cosh (2 * α * u) := by
  have h := hermitian_poisson hφ hev hL h2R ((γ : ℂ) - Complex.I * (α : ℂ))
  rw [zeroCoord_sub_conj, PhiExt_ofReal_neg_two_mul_I,
    integral_even_mul_exp_eq_cosh hφ.toCompactTaper hev α] at h
  have := congrArg Complex.re h
  simpa [gridEnergy] using this

/-- **The transverse energy excess.**  The energy at offset `α` exceeds the
energy on the critical line by exactly `L` times the taper excess. -/
theorem gridEnergy_excess {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (γ γ' α : ℝ) :
    gridEnergy φ L γ α - gridEnergy φ L γ' 0 = L * taperExcess φ α := by
  have hint₁ : Integrable fun t : ℝ => φ t ^ 2 * Real.cosh (2 * α * t) :=
    hφ.toCompactTaper.integrable_sq_mul (by fun_prop)
  have hsplit : taperExcess φ α
      = (∫ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t)) - ∫ t : ℝ, φ t ^ 2 := by
    unfold taperExcess
    rw [← integral_sub hint₁ hφ.toCompactTaper.integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  rw [gridEnergy_eq_cosh_moment hφ hev hL h2R γ α,
    gridEnergy_eq_cosh_moment hφ hev hL h2R γ' 0, hsplit]
  simp
  ring

/-- **Literal transverse energy floor.**

For a `C¹` real even taper supported in `[-R, R]` with `2R ≤ L` and a plateau
of half-width `a ≥ 3L/8` — the source regime `a = L/2 - w` with `8w ≤ L` — the
transverse energy of the grid centred at an off-line zero coordinate exceeds
the on-line energy by at least `(9/128) L⁴ α²`. -/
theorem gridEnergy_transverse_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (γ γ' α : ℝ) :
    9 / 128 * L ^ 4 * α ^ 2 ≤ gridEnergy φ L γ α - gridEnergy φ L γ' 0 := by
  rw [gridEnergy_excess hφ hev hL h2R γ γ' α]
  exact transverseDefect_lower_source_regime hφ.toCompactTaper hL ha hplat α

/-- The transverse energy floor is strict for a genuinely off-line zero:
if `α ≠ 0` then the grid energy strictly exceeds its on-line value. -/
theorem gridEnergy_lt_of_ne_zero {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (γ γ' : ℝ)
    {α : ℝ} (hα : α ≠ 0) :
    gridEnergy φ L γ' 0 < gridEnergy φ L γ α := by
  have hfloor := gridEnergy_transverse_floor hφ hev hL h2R ha hplat γ γ' α
  have hpos : 0 < 9 / 128 * L ^ 4 * α ^ 2 := by positivity
  linarith

end RiemannAnalytic
