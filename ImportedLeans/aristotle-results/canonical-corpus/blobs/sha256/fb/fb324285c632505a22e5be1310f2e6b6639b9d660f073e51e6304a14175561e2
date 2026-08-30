/-
Complex bilinear (Fourier--Laplace) extension of a real, even taper.

This file discharges, at literal analytic strength over `ℂ` and `ℝ`, the
symmetry package that the Agda module
`DASHI.Analysis.RiemannCenteredGridRetentionExact` only records abstractly:

* the extension `Φ` of a real even taper is even,
* it satisfies the reflection/conjugation law `conj (Φ z) = Φ (conj z)`,
* consequently, on the centred grid `z_k = k·h - i·α` the `+k` and `-k`
  samples are complex conjugates, so their imaginary parts are opposite and
  their squares agree, while the `k = 0` sample is real.

No integrability hypothesis is needed: `integral_conj` and
`integral_neg_eq_self` are unconditional in Mathlib (when the integrand fails
to be integrable both sides degenerate in the same way).
-/
import Mathlib

namespace RiemannAnalytic

open MeasureTheory Complex

/-- Complex bilinear Poisson (Fourier--Laplace) extension of a taper
`φ : ℝ → ℝ`:  `Φ φ z = ∫ φ(t) e^{-i z t} dt`. -/
noncomputable def PhiExt (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (φ t : ℂ) * Complex.exp (-(Complex.I * z * (t : ℂ)))

/-- For an even taper the complex extension is even. -/
theorem PhiExt_even (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t) (z : ℂ) :
    PhiExt φ (-z) = PhiExt φ z := by
  have h := integral_neg_eq_self
    (fun t : ℝ => (φ t : ℂ) * Complex.exp (-(Complex.I * z * (t : ℂ)))) volume
  unfold PhiExt
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hφ t]
  congr 1
  push_cast
  ring_nf

/-- Conjugation law for a real taper: `conj (Φ z) = Φ (-conj z)`. -/
theorem PhiExt_conj (φ : ℝ → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (PhiExt φ z) = PhiExt φ (-(starRingEnd ℂ) z) := by
  unfold PhiExt
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  congr 1
  ring_nf

/-- Reflection law for a real *even* taper: `conj (Φ z) = Φ (conj z)`. -/
theorem PhiExt_conj_even (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t) (z : ℂ) :
    (starRingEnd ℂ) (PhiExt φ z) = PhiExt φ ((starRingEnd ℂ) z) := by
  rw [PhiExt_conj φ z, PhiExt_even φ hφ]

/-- The centred grid of the Alpöge--Furman geometry: with the source height
chosen equal to the ordinate of the hypothetical zero, the `k`-th sample of the
extension is taken at `k·h - i·α`. -/
noncomputable def gridSample (φ : ℝ → ℝ) (h α : ℝ) (k : ℤ) : ℂ :=
  PhiExt φ ((k : ℝ) * h - Complex.I * α)

/-- The `+k` and `-k` samples on the centred grid are complex conjugates. -/
theorem gridSample_neg_eq_conj (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t)
    (h α : ℝ) (k : ℤ) :
    gridSample φ h α (-k) = (starRingEnd ℂ) (gridSample φ h α k) := by
  unfold gridSample
  rw [PhiExt_conj_even φ hφ]
  have harg : (starRingEnd ℂ) (((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ))
      = -((((-k : ℤ) : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)) := by
    push_cast
    simp [Complex.ext_iff]
  rw [harg, PhiExt_even φ hφ]

/-- Hence the imaginary parts of the `±k` samples are opposite. -/
theorem gridSample_im_neg (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t)
    (h α : ℝ) (k : ℤ) :
    (gridSample φ h α (-k)).im = -(gridSample φ h α k).im := by
  rw [gridSample_neg_eq_conj φ hφ h α k]
  simp

/-- ... and the transverse (imaginary-channel) energies of the `±k` samples
agree. -/
theorem gridSample_im_sq_neg (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t)
    (h α : ℝ) (k : ℤ) :
    (gridSample φ h α (-k)).im ^ 2 = (gridSample φ h α k).im ^ 2 := by
  rw [gridSample_im_neg φ hφ h α k]
  ring

/-- The central sample `Φ(-iα)` of a real even taper is real. -/
theorem gridSample_zero_im (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t) (h α : ℝ) :
    (gridSample φ h α 0).im = 0 := by
  have := gridSample_im_neg φ hφ h α 0
  simp only [neg_zero] at this
  linarith

end RiemannAnalytic
