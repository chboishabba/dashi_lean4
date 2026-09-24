/-
The two complex-`Φ` interference channels of a pair of hypothetical zeros.

For two zero coordinates `z, w` the Alpöge--Furman pairing produces two scalar
channels: the bilinear one

  `S = ∑_k φ̂(z - τ_k) φ̂(w - τ_k)`

and the sesquilinear (Hermitian) one

  `H = ∑_k φ̂(z - τ_k) conj (φ̂(w - τ_k))`.

Over the whole lattice these are identified *exactly*, by the complex bilinear
Poisson identity and the reflection law of a real even taper, with

  `S = L Φ(z - w)`,   `H = L Φ(z - conj w)`.

Consequently the mixed interference weight of `FrobeniusDecomposition.lean`,
which by `mixedChannel_parseval` equals `((Im S)² + (Im H)²)/2`, becomes the
complex-`Φ` kernel

  `(L²/2) [ (Im Φ(z - w))² + (Im Φ(z - conj w))² ]`.

This file proves those identifications and the accompanying decay facts: the
kernel is real on the real axis (so both channels vanish for two on-line zeros
with the same ordinate offset), and it decays like `|Re|⁻¹` along horizontal
lines, with an explicit constant.
-/
import RiemannAnalytic.ImaginaryChannel

namespace RiemannAnalytic

open MeasureTheory Complex

/-! ### The squared taper is again a `C¹` taper -/

namespace C1Taper

variable {φ : ℝ → ℝ} {R : ℝ}

theorem deriv_sq (hφ : C1Taper φ R) (t : ℝ) :
    deriv (fun u => φ u ^ 2) t = 2 * φ t * deriv φ t := by
  have h := ((hφ.diff t).hasDerivAt.pow 2).deriv
  simpa [mul_comm, mul_assoc, mul_left_comm] using h

/-- The square of a `C¹` taper is a `C¹` taper of the same radius. -/
theorem sq (hφ : C1Taper φ R) : C1Taper (fun u => φ u ^ 2) R where
  diff := hφ.diff.pow 2
  contDeriv := by
    have : Continuous fun t => 2 * φ t * deriv φ t := by
      exact (continuous_const.mul hφ.cont).mul hφ.contDeriv
    exact this.congr fun t => (hφ.deriv_sq t).symm
  supp := fun t ht => by simp [hφ.supp t ht]

end C1Taper

/-! ### The kernel is real on the real axis -/

/-- The complex extension of a real even taper is real on the real axis. -/
theorem PhiExt_im_ofReal (ψ : ℝ → ℝ) (hev : ∀ t, ψ (-t) = ψ t) (x : ℝ) :
    (PhiExt ψ (x : ℂ)).im = 0 := by
  have h := PhiExt_conj_even ψ hev (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-! ### The two channels -/

/-- The **bilinear channel** over the whole lattice: `S = L Φ(z - w)`. -/
theorem grid_Sbil {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (hev : ∀ t, φ (-t) = φ t)
    {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (z w : ℂ) :
    ∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
        * PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L))
      = (L : ℂ) * PhiExt (fun t => φ t ^ 2) (z - w) :=
  complex_bilinear_poisson hφ hev hL h2R z w

/-- The **Hermitian channel** over the whole lattice: `H = L Φ(z - conj w)`. -/
theorem grid_Hsesq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (hev : ∀ t, φ (-t) = φ t)
    {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (z w : ℂ) :
    ∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
        * (starRingEnd ℂ) (PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L)))
      = (L : ℂ) * PhiExt (fun t => φ t ^ 2) (z - (starRingEnd ℂ) w) := by
  rw [← complex_bilinear_poisson hφ hev hL h2R z ((starRingEnd ℂ) w)]
  refine tsum_congr fun n => ?_
  congr 1
  rw [PhiExt_conj_even φ hev]
  have hshift : (starRingEnd ℂ) (w + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (L : ℂ)))
      = (starRingEnd ℂ) w + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (L : ℂ)) := by
    simp [Complex.ext_iff]
  rw [hshift]

/-- **The mixed interference weight as a complex-`Φ` kernel.**

With `S` and `H` the two lattice channels of the pair `(z, w)`, the quantity
`((Im S)² + (Im H)²)/2` — which by `mixedChannel_parseval` is exactly the mixed
interference weight `N` of the Frobenius pair expansion — equals

  `(L²/2) [ (Im Φ(z - w))² + (Im Φ(z - conj w))² ]`. -/
theorem mixedLoss_eq_Phi_kernel {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (z w : ℂ) :
    (∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
          * PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L))).im ^ 2
        + (∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
          * (starRingEnd ℂ) (PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L)))).im ^ 2
      = L ^ 2 * ((PhiExt (fun t => φ t ^ 2) (z - w)).im ^ 2
          + (PhiExt (fun t => φ t ^ 2) (z - (starRingEnd ℂ) w)).im ^ 2) := by
  rw [grid_Sbil hφ hev hL h2R z w, grid_Hsesq hφ hev hL h2R z w]
  simp [Complex.mul_im]
  ring

/-! ### Decay of the kernel along horizontal lines -/

/-- **Horizontal decay of the `Φ`-kernel.**  The modulus of the kernel times the
distance to the imaginary axis is bounded by the `L¹` mass of the twisted
derivative of the squared taper. -/
theorem norm_PhiKernel_mul_abs_re_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (z : ℂ) :
    ‖PhiExt (fun t => φ t ^ 2) z‖ * |z.re|
      ≤ ∫ u : ℝ, |deriv (fun t => φ t ^ 2) u| * Real.exp (z.im * u) :=
  norm_PhiExt_mul_abs_re_le hφ.sq z

/-- Consequently each interference channel of a pair of zeros decays like the
inverse distance between their coordinates. -/
theorem norm_PhiKernel_le_of_re {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {z : ℂ}
    (hz : z.re ≠ 0) :
    ‖PhiExt (fun t => φ t ^ 2) z‖
      ≤ (∫ u : ℝ, |deriv (fun t => φ t ^ 2) u| * Real.exp (z.im * u)) / |z.re| := by
  have hpos : 0 < |z.re| := abs_pos.2 hz
  rw [le_div_iff₀ hpos]
  exact norm_PhiKernel_mul_abs_re_le hφ z

/-- The imaginary part of the kernel obeys the same decay. -/
theorem abs_PhiKernel_im_le_of_re {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {z : ℂ}
    (hz : z.re ≠ 0) :
    |(PhiExt (fun t => φ t ^ 2) z).im|
      ≤ (∫ u : ℝ, |deriv (fun t => φ t ^ 2) u| * Real.exp (z.im * u)) / |z.re| :=
  le_trans (Complex.abs_im_le_norm _) (norm_PhiKernel_le_of_re hφ hz)

end RiemannAnalytic
