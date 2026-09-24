/-
**The realified `C₃` conjugate pair is a genuine transverse plane.**

The phase carrier `{1, ζ, ζ²}` splits as a fixed singleton and a
conjugate/inverse pair `{ζ, ζ⁻¹} = {ζ, ζ²}`.  Over `ℝ` the pair realifies to the
plane spanned by the real and imaginary parts of the nontrivial Fourier
character `χ₁ = (1, ζ, ζ²)`:

    u = Re χ₁ = (1, −1/2, −1/2),      w = Im χ₁ = (0, √3/2, −√3/2).

Having two phase labels is *not* by itself a two-dimensional geometry: a pair of
collinear vectors also carries "two names".  The nondegeneracy statement that
the labels do span a plane is the positivity of the Gram defect, and here it is
an exact computation:

    ‖u‖² = ‖w‖² = 3/2,   ⟪u, w⟫ = 0,   Δ = ‖u‖²‖w‖² − ⟪u,w⟫² = 9/4 > 0

(`c3_gramDefect`, `c3_gramDefect_pos`).  Both vectors are orthogonal to the
constant/trivial mode `(1,1,1)` (`c3Real_dot_const`, `c3Imag_dot_const`), which
is the `1 + 2` splitting `full carrier = constant mode ⊕ transverse plane`; and
the conjugate character `χ₂ = (1, ζ², ζ)` spans the *same* real plane, with the
opposite orientation (`c3_conj_re`, `c3_conj_im`).

This is the finite model of the mechanism used on the source window: a
distinguished fixed coordinate plus a genuinely occupied transverse sector.
-/
import RiemannAnalytic.CubicPhase
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open Matrix

/-! ### The realified character vectors -/

/-- The real part of the nontrivial `C₃` Fourier character `χ₁ = (1, ζ, ζ²)`. -/
noncomputable def c3Real : Fin 3 → ℝ := ![1, -(1 / 2), -(1 / 2)]

/-- The imaginary part of `χ₁ = (1, ζ, ζ²)`. -/
noncomputable def c3Imag : Fin 3 → ℝ := ![0, Real.sqrt 3 / 2, -(Real.sqrt 3 / 2)]

/-- The trivial character `χ₀ = (1, 1, 1)`: the constant/fixed mode. -/
def c3Const : Fin 3 → ℝ := ![1, 1, 1]

theorem c3Real_eq (j : Fin 3) : c3Real j = (fourier3 1 j).re := by
  have hz : zeta3.re = -(1 / 2) := by
    simp [zeta3, Complex.add_re, Complex.mul_re]
    norm_num
  have hz2 : (zeta3 ^ 2).re = -(1 / 2) := by
    rw [zeta3_sq]
    simp [Complex.sub_re, Complex.mul_re]
    norm_num
  fin_cases j <;> simp [c3Real, fourier3, hz, hz2]

theorem c3Imag_eq (j : Fin 3) : c3Imag j = (fourier3 1 j).im := by
  have hz : zeta3.im = Real.sqrt 3 / 2 := by
    simp [zeta3, Complex.add_im, Complex.mul_im]
  have hz2 : (zeta3 ^ 2).im = -(Real.sqrt 3 / 2) := by
    rw [zeta3_sq]
    simp [Complex.sub_im, Complex.mul_im]
    ring
  fin_cases j <;> simp [c3Imag, fourier3, hz, hz2]

/-- The conjugate character `χ₂ = (1, ζ², ζ)` has the same real part. -/
theorem c3_conj_re (j : Fin 3) : (fourier3 2 j).re = c3Real j := by
  have h := fourier3_conj_row j
  have : (fourier3 2 j).re = ((starRingEnd ℂ) (fourier3 1 j)).re := by rw [h]
  rw [this, Complex.conj_re, c3Real_eq j]

/-- The conjugate character `χ₂ = (1, ζ², ζ)` has the opposite imaginary part:
it spans the same real plane with the opposite orientation. -/
theorem c3_conj_im (j : Fin 3) : (fourier3 2 j).im = -c3Imag j := by
  have h := fourier3_conj_row j
  have : (fourier3 2 j).im = ((starRingEnd ℂ) (fourier3 1 j)).im := by rw [h]
  rw [this, Complex.conj_im, c3Imag_eq j]

/-! ### The transverse plane is nondegenerate -/

theorem c3Real_dot_const : c3Real ⬝ᵥ c3Const = 0 := by
  simp [c3Real, c3Const, dotProduct, Fin.sum_univ_three]
  norm_num

theorem c3Imag_dot_const : c3Imag ⬝ᵥ c3Const = 0 := by
  simp [c3Imag, c3Const, dotProduct, Fin.sum_univ_three]

theorem c3Real_normSq : c3Real ⬝ᵥ c3Real = 3 / 2 := by
  simp [c3Real, dotProduct, Fin.sum_univ_three]
  norm_num

theorem c3Imag_normSq : c3Imag ⬝ᵥ c3Imag = 3 / 2 := by
  have h : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  simp [c3Imag, dotProduct, Fin.sum_univ_three]
  nlinarith [h]

theorem c3_dot : c3Real ⬝ᵥ c3Imag = 0 := by
  simp [c3Real, c3Imag, dotProduct, Fin.sum_univ_three]

/-- **The realified conjugate phase pair spans a genuine transverse plane**: its
Gram defect (squared area) is `9/4`. -/
theorem c3_gramDefect : gramDefect c3Real c3Imag = 9 / 4 := by
  rw [gramDefect, c3Real_normSq, c3Imag_normSq, c3_dot]
  norm_num

/-- Hence the two phase labels are not two names for one line. -/
theorem c3_gramDefect_pos : 0 < gramDefect c3Real c3Imag := by
  rw [c3_gramDefect]; norm_num

end RiemannAnalytic
