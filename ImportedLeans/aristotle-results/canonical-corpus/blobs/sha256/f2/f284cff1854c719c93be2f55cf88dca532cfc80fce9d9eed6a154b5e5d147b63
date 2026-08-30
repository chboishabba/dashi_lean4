/-
# The leading response coefficient is a weighted covariance

`LiteralWeilTargetDefectLeadingCoefficient` isolated the radius-free coefficient of
the literal two-radius height defect,

    L(g, a) = 3/2 · ( N_a M_0 - M_a N_0 ),
    M_y = ∫ g(u) cosh(yu) du,   N_y = ∫ g(u) u² cosh(yu) du.

That expression is the covariance, against the taper `g`, of the two "observables"
`u ↦ u²` and `u ↦ cosh(au)`.  This module proves the symmetric double-integral form

    L(g, a) = 3/4 ∫∫ g(u) g(v) (u² - v²) (cosh(au) - cosh(av)) du dv,

and reads off two consequences.

* `targetLeadingCoeff_nonneg` — the integrand is pointwise nonnegative, because
  `cosh(a·)` is increasing in the modulus: `(u² - v²)` and `(cosh(au) - cosh(av))`
  always have the same sign.  So `L(g, a) ≥ 0` for every nonnegative taper.
* `targetLeadingCoeff_zero_height` — `L(g, 0) = 0`.

The covariance form is the natural place from which to attack the outstanding
obligation of the multi-taper Schur programme, namely the **response-ratio
separation** `L(g₀,a)/L(g₀,b) ≠ L(g₁,a)/L(g₁,b)` for the two window tapers
constructed in `LiteralWeilThreeWindowPoleNullSeed`: the covariance is supported on
the pairs `(u, v)` with `u` and `v` in *different* windows, so the two tapers weigh
the same nuisance/target pair through different modulus pairs.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

noncomputable section

open scoped Real
open MeasureTheory

namespace Zeta23Bridge
namespace LiteralWeilLeadingCoefficientCovariance

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

variable {g : ℝ → ℝ}

/-- The antisymmetric half of the covariance kernel. -/
def covKernelHalf (g : ℝ → ℝ) (a : ℝ) : ℝ → ℝ → ℝ := fun u v =>
  g u * g v * ((u ^ 2 - v ^ 2) * Real.cosh (a * u))

/-- The full (symmetric) covariance kernel. -/
def covKernel (g : ℝ → ℝ) (a : ℝ) : ℝ → ℝ → ℝ := fun u v =>
  g u * g v * ((u ^ 2 - v ^ 2) * (Real.cosh (a * u) - Real.cosh (a * v)))

theorem coshMoment_zero (g : ℝ → ℝ) : coshMoment g 0 = ∫ u : ℝ, g u := by
  unfold coshMoment
  simp

theorem sqCoshMoment_zero (g : ℝ → ℝ) : sqCoshMoment g 0 = ∫ u : ℝ, g u * u ^ 2 := by
  unfold sqCoshMoment
  simp

/-- The inner integral of the antisymmetric half. -/
theorem integral_covKernelHalf_inner (hg : Continuous g) (hgc : HasCompactSupport g) (a u : ℝ) :
    ∫ v : ℝ, covKernelHalf g a u v
      = (g u * Real.cosh (a * u)) * (u ^ 2 * coshMoment g 0)
        - (g u * Real.cosh (a * u)) * sqCoshMoment g 0 := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have h1 : Integrable (fun v : ℝ => (g u * Real.cosh (a * u)) * (u ^ 2 * g v)) :=
    (hgint.const_mul (u ^ 2)).const_mul _
  have h2 : Integrable (fun v : ℝ => (g u * Real.cosh (a * u)) * (g v * v ^ 2)) :=
    (taper_integrable hg hgc (by fun_prop)).const_mul _
  have hsplit : (fun v : ℝ => covKernelHalf g a u v)
      = fun v : ℝ => (g u * Real.cosh (a * u)) * (u ^ 2 * g v)
          - (g u * Real.cosh (a * u)) * (g v * v ^ 2) := by
    funext v
    unfold covKernelHalf
    ring
  rw [hsplit, integral_sub h1 h2, integral_const_mul, integral_const_mul, integral_const_mul,
    coshMoment_zero, sqCoshMoment_zero]

/-- The iterated integral of the antisymmetric half is exactly the covariance
`N_a M_0 - M_a N_0`. -/
theorem integral_covKernelHalf (hg : Continuous g) (hgc : HasCompactSupport g) (a : ℝ) :
    ∫ u : ℝ, ∫ v : ℝ, covKernelHalf g a u v
      = sqCoshMoment g a * coshMoment g 0 - coshMoment g a * sqCoshMoment g 0 := by
  have hinner : (fun u : ℝ => ∫ v : ℝ, covKernelHalf g a u v)
      = fun u : ℝ => coshMoment g 0 * (g u * (u ^ 2 * Real.cosh (a * u)))
          - sqCoshMoment g 0 * (g u * Real.cosh (a * u)) := by
    funext u
    rw [integral_covKernelHalf_inner hg hgc a u]
    ring
  have h1 : Integrable (fun u : ℝ => coshMoment g 0 * (g u * (u ^ 2 * Real.cosh (a * u)))) :=
    (taper_integrable hg hgc (by fun_prop)).const_mul _
  have h2 : Integrable (fun u : ℝ => sqCoshMoment g 0 * (g u * Real.cosh (a * u))) :=
    (taper_integrable hg hgc (by fun_prop)).const_mul _
  rw [hinner, integral_sub h1 h2, integral_const_mul, integral_const_mul]
  unfold sqCoshMoment coshMoment
  ring

/-- Each slice of the antisymmetric half is integrable. -/
theorem integrable_covKernelHalf_slice (hg : Continuous g) (hgc : HasCompactSupport g)
    (a u : ℝ) : Integrable (fun v : ℝ => covKernelHalf g a u v) := by
  have hrw : (fun v : ℝ => covKernelHalf g a u v)
      = fun v : ℝ => (g u * ((u ^ 2 - v ^ 2) * Real.cosh (a * u))) * g v := by
    funext v
    unfold covKernelHalf
    ring
  rw [hrw]
  have := taper_integrable hg hgc
    (h := fun v : ℝ => g u * ((u ^ 2 - v ^ 2) * Real.cosh (a * u))) (by fun_prop)
  simpa [mul_comm] using this

/-- Each transposed slice of the antisymmetric half is integrable. -/
theorem integrable_covKernelHalf_slice' (hg : Continuous g) (hgc : HasCompactSupport g)
    (a u : ℝ) : Integrable (fun v : ℝ => covKernelHalf g a v u) := by
  have hrw : (fun v : ℝ => covKernelHalf g a v u)
      = fun v : ℝ => g v * (g u * ((v ^ 2 - u ^ 2) * Real.cosh (a * v))) := by
    funext v
    unfold covKernelHalf
    ring
  rw [hrw]
  exact taper_integrable hg hgc (by fun_prop)

/-! ## Symmetrisation -/

theorem continuous_uncurry_covKernelHalf (hg : Continuous g) (a : ℝ) :
    Continuous (Function.uncurry (covKernelHalf g a)) := by
  unfold covKernelHalf Function.uncurry
  fun_prop

theorem hasCompactSupport_uncurry_covKernelHalf (hgc : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport (Function.uncurry (covKernelHalf g a)) := by
  refine HasCompactSupport.intro (K := tsupport g ×ˢ tsupport g) (hgc.prod hgc) ?_
  intro z hz
  have hcases : z.1 ∉ tsupport g ∨ z.2 ∉ tsupport g := by
    by_contra hcon
    push_neg at hcon
    exact hz (Set.mem_prod.mpr ⟨hcon.1, hcon.2⟩)
  have hzero : g z.1 = 0 ∨ g z.2 = 0 := by
    rcases hcases with h | h
    · exact Or.inl (image_eq_zero_of_notMem_tsupport h)
    · exact Or.inr (image_eq_zero_of_notMem_tsupport h)
  show covKernelHalf g a z.1 z.2 = 0
  unfold covKernelHalf
  rcases hzero with h | h <;> rw [h] <;> ring

theorem integrable_uncurry_covKernelHalf (hg : Continuous g) (hgc : HasCompactSupport g) (a : ℝ) :
    Integrable (Function.uncurry (covKernelHalf g a)) :=
  (continuous_uncurry_covKernelHalf hg a).integrable_of_hasCompactSupport
    (hasCompactSupport_uncurry_covKernelHalf hgc a)

/-- **The covariance form of the leading coefficient.** -/
theorem targetLeadingCoeff_eq_covariance (hg : Continuous g) (hgc : HasCompactSupport g) (a : ℝ) :
    targetLeadingCoeff g a = 3 / 4 * ∫ u : ℝ, ∫ v : ℝ, covKernel g a u v := by
  have hswap : ∫ u : ℝ, ∫ v : ℝ, covKernelHalf g a v u
      = ∫ u : ℝ, ∫ v : ℝ, covKernelHalf g a u v :=
    (integral_integral_swap (integrable_uncurry_covKernelHalf hg hgc a)).symm
  -- the two halves
  have hkernel : (fun u : ℝ => ∫ v : ℝ, covKernel g a u v)
      = fun u : ℝ => (∫ v : ℝ, covKernelHalf g a u v) + ∫ v : ℝ, covKernelHalf g a v u := by
    funext u
    have hsplit : (fun v : ℝ => covKernel g a u v)
        = fun v : ℝ => covKernelHalf g a u v + covKernelHalf g a v u := by
      funext v
      unfold covKernel covKernelHalf
      ring
    rw [hsplit]
    refine integral_add ?_ ?_
    · exact integrable_covKernelHalf_slice hg hgc a u
    · exact integrable_covKernelHalf_slice' hg hgc a u
  have hsum : ∫ u : ℝ, ∫ v : ℝ, covKernel g a u v
      = 2 * ∫ u : ℝ, ∫ v : ℝ, covKernelHalf g a u v := by
    rw [hkernel]
    have hA : Integrable (fun u : ℝ => ∫ v : ℝ, covKernelHalf g a u v) :=
      (integrable_uncurry_covKernelHalf hg hgc a).integral_prod_left
    have hB : Integrable (fun u : ℝ => ∫ v : ℝ, covKernelHalf g a v u) := by
      have hswapint : Integrable (Function.uncurry fun x y => covKernelHalf g a y x) :=
        (integrable_uncurry_covKernelHalf hg hgc a).swap
      exact hswapint.integral_prod_left
    rw [integral_add hA hB, hswap]
    ring
  rw [hsum, integral_covKernelHalf hg hgc a]
  unfold targetLeadingCoeff
  ring

/-! ## Consequences -/

theorem cosh_mono_sq (a : ℝ) {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) :
    Real.cosh (a * x) ≤ Real.cosh (a * y) := by
  have habs : |x| ≤ |y| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have hmul : |a * x| ≤ |a * y| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg a)
  exact Real.cosh_le_cosh.mpr hmul

/-- The covariance integrand is pointwise nonnegative for a nonnegative taper:
`u² - v²` and `cosh(au) - cosh(av)` always have the same sign. -/
theorem covKernel_nonneg (hnn : ∀ u, 0 ≤ g u) (a u v : ℝ) : 0 ≤ covKernel g a u v := by
  have hgg : 0 ≤ g u * g v := mul_nonneg (hnn u) (hnn v)
  have hsame : 0 ≤ (u ^ 2 - v ^ 2) * (Real.cosh (a * u) - Real.cosh (a * v)) := by
    rcases le_total (v ^ 2) (u ^ 2) with h | h
    · have hcosh := cosh_mono_sq a h
      exact mul_nonneg (by linarith) (by linarith)
    · have hcosh := cosh_mono_sq a h
      nlinarith [h, hcosh]
  unfold covKernel
  exact mul_nonneg hgg hsame

/-- Hence the leading response coefficient of a nonnegative taper is nonnegative. -/
theorem targetLeadingCoeff_nonneg (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) (a : ℝ) : 0 ≤ targetLeadingCoeff g a := by
  rw [targetLeadingCoeff_eq_covariance hg hgc a]
  have hinner : ∀ u : ℝ, 0 ≤ ∫ v : ℝ, covKernel g a u v := by
    intro u
    exact integral_nonneg fun v => covKernel_nonneg hnn a u v
  have hnn2 : 0 ≤ ∫ u : ℝ, ∫ v : ℝ, covKernel g a u v := integral_nonneg hinner
  linarith

/-- The covariance kernel vanishes identically at height zero. -/
theorem covKernel_zero_height (g : ℝ → ℝ) (u v : ℝ) : covKernel g 0 u v = 0 := by
  unfold covKernel
  simp

theorem targetLeadingCoeff_zero_height (hg : Continuous g) (hgc : HasCompactSupport g) :
    targetLeadingCoeff g 0 = 0 := by
  rw [targetLeadingCoeff_eq_covariance hg hgc 0]
  simp [covKernel_zero_height]


/-! ## The polarised (bilinear) covariance form

Writing the covariance out in moments makes the *bilinear* structure explicit: the
leading coefficient of a sum of two window bumps splits into the two self-terms and a
cross term, and it is the cross term that carries the window geometry. -/

/-- The polarisation of the leading coefficient: the symmetric bilinear form whose
diagonal is `targetLeadingCoeff`. -/
def covForm (g h : ℝ → ℝ) (a : ℝ) : ℝ :=
  3 / 4 * (sqCoshMoment g a * coshMoment h 0 - coshMoment g a * sqCoshMoment h 0
    - sqCoshMoment g 0 * coshMoment h a + coshMoment g 0 * sqCoshMoment h a)

theorem covForm_self (g : ℝ → ℝ) (a : ℝ) : covForm g g a = targetLeadingCoeff g a := by
  unfold covForm targetLeadingCoeff
  ring

theorem covForm_symm (g h : ℝ → ℝ) (a : ℝ) : covForm g h a = covForm h g a := by
  unfold covForm
  ring

theorem coshMoment_add_smul {p q : ℝ → ℝ} (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq : Continuous q) (hqc : HasCompactSupport q) (lam a : ℝ) :
    coshMoment (fun u => p u + lam * q u) a = coshMoment p a + lam * coshMoment q a := by
  unfold coshMoment
  have h1 : Integrable (fun u : ℝ => p u * Real.cosh (a * u)) :=
    taper_integrable hp hpc (by fun_prop)
  have h2 : Integrable (fun u : ℝ => lam * (q u * Real.cosh (a * u))) :=
    (taper_integrable hq hqc (by fun_prop)).const_mul lam
  rw [show (fun u : ℝ => (p u + lam * q u) * Real.cosh (a * u))
      = fun u : ℝ => p u * Real.cosh (a * u) + lam * (q u * Real.cosh (a * u)) by
    funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

theorem sqCoshMoment_add_smul {p q : ℝ → ℝ} (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq : Continuous q) (hqc : HasCompactSupport q) (lam a : ℝ) :
    sqCoshMoment (fun u => p u + lam * q u) a = sqCoshMoment p a + lam * sqCoshMoment q a := by
  unfold sqCoshMoment
  have h1 : Integrable (fun u : ℝ => p u * (u ^ 2 * Real.cosh (a * u))) :=
    taper_integrable hp hpc (by fun_prop)
  have h2 : Integrable (fun u : ℝ => lam * (q u * (u ^ 2 * Real.cosh (a * u)))) :=
    (taper_integrable hq hqc (by fun_prop)).const_mul lam
  rw [show (fun u : ℝ => (p u + lam * q u) * (u ^ 2 * Real.cosh (a * u)))
      = fun u : ℝ => p u * (u ^ 2 * Real.cosh (a * u))
        + lam * (q u * (u ^ 2 * Real.cosh (a * u))) by funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

theorem covForm_add_smul_left {p q h : ℝ → ℝ} (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq : Continuous q) (hqc : HasCompactSupport q) (lam a : ℝ) :
    covForm (fun u => p u + lam * q u) h a = covForm p h a + lam * covForm q h a := by
  unfold covForm
  rw [coshMoment_add_smul hp hpc hq hqc, coshMoment_add_smul hp hpc hq hqc,
    sqCoshMoment_add_smul hp hpc hq hqc, sqCoshMoment_add_smul hp hpc hq hqc]
  ring

/-- **The two-window decomposition of the leading response coefficient.**  For a taper
`p + λ q` built from a shared negative-response window `p` and a positive-response
window `q`, the leading coefficient is the sum of the two self-responses and twice the
cross response.  In the three-window seed the two tapers share `p` and differ only in
`q`, so the whole response-ratio separation is carried by the cross terms. -/
theorem targetLeadingCoeff_add_smul {p q : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hq : Continuous q) (hqc : HasCompactSupport q) (lam a : ℝ) :
    targetLeadingCoeff (fun u => p u + lam * q u) a
      = targetLeadingCoeff p a + 2 * lam * covForm p q a + lam ^ 2 * targetLeadingCoeff q a := by
  rw [← covForm_self, covForm_add_smul_left hp hpc hq hqc]
  have hswap : ∀ f : ℝ → ℝ, covForm f (fun u => p u + lam * q u) a
      = covForm p f a + lam * covForm q f a := by
    intro f
    rw [covForm_symm, covForm_add_smul_left hp hpc hq hqc]
  rw [hswap p, hswap q, covForm_self, covForm_self, covForm_symm q p]
  ring

end LiteralWeilLeadingCoefficientCovariance
end Zeta23Bridge
