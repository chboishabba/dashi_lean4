/-
# Row C (temporal half) — the covariance-corrected curvature debt

The temporal half of Row C asks for a *cutoff-uniform* bound on the accumulated
negative curvature debt of the stochastic (Heat/Doob) relaxation.  A tempting
shortcut is to identify the dynamical second variation with the static
(RG-differentiated) Hessian.  That identification is **false in general**: for a
tilted family `V_t = −log H_t(e^{−V})` the second derivative of the logarithm
produces, besides the conditional expectation of the static Hessian, a
*covariance of gradients* term.  This file keeps that term and shows what is
still true.

* `wexp`, `wcov`, `wvar` — expectation, covariance and variance for a finite
  weight; `wcov_centered` is the centred form and `wvar_nonneg` its positivity.
* `abs_wcov_le_sqrt` — the covariance is controlled by the two variances,
  `|Cov(f,g)| ≤ √Var f·√Var g`.  This is the step that converts a first-gradient
  (Cauchy) shell estimate into a covariance shell estimate: no separate
  covariance decay theorem is needed once the gradient fluctuations are
  controlled.
* `curvature_shell_of_split` — the honest temporal seam: if the debt splits as
  `η_n ≤ H_n + Cov_n` with the static shell `H_n ≤ A_H·2⁻ⁿ` (which is what the
  RG differentiated-locality estimate gives) and a covariance shell
  `Cov_n ≤ A_cov·2⁻ⁿ`, then `η_n ≤ (A_H+A_cov)·2⁻ⁿ`.
* `curvature_shell_envelope` — `2⁻ⁿ ≤ (17/32)ⁿ`, so the combined shell fits
  inside the repository's existing `17/32` curvature envelope with no new
  summation theorem.
* `curvature_debt_total`, `curvature_debt_tsum` — the accumulated debt is
  bounded by `2(A_H+A_cov)`, uniformly in the cutoff.

**Honest status.**  The physics inputs are the two shell estimates (`hH`, `hCov`)
and, upstream of them, the identification of the finite-cutoff Heat/Doob density
with the RG-generated one.  Neither is proved here.  Row C is **not** closed by
this file and the frozen research count is unchanged.
-/
import Mathlib

namespace YangMills

open Finset

/-! ## 1. Finite covariance -/

section Covariance

variable {Ω : Type*} [Fintype Ω]

/-- Expectation against a finite weight. -/
def wexp (rho : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ w, rho w * f w

/-- Covariance against a finite weight. -/
def wcov (rho : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  wexp rho (fun w => f w * g w) - wexp rho f * wexp rho g

/-- Variance against a finite weight. -/
def wvar (rho : Ω → ℝ) (f : Ω → ℝ) : ℝ := wcov rho f f

/-- **Centred form of the covariance** for a normalised weight. -/
theorem wcov_centered {rho : Ω → ℝ} (hnorm : ∑ w, rho w = 1) (f g : Ω → ℝ) :
    wcov rho f g
      = ∑ w, rho w * ((f w - wexp rho f) * (g w - wexp rho g)) := by
  have hA : wexp rho f = ∑ w, rho w * f w := rfl
  have hB : wexp rho g = ∑ w, rho w * g w := rfl
  calc wcov rho f g
      = (∑ w, rho w * (f w * g w)) - (∑ w, rho w * f w) * (∑ w, rho w * g w) := rfl
    _ = ∑ w, (rho w * (f w * g w) - wexp rho g * (rho w * f w)
          - wexp rho f * (rho w * g w) + (wexp rho f * wexp rho g) * rho w) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, hA, hB]
        ring
    _ = ∑ w, rho w * ((f w - wexp rho f) * (g w - wexp rho g)) :=
        Finset.sum_congr rfl fun w _ => by ring

/-- Variance against a nonnegative normalised weight is nonnegative. -/
theorem wvar_nonneg {rho : Ω → ℝ} (hrho : ∀ w, 0 ≤ rho w) (hnorm : ∑ w, rho w = 1)
    (f : Ω → ℝ) : 0 ≤ wvar rho f := by
  rw [wvar, wcov_centered hnorm]
  refine Finset.sum_nonneg fun w _ => mul_nonneg (hrho w) ?_
  nlinarith [sq_nonneg (f w - wexp rho f)]

/-- **The covariance debt is controlled by the gradient fluctuations.**
`|Cov(f,g)| ≤ √Var f·√Var g`. -/
theorem abs_wcov_le_sqrt {rho : Ω → ℝ} (hrho : ∀ w, 0 ≤ rho w) (hnorm : ∑ w, rho w = 1)
    (f g : Ω → ℝ) :
    |wcov rho f g| ≤ Real.sqrt (wvar rho f) * Real.sqrt (wvar rho g) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun w => Real.sqrt (rho w) * (f w - wexp rho f))
    (fun w => Real.sqrt (rho w) * (g w - wexp rho g))
  have hFG : ∑ w, (Real.sqrt (rho w) * (f w - wexp rho f))
      * (Real.sqrt (rho w) * (g w - wexp rho g)) = wcov rho f g := by
    rw [wcov_centered hnorm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show (Real.sqrt (rho w) * (f w - wexp rho f))
        * (Real.sqrt (rho w) * (g w - wexp rho g))
        = (Real.sqrt (rho w) * Real.sqrt (rho w))
            * ((f w - wexp rho f) * (g w - wexp rho g)) from by ring,
      Real.mul_self_sqrt (hrho w)]
  have hFF : ∑ w, (Real.sqrt (rho w) * (f w - wexp rho f)) ^ 2 = wvar rho f := by
    rw [wvar, wcov_centered hnorm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show (Real.sqrt (rho w) * (f w - wexp rho f)) ^ 2
        = (Real.sqrt (rho w) * Real.sqrt (rho w))
            * ((f w - wexp rho f) * (f w - wexp rho f)) from by ring,
      Real.mul_self_sqrt (hrho w)]
  have hGG : ∑ w, (Real.sqrt (rho w) * (g w - wexp rho g)) ^ 2 = wvar rho g := by
    rw [wvar, wcov_centered hnorm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show (Real.sqrt (rho w) * (g w - wexp rho g)) ^ 2
        = (Real.sqrt (rho w) * Real.sqrt (rho w))
            * ((g w - wexp rho g) * (g w - wexp rho g)) from by ring,
      Real.mul_self_sqrt (hrho w)]
  simp only at hCS
  rw [hFG, hFF, hGG] at hCS
  have hvf : 0 ≤ wvar rho f := wvar_nonneg hrho hnorm f
  have h1 : |wcov rho f g| ≤ Real.sqrt (wvar rho f * wvar rho g) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS
  rwa [Real.sqrt_mul hvf] at h1

end Covariance

/-! ## 2. The curvature debt shells -/

/-- **The honest temporal seam.**  A static shell plus a covariance shell give a
combined geometric shell for the negative curvature debt. -/
theorem curvature_shell_of_split {eta H Cov : ℕ → ℝ} {AH ACov : ℝ}
    (hsplit : ∀ n, eta n ≤ H n + Cov n)
    (hH : ∀ n, H n ≤ AH * (1 / 2 : ℝ) ^ n)
    (hCov : ∀ n, Cov n ≤ ACov * (1 / 2 : ℝ) ^ n) (n : ℕ) :
    eta n ≤ (AH + ACov) * (1 / 2 : ℝ) ^ n := by
  have := hsplit n
  have h1 := hH n
  have h2 := hCov n
  nlinarith [this, h1, h2]

/-- **The combined shell fits the existing `17/32` envelope.** -/
theorem curvature_shell_envelope {eta H Cov : ℕ → ℝ} {AH ACov : ℝ}
    (hA : 0 ≤ AH + ACov)
    (hsplit : ∀ n, eta n ≤ H n + Cov n)
    (hH : ∀ n, H n ≤ AH * (1 / 2 : ℝ) ^ n)
    (hCov : ∀ n, Cov n ≤ ACov * (1 / 2 : ℝ) ^ n) (n : ℕ) :
    eta n ≤ (AH + ACov) * (17 / 32 : ℝ) ^ n := by
  refine (curvature_shell_of_split hsplit hH hCov n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hA
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- **Cutoff-uniform accumulated curvature debt.** -/
theorem curvature_debt_total {eta H Cov : ℕ → ℝ} {AH ACov : ℝ}
    (hA : 0 ≤ AH + ACov)
    (hsplit : ∀ n, eta n ≤ H n + Cov n)
    (hH : ∀ n, H n ≤ AH * (1 / 2 : ℝ) ^ n)
    (hCov : ∀ n, Cov n ≤ ACov * (1 / 2 : ℝ) ^ n) (N : ℕ) :
    ∑ n ∈ range N, eta n ≤ 2 * (AH + ACov) := by
  calc ∑ n ∈ range N, eta n
      ≤ ∑ n ∈ range N, (AH + ACov) * (1 / 2 : ℝ) ^ n :=
        Finset.sum_le_sum fun n _ => curvature_shell_of_split hsplit hH hCov n
    _ = (AH + ACov) * ∑ n ∈ range N, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ (AH + ACov) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hA
    _ = 2 * (AH + ACov) := by ring

/-- The total debt of a nonnegative shell family is finite, with the same
cutoff-independent bound. -/
theorem curvature_debt_tsum {eta H Cov : ℕ → ℝ} {AH ACov : ℝ}
    (hA : 0 ≤ AH + ACov) (heta : ∀ n, 0 ≤ eta n)
    (hsplit : ∀ n, eta n ≤ H n + Cov n)
    (hH : ∀ n, H n ≤ AH * (1 / 2 : ℝ) ^ n)
    (hCov : ∀ n, Cov n ≤ ACov * (1 / 2 : ℝ) ^ n) :
    ∑' n : ℕ, eta n ≤ 2 * (AH + ACov) :=
  Real.tsum_le_of_sum_range_le heta fun N =>
    curvature_debt_total hA hsplit hH hCov N

end YangMills
