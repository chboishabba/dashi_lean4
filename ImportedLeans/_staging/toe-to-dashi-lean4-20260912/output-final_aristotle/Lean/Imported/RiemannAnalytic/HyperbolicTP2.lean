/-
# Strict total positivity of order two for the hyperbolic kernels

This module proves, at literal strength and with no auxiliary hypotheses, the
two atomic inequalities that the zero-side (parity minor) programme needs:

* `sinh_strictTP2` : for `0 < a < p` and `0 < u < v`,
  `sinh (p*u) * sinh (a*v) < sinh (p*v) * sinh (a*u)`;
* `cosh_strictTP2` : for `0 < a < p` and `0 < u < v`,
  `cosh (p*u) * cosh (a*v) < cosh (p*v) * cosh (a*u)`.

Equivalently, the kernels `K(y,u) = sinh (y*u)` and `K(y,u) = cosh (y*u)` are
strictly `TP₂` on the open positive quadrant: every `2 × 2` minor with strictly
increasing row and column indices is strictly positive.

The odd (`sinh`) sector is the substantive one.  It is obtained from the chain

  `sinh (2x) > 2x`  ⟹  `x ↦ x * coth x` strictly increasing on `(0,∞)`
                    ⟹  `u ↦ sinh (p*u) / sinh (a*u)` strictly increasing
                    ⟹  strict `TP₂`.

The first step is `self_lt_sinh_mul_cosh` (from `Real.self_lt_sinh_iff` and
`Real.sinh_two_mul`); the two monotonicity steps are genuine derivative
arguments (`strictMonoOn_of_deriv_pos`), with

  `(x * coth x)' = (sinh x * cosh x - x) / sinh x ^ 2`.

The even (`cosh`) sector needs no calculus at all: the product-to-sum identity
`2 cosh X cosh Y = cosh (X+Y) + cosh (X-Y)` reduces it to the two ordered
comparisons `p*u + a*v < p*v + a*u` (i.e. `(p-a)(v-u) > 0`) and
`(p*u - a*v)^2 < (p*v - a*u)^2` (i.e. `(p^2-a^2)(v^2-u^2) > 0`), together with
the fact that `cosh` is strictly increasing in `|·|`.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib

open Real Set

namespace RiemannAnalytic
namespace HyperbolicTP2

/-! ## The atomic inequality `sinh (2x) > 2x` in product form -/

/-- `x < sinh x * cosh x` for `x > 0`; equivalently `sinh (2x) > 2x`. -/
theorem self_lt_sinh_mul_cosh {x : ℝ} (hx : 0 < x) : x < Real.sinh x * Real.cosh x := by
  have h : 2 * x < Real.sinh (2 * x) := Real.self_lt_sinh_iff.2 (by linarith)
  rw [Real.sinh_two_mul] at h
  linarith

/-! ## `x ↦ x * coth x` is strictly increasing on `(0,∞)` -/

/-- The scalar function `G x = x * coth x`, written without `coth` so that the
derivative computation stays inside the `sinh`/`cosh` API. -/
noncomputable def xcoth (x : ℝ) : ℝ := x * Real.cosh x / Real.sinh x

theorem hasDerivAt_xcoth {x : ℝ} (hx : 0 < x) :
    HasDerivAt xcoth ((Real.sinh x * Real.cosh x - x) / (Real.sinh x) ^ 2) x := by
  have hs : Real.sinh x ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 hx)
  have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
      (1 * Real.cosh x + x * Real.sinh x) x := (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
  have h3 := h1.div (Real.hasDerivAt_sinh x) hs
  have key : ((1 * Real.cosh x + x * Real.sinh x) * Real.sinh x - x * Real.cosh x * Real.cosh x)
      / (Real.sinh x) ^ 2 = (Real.sinh x * Real.cosh x - x) / (Real.sinh x) ^ 2 := by
    have h := Real.cosh_sq_sub_sinh_sq x
    congr 1
    nlinarith [h]
  rw [key] at h3
  exact h3

theorem strictMonoOn_xcoth : StrictMonoOn xcoth (Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact ((hasDerivAt_xcoth (mem_Ioi.1 hx)).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(hasDerivAt_xcoth hx).deriv]
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
    exact div_pos (by linarith [self_lt_sinh_mul_cosh hx]) (by positivity)

/-- The logarithmic-derivative inequality `p * coth (p*t) > a * coth (a*t)` in
cleared form. -/
theorem crossDeriv_pos {a p t : ℝ} (ha : 0 < a) (hap : a < p) (ht : 0 < t) :
    a * Real.cosh (a * t) * Real.sinh (p * t) < p * Real.cosh (p * t) * Real.sinh (a * t) := by
  have hat : 0 < a * t := mul_pos ha ht
  have hpt : 0 < p * t := mul_pos (ha.trans hap) ht
  have h := strictMonoOn_xcoth (mem_Ioi.2 hat) (mem_Ioi.2 hpt) (by nlinarith)
  have hsa : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.2 hat
  have hsp : 0 < Real.sinh (p * t) := Real.sinh_pos_iff.2 hpt
  rw [xcoth, xcoth, div_lt_div_iff₀ hsa hsp] at h
  nlinarith [h]

/-! ## The odd sector: strict `TP₂` for `sinh` -/

/-- The ratio `R_{a,p}(t) = sinh (p*t) / sinh (a*t)`. -/
noncomputable def sinhRatio (a p t : ℝ) : ℝ := Real.sinh (p * t) / Real.sinh (a * t)

theorem strictMonoOn_sinhRatio {a p : ℝ} (ha : 0 < a) (hap : a < p) :
    StrictMonoOn (sinhRatio a p) (Ioi (0 : ℝ)) := by
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (sinhRatio a p)
      ((Real.cosh (p * t) * p * Real.sinh (a * t)
        - Real.sinh (p * t) * (Real.cosh (a * t) * a)) / (Real.sinh (a * t)) ^ 2) t := by
    intro t ht
    have hsa : Real.sinh (a * t) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 (mul_pos ha ht))
    have hp : HasDerivAt (fun s : ℝ => p * s) p t := by simpa using (hasDerivAt_id t).const_mul p
    have haa : HasDerivAt (fun s : ℝ => a * s) a t := by simpa using (hasDerivAt_id t).const_mul a
    exact hp.sinh.div haa.sinh hsa
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact ((hderiv x (mem_Ioi.1 hx)).continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Ioi, mem_Ioi] at ht
    rw [(hderiv t ht).deriv]
    have hcross := crossDeriv_pos ha hap ht
    have hsa : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.2 (mul_pos ha ht)
    exact div_pos (by nlinarith) (by positivity)

/-- **Strict `TP₂` for the `sinh` kernel.**  For `0 < a < p` and `0 < u < v`,
`det ![![sinh (a*u), sinh (a*v)], ![sinh (p*u), sinh (p*v)]] > 0`. -/
theorem sinh_strictTP2 {a p u v : ℝ} (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.sinh (p * u) * Real.sinh (a * v) < Real.sinh (p * v) * Real.sinh (a * u) := by
  have h := strictMonoOn_sinhRatio ha hap (mem_Ioi.2 hu) (mem_Ioi.2 (hu.trans huv)) huv
  have hsau : 0 < Real.sinh (a * u) := Real.sinh_pos_iff.2 (mul_pos ha hu)
  have hsav : 0 < Real.sinh (a * v) := Real.sinh_pos_iff.2 (mul_pos ha (hu.trans huv))
  rw [sinhRatio, sinhRatio, div_lt_div_iff₀ hsau hsav] at h
  linarith

/-! ## The even sector: strict `TP₂` for `cosh`, with no calculus -/

/-- **Strict `TP₂` for the `cosh` kernel.**  For `0 < a < p` and `0 < u < v`,
`det ![![cosh (a*u), cosh (a*v)], ![cosh (p*u), cosh (p*v)]] > 0`. -/
theorem cosh_strictTP2 {a p u v : ℝ} (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.cosh (p * u) * Real.cosh (a * v) < Real.cosh (p * v) * Real.cosh (a * u) := by
  have hp : 0 < p := ha.trans hap
  have hv : 0 < v := hu.trans huv
  have e1 : ∀ X Y : ℝ, 2 * (Real.cosh X * Real.cosh Y)
      = Real.cosh (X + Y) + Real.cosh (X - Y) := by
    intro X Y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have h1 : Real.cosh (p * u + a * v) < Real.cosh (p * v + a * u) := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    nlinarith
  have h2 : Real.cosh (p * u - a * v) < Real.cosh (p * v - a * u) := by
    rw [Real.cosh_lt_cosh]
    refine sq_lt_sq.mp ?_
    nlinarith [mul_pos (show (0:ℝ) < p ^ 2 - a ^ 2 by nlinarith)
      (show (0:ℝ) < v ^ 2 - u ^ 2 by nlinarith)]
  have E1 := e1 (p * u) (a * v)
  have E2 := e1 (p * v) (a * u)
  linarith

end HyperbolicTP2
end RiemannAnalytic
