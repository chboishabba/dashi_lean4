/-
# Finite-radius transfer of the strict odd moment determinant

`StrictKernelMomentRatio.lean` closes the *continuum* odd obligation with a
strict margin,

  `Δ_odd = N 1 a * N 3 p − N 3 a * N 1 p > 0`   for `0 < a < p`.

This module transports that margin to the **actual finite-radius odd response**

  `B_y(r) = ∫₀ᴸ φ(u) sinh (y u) sin (r u) du`,

which is the odd (sine) channel of the two-height observation at radius `r`.

The chain is:

* `abs_sin_sub_taylor3` : `|sin x − (x − x³/6)| ≤ x⁵/120` for `x ≥ 0`, proved
  from scratch by the four-step derivative chain
  `sin t ≤ t → 1 − t²/2 ≤ cos t → t − t³/6 ≤ sin t → cos t ≤ 1 − t²/2 + t⁴/24
   → sin t ≤ t − t³/6 + t⁵/120`;

* `oddResponse_sub_trunc_abs_le` : the entrywise remainder bound
  `|B_y(r) − (r N 1 y − (r³/6) N 3 y)| ≤ (r⁵/120) N 5 y`;

* `oddTruncatedDeterminant_eq` : the **exact** cancellation identity
  `T_a(r) T_p(2r) − T_a(2r) T_p(r) = − r⁴ Δ_odd`
  (the linear×linear and cubic×cubic contributions cancel identically; only the
  linear/cubic cross terms survive), and
  `oddDeterminant_sub_truncated_eq`, the exact determinant-level remainder
  identity — the analysis is never done entrywise on four independent entries;

* `oddMoment_le_of_support` : `N 3 y ≤ L² N 1 y` and `N 5 y ≤ L⁴ N 1 y`, the
  compact-support moment domination (an honest `integral_mono`, not an
  assumption);

* `oddFiniteRadiusDeterminant_neg` : the sign-preservation gate.  For
  `0 < r`, `r L ≤ 1` and the *relative* smallness condition
  `r² L⁴ N 1 a * N 1 p < Δ_odd`, the finite-radius minor
  `D_R = B_a(r) B_p(2r) − B_a(2r) B_p(r)` is strictly negative;

* `oddFiniteRadiusDeterminant_neg_of_smallRadius` : combined with the continuum
  theorem this gives, for any admissible taper and any `0 < a < p`, an explicit
  threshold below which the actual finite-radius odd minor has a strict sign.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.StrictKernelMomentRatio

open MeasureTheory Set

namespace RiemannAnalytic
namespace OddTaylorDeterminant

open StrictKernelMomentRatio

/-! ## The fifth-order sine remainder, from scratch -/

/-- If `f 0 = 0` and `f' ≥ 0` on `[0,∞)` then `f ≥ 0` on `[0,∞)`. -/
theorem nonneg_of_deriv_nonneg_Ici {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici, mem_Ioi] at hy
      rw [(hf y).deriv]
      exact hd y hy.le
  have h := hmono Set.self_mem_Ici (mem_Ici.2 hx) hx
  rw [h0] at h
  exact h

theorem sin_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun t => Real.sin t - t + t ^ 3 / 6) (f' := fun t => Real.cos t - 1 + t ^ 2 / 2)
    (by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => Real.sin t - t + t ^ 3 / 6)
          (Real.cos t - 1 + (3 * t ^ 2) / 6) t := by
        simpa using ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).add
          ((hasDerivAt_pow 3 t).div_const 6)
      convert h1 using 1; ring)
    (by norm_num) (fun t _ => by nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)])
    x hx
  linarith

theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
    (f' := fun t => -t + t ^ 3 / 6 + Real.sin t)
    (by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
          (0 - (2 * t ^ 1) / 2 + (4 * t ^ 3) / 24 - (-Real.sin t)) t := by
        simpa using (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
      convert h1 using 1; ring)
    (by norm_num) (fun t ht => by nlinarith [sin_ge_sub_cube ht])
    x hx
  linarith

theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
    (by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
          (1 - (3 * t ^ 2) / 6 + (5 * t ^ 4) / 120 - Real.cos t) t := by
        simpa using (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
      convert h1 using 1; ring)
    (by norm_num) (fun t ht => by nlinarith [cos_le_quartic ht])
    x hx
  linarith

/-- The fifth-order sine remainder bound on the positive axis. -/
theorem abs_sin_sub_taylor3 {x : ℝ} (hx : 0 ≤ x) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ x ^ 5 / 120 := by
  rw [abs_le]
  exact ⟨by nlinarith [sin_ge_sub_cube hx, pow_nonneg hx 5], by nlinarith [sin_le_quintic hx]⟩

/-! ## The finite-radius odd response and its truncation -/

/-- The odd (sine) response of the taper at height `y` and observation radius `r`. -/
noncomputable def oddResponse (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) L, φ u * Real.sinh (y * u) * Real.sin (r * u)

/-- The cubic truncation `T_y(r) = r N 1 y − (r³/6) N 3 y`. -/
noncomputable def oddTrunc (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  r * oddMoment L φ 1 y - r ^ 3 / 6 * oddMoment L φ 3 y

section Taper

variable {L Cφ y r : ℝ} {φ : ℝ → ℝ}

/-- Integrability of the moment integrands. -/
theorem integrable_moment (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (k : ℕ) :
    Integrable (fun u => u ^ k * φ u * Real.sinh (y * u)) (volume.restrict (Ioc (0 : ℝ) L)) := by
  refine integrable_restrict_Ioc_of_bounded
    ((measurable_id.pow_const k |>.mul hφmeas).mul
      (Real.measurable_sinh.comp (measurable_const.mul measurable_id)))
    (C := L ^ k * |Cφ| * Real.sinh (y * L)) ?_
  intro u hu
  rw [abs_mul, abs_mul]
  have h1 : |u ^ k| ≤ L ^ k := by
    rw [abs_pow, abs_of_pos hu.1]
    exact pow_le_pow_left₀ hu.1.le hu.2 k
  have h2 : |φ u| ≤ |Cφ| := (hφb u hu).trans (le_abs_self _)
  have h3 : |Real.sinh (y * u)| ≤ Real.sinh (y * L) := by
    rw [abs_of_pos (Real.sinh_pos_iff.2 (mul_pos hy hu.1))]
    exact Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hu.2 hy.le)
  have hs : 0 ≤ Real.sinh (y * L) := (Real.sinh_pos_iff.2 (mul_pos hy hL)).le
  exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _)
    (by positivity)

theorem integrable_response (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) :
    Integrable (fun u => φ u * Real.sinh (y * u) * Real.sin (r * u))
      (volume.restrict (Ioc (0 : ℝ) L)) := by
  refine integrable_restrict_Ioc_of_bounded
    ((hφmeas.mul (Real.measurable_sinh.comp (measurable_const.mul measurable_id))).mul
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)))
    (C := |Cφ| * Real.sinh (y * L) * 1) ?_
  intro u hu
  rw [abs_mul, abs_mul]
  have h2 : |φ u| ≤ |Cφ| := (hφb u hu).trans (le_abs_self _)
  have h3 : |Real.sinh (y * u)| ≤ Real.sinh (y * L) := by
    rw [abs_of_pos (Real.sinh_pos_iff.2 (mul_pos hy hu.1))]
    exact Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hu.2 hy.le)
  have hs : 0 ≤ Real.sinh (y * L) := (Real.sinh_pos_iff.2 (mul_pos hy hL)).le
  exact mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) (abs_nonneg _))
    (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)

/-- **Entrywise remainder bound.**  The odd response differs from its cubic
truncation by at most `(r⁵/120) N 5 y`. -/
theorem oddResponse_sub_trunc_abs_le (hφmeas : Measurable φ)
    (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (hr : 0 ≤ r) :
    |oddResponse L φ y r - oddTrunc L φ y r| ≤ r ^ 5 / 120 * oddMoment L φ 5 y := by
  have hI1 := integrable_response (r := r) hφmeas hφb hL hy
  have hM1 := integrable_moment hφmeas hφb hL hy 1
  have hM3 := integrable_moment hφmeas hφb hL hy 3
  have hM5 := integrable_moment hφmeas hφb hL hy 5
  have hG : Integrable (fun u => r * (u ^ 1 * φ u * Real.sinh (y * u))
      - r ^ 3 / 6 * (u ^ 3 * φ u * Real.sinh (y * u))) (volume.restrict (Ioc (0 : ℝ) L)) := by
    simpa using (hM1.const_mul r).sub (hM3.const_mul (r ^ 3 / 6))
  have hdiff : oddResponse L φ y r - oddTrunc L φ y r
      = ∫ u in Ioc (0 : ℝ) L,
          φ u * Real.sinh (y * u) * (Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6)) := by
    calc oddResponse L φ y r - oddTrunc L φ y r
        = (∫ u in Ioc (0 : ℝ) L, φ u * Real.sinh (y * u) * Real.sin (r * u))
          - ((∫ u in Ioc (0 : ℝ) L, r * (u ^ 1 * φ u * Real.sinh (y * u)))
            - (∫ u in Ioc (0 : ℝ) L, r ^ 3 / 6 * (u ^ 3 * φ u * Real.sinh (y * u)))) := by
          rw [oddResponse, oddTrunc, oddMoment, oddMoment, integral_const_mul, integral_const_mul]
      _ = ∫ u in Ioc (0 : ℝ) L, (φ u * Real.sinh (y * u) * Real.sin (r * u)
            - (r * (u ^ 1 * φ u * Real.sinh (y * u))
              - r ^ 3 / 6 * (u ^ 3 * φ u * Real.sinh (y * u)))) := by
          rw [integral_sub hI1 hG, integral_sub (hM1.const_mul r) (hM3.const_mul (r ^ 3 / 6))]
      _ = ∫ u in Ioc (0 : ℝ) L,
            φ u * Real.sinh (y * u) * (Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6)) := by
          congr 1
          funext u
          ring
  rw [hdiff]
  have hbound : ∀ u ∈ Ioc (0 : ℝ) L,
      |φ u * Real.sinh (y * u) * (Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6))|
        ≤ r ^ 5 / 120 * (u ^ 5 * φ u * Real.sinh (y * u)) := by
    intro u hu
    have hφu := hφ0 u hu
    have hsu : 0 ≤ Real.sinh (y * u) := (Real.sinh_pos_iff.2 (mul_pos hy hu.1)).le
    have hru : 0 ≤ r * u := mul_nonneg hr hu.1.le
    have h := abs_sin_sub_taylor3 hru
    rw [abs_mul, abs_of_nonneg (mul_nonneg hφu hsu)]
    have : |Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6)| ≤ r ^ 5 / 120 * u ^ 5 := by
      refine h.trans (le_of_eq ?_)
      ring
    calc φ u * Real.sinh (y * u) * |Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6)|
        ≤ φ u * Real.sinh (y * u) * (r ^ 5 / 120 * u ^ 5) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hφu hsu)
      _ = r ^ 5 / 120 * (u ^ 5 * φ u * Real.sinh (y * u)) := by ring
  calc |∫ u in Ioc (0 : ℝ) L,
          φ u * Real.sinh (y * u) * (Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6))|
      ≤ ∫ u in Ioc (0 : ℝ) L,
          |φ u * Real.sinh (y * u) * (Real.sin (r * u) - (r * u - (r * u) ^ 3 / 6))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioc (0 : ℝ) L, r ^ 5 / 120 * (u ^ 5 * φ u * Real.sinh (y * u)) := by
        refine integral_mono_of_nonneg (by filter_upwards with u using abs_nonneg _)
          (hM5.const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu using hbound u hu
    _ = r ^ 5 / 120 * oddMoment L φ 5 y := by
        rw [integral_const_mul]; rfl

/-! ## Compact-support moment domination -/

/-- `N k y ≥ 0` for a nonnegative taper and positive height. -/
theorem oddMoment_nonneg (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u) (hy : 0 < y) (k : ℕ) :
    0 ≤ oddMoment L φ k y := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact mul_nonneg (mul_nonneg (pow_nonneg hu.1.le k) (hφ0 u hu))
    (Real.sinh_pos_iff.2 (mul_pos hy hu.1)).le

/-- **Support domination.**  On a taper supported in `(0,L]`, higher moments are
controlled by lower ones: `N (k+j) y ≤ L^j * N k y`. -/
theorem oddMoment_le_of_support (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (k j : ℕ) :
    oddMoment L φ (k + j) y ≤ L ^ j * oddMoment L φ k y := by
  have hMk := integrable_moment hφmeas hφb hL hy k
  have hMkj := integrable_moment hφmeas hφb hL hy (k + j)
  have : oddMoment L φ (k + j) y ≤ ∫ u in Ioc (0 : ℝ) L,
      L ^ j * (u ^ k * φ u * Real.sinh (y * u)) := by
    refine integral_mono_ae hMkj (hMk.const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    · have hφu := hφ0 u hu
      have hsu : 0 ≤ Real.sinh (y * u) := (Real.sinh_pos_iff.2 (mul_pos hy hu.1)).le
      have huj : u ^ j ≤ L ^ j := pow_le_pow_left₀ hu.1.le hu.2 j
      have : u ^ (k + j) * φ u * Real.sinh (y * u)
          = (u ^ k * φ u * Real.sinh (y * u)) * u ^ j := by rw [pow_add]; ring
      rw [this]
      have hnn : 0 ≤ u ^ k * φ u * Real.sinh (y * u) :=
        mul_nonneg (mul_nonneg (pow_nonneg hu.1.le k) hφu) hsu
      calc (u ^ k * φ u * Real.sinh (y * u)) * u ^ j
          ≤ (u ^ k * φ u * Real.sinh (y * u)) * L ^ j := mul_le_mul_of_nonneg_left huj hnn
        _ = L ^ j * (u ^ k * φ u * Real.sinh (y * u)) := by ring
  rw [integral_const_mul] at this
  exact this

end Taper

/-! ## Exact determinant algebra -/

/-- **Exact truncated determinant.**  At the radii `r` and `2r` the linear×linear
and cubic×cubic contributions cancel identically; the surviving signal is the
linear/cubic cross term, proportional to the continuum margin `Δ_odd`. -/
theorem oddTruncatedDeterminant_eq (L : ℝ) (φ : ℝ → ℝ) (a p r : ℝ) :
    oddTrunc L φ a r * oddTrunc L φ p (2 * r) - oddTrunc L φ a (2 * r) * oddTrunc L φ p r
      = -(r ^ 4 * (oddMoment L φ 1 a * oddMoment L φ 3 p
          - oddMoment L φ 3 a * oddMoment L φ 1 p)) := by
  simp only [oddTrunc]
  ring

/-- **Exact determinant-level remainder identity.**  The determinant error is a
combination of *determinant* cross terms, never four independent entrywise
approximations. -/
theorem oddDeterminant_sub_truncated_eq (Ba1 Ba2 Bp1 Bp2 Ta1 Ta2 Tp1 Tp2 : ℝ) :
    (Ba1 * Bp2 - Ba2 * Bp1) - (Ta1 * Tp2 - Ta2 * Tp1)
      = Ta1 * (Bp2 - Tp2) + (Ba1 - Ta1) * Tp2 + (Ba1 - Ta1) * (Bp2 - Tp2)
        - (Ta2 * (Bp1 - Tp1) + (Ba2 - Ta2) * Tp1 + (Ba2 - Ta2) * (Bp1 - Tp1)) := by
  ring

/-! ## The sign-preservation gate -/

/-- Abstract combination step: a determinant whose exact signal is `-S` and whose
determinant-level error is bounded by a total of at most `Z < S` is negative. -/
theorem det_sign_from_bounds {D S Z c1 c2 c3 c4 c5 c6 X1 X2 X3 X4 X5 X6 : ℝ}
    (hid : D = -S + (X1 + X2 + X3 - (X4 + X5 + X6)))
    (h1 : |X1| ≤ c1 * Z) (h2 : |X2| ≤ c2 * Z) (h3 : |X3| ≤ c3 * Z)
    (h4 : |X4| ≤ c4 * Z) (h5 : |X5| ≤ c5 * Z) (h6 : |X6| ≤ c6 * Z)
    (hc : c1 + c2 + c3 + c4 + c5 + c6 ≤ 1) (hZ0 : 0 ≤ Z) (hZS : Z < S) : D < 0 := by
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  have a4 := abs_le.1 h4
  have a5 := abs_le.1 h5
  have a6 := abs_le.1 h6
  have hsum : c1 * Z + c2 * Z + c3 * Z + c4 * Z + c5 * Z + c6 * Z ≤ Z := by
    calc c1 * Z + c2 * Z + c3 * Z + c4 * Z + c5 * Z + c6 * Z
        = (c1 + c2 + c3 + c4 + c5 + c6) * Z := by ring
      _ ≤ 1 * Z := mul_le_mul_of_nonneg_right hc hZ0
      _ = Z := one_mul _
  linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1, a6.2]

set_option maxHeartbeats 1000000 in
/-- **Relative-margin sign transfer.**  Purely quantitative core: given the
moment domination bounds, the entrywise fifth-order remainder bounds and the
*relative* smallness condition `r² L⁴ N₁(a) N₁(p) < Δ_odd`, the finite-radius
determinant is strictly negative.  The error is compared against the continuum
determinant margin, not against four independent entrywise bounds. -/
theorem sign_transfer {A1 A3 A5 P1 P3 P5 Ba1 Ba2 Bp1 Bp2 Ta1 Ta2 Tp1 Tp2 L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hrL : r * L ≤ 1)
    (hA1 : 0 ≤ A1) (hA3 : 0 ≤ A3) (hP1 : 0 ≤ P1) (hP3 : 0 ≤ P3)
    (hA3L : A3 ≤ L ^ 2 * A1) (hA5L : A5 ≤ L ^ 4 * A1)
    (hP3L : P3 ≤ L ^ 2 * P1) (hP5L : P5 ≤ L ^ 4 * P1)
    (hTa1 : Ta1 = r * A1 - r ^ 3 / 6 * A3) (hTa2 : Ta2 = 2 * r * A1 - (2 * r) ^ 3 / 6 * A3)
    (hTp1 : Tp1 = r * P1 - r ^ 3 / 6 * P3) (hTp2 : Tp2 = 2 * r * P1 - (2 * r) ^ 3 / 6 * P3)
    (hEa1 : |Ba1 - Ta1| ≤ r ^ 5 / 120 * A5) (hEa2 : |Ba2 - Ta2| ≤ (2 * r) ^ 5 / 120 * A5)
    (hEp1 : |Bp1 - Tp1| ≤ r ^ 5 / 120 * P5) (hEp2 : |Bp2 - Tp2| ≤ (2 * r) ^ 5 / 120 * P5)
    (hgap : r ^ 2 * L ^ 4 * (A1 * P1) < A1 * P3 - A3 * P1) :
    Ba1 * Bp2 - Ba2 * Bp1 < 0 := by
  have hrA1 : 0 ≤ r * A1 := mul_nonneg hr.le hA1
  have hrP1 : 0 ≤ r * P1 := mul_nonneg hr.le hP1
  have hrL0 : 0 < r * L := mul_pos hr hL
  have hsq : (r * L) ^ 2 ≤ 1 := pow_le_one₀ hrL0.le hrL
  have h4L : r ^ 4 * L ^ 4 ≤ 1 := by
    calc r ^ 4 * L ^ 4 = (r * L) ^ 4 := by ring
      _ ≤ 1 := pow_le_one₀ hrL0.le hrL
  have hkeya : r ^ 3 * A3 ≤ r * A1 := by
    calc r ^ 3 * A3 ≤ r ^ 3 * (L ^ 2 * A1) := mul_le_mul_of_nonneg_left hA3L (by positivity)
      _ = (r * L) ^ 2 * (r * A1) := by ring
      _ ≤ 1 * (r * A1) := mul_le_mul_of_nonneg_right hsq hrA1
      _ = r * A1 := one_mul _
  have hkeyp : r ^ 3 * P3 ≤ r * P1 := by
    calc r ^ 3 * P3 ≤ r ^ 3 * (L ^ 2 * P1) := mul_le_mul_of_nonneg_left hP3L (by positivity)
      _ = (r * L) ^ 2 * (r * P1) := by ring
      _ ≤ 1 * (r * P1) := mul_le_mul_of_nonneg_right hsq hrP1
      _ = r * P1 := one_mul _
  have hr3A3 : 0 ≤ r ^ 3 * A3 := by positivity
  have hr3P3 : 0 ≤ r ^ 3 * P3 := by positivity
  have hbTa1 : |Ta1| ≤ 7 / 6 * (r * A1) := by rw [hTa1, abs_le]; constructor <;> linarith
  have hbTa2 : |Ta2| ≤ 10 / 3 * (r * A1) := by rw [hTa2, abs_le]; constructor <;> linarith
  have hbTp1 : |Tp1| ≤ 7 / 6 * (r * P1) := by rw [hTp1, abs_le]; constructor <;> linarith
  have hbTp2 : |Tp2| ≤ 10 / 3 * (r * P1) := by rw [hTp2, abs_le]; constructor <;> linarith
  have hEa1' : |Ba1 - Ta1| ≤ r ^ 5 * L ^ 4 * A1 / 120 := by
    refine hEa1.trans ?_
    calc r ^ 5 / 120 * A5 ≤ r ^ 5 / 120 * (L ^ 4 * A1) :=
          mul_le_mul_of_nonneg_left hA5L (by positivity)
      _ = r ^ 5 * L ^ 4 * A1 / 120 := by ring
  have hEa2' : |Ba2 - Ta2| ≤ 32 * (r ^ 5 * L ^ 4 * A1) / 120 := by
    refine hEa2.trans ?_
    calc (2 * r) ^ 5 / 120 * A5 ≤ (2 * r) ^ 5 / 120 * (L ^ 4 * A1) :=
          mul_le_mul_of_nonneg_left hA5L (by positivity)
      _ = 32 * (r ^ 5 * L ^ 4 * A1) / 120 := by ring
  have hEp1' : |Bp1 - Tp1| ≤ r ^ 5 * L ^ 4 * P1 / 120 := by
    refine hEp1.trans ?_
    calc r ^ 5 / 120 * P5 ≤ r ^ 5 / 120 * (L ^ 4 * P1) :=
          mul_le_mul_of_nonneg_left hP5L (by positivity)
      _ = r ^ 5 * L ^ 4 * P1 / 120 := by ring
  have hEp2' : |Bp2 - Tp2| ≤ 32 * (r ^ 5 * L ^ 4 * P1) / 120 := by
    refine hEp2.trans ?_
    calc (2 * r) ^ 5 / 120 * P5 ≤ (2 * r) ^ 5 / 120 * (L ^ 4 * P1) :=
          mul_le_mul_of_nonneg_left hP5L (by positivity)
      _ = 32 * (r ^ 5 * L ^ 4 * P1) / 120 := by ring
  have hZ0 : (0 : ℝ) ≤ r ^ 6 * L ^ 4 * (A1 * P1) := by positivity
  have hshrink : (r ^ 6 * L ^ 4 * (A1 * P1)) * (r ^ 4 * L ^ 4) ≤ (r ^ 6 * L ^ 4 * (A1 * P1)) * 1 :=
    mul_le_mul_of_nonneg_left h4L hZ0
  have b1 : |Ta1 * (Bp2 - Tp2)| ≤ (224 / 720) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    calc |Ta1| * |Bp2 - Tp2| ≤ (7 / 6 * (r * A1)) * (32 * (r ^ 5 * L ^ 4 * P1) / 120) :=
          mul_le_mul hbTa1 hEp2' (abs_nonneg _) (by positivity)
      _ = (224 / 720) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  have b2 : |(Ba1 - Ta1) * Tp2| ≤ (10 / 360) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    calc |Ba1 - Ta1| * |Tp2| ≤ (r ^ 5 * L ^ 4 * A1 / 120) * (10 / 3 * (r * P1)) :=
          mul_le_mul hEa1' hbTp2 (abs_nonneg _) (by positivity)
      _ = (10 / 360) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  have b3 : |(Ba1 - Ta1) * (Bp2 - Tp2)| ≤ (32 / 14400) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    refine (mul_le_mul hEa1' hEp2' (abs_nonneg _) (by positivity)).trans ?_
    calc (r ^ 5 * L ^ 4 * A1 / 120) * (32 * (r ^ 5 * L ^ 4 * P1) / 120)
        = (32 / 14400) * ((r ^ 6 * L ^ 4 * (A1 * P1)) * (r ^ 4 * L ^ 4)) := by ring
      _ ≤ (32 / 14400) * ((r ^ 6 * L ^ 4 * (A1 * P1)) * 1) := by linarith
      _ = (32 / 14400) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  have b4 : |Ta2 * (Bp1 - Tp1)| ≤ (10 / 360) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    calc |Ta2| * |Bp1 - Tp1| ≤ (10 / 3 * (r * A1)) * (r ^ 5 * L ^ 4 * P1 / 120) :=
          mul_le_mul hbTa2 hEp1' (abs_nonneg _) (by positivity)
      _ = (10 / 360) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  have b5 : |(Ba2 - Ta2) * Tp1| ≤ (224 / 720) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    calc |Ba2 - Ta2| * |Tp1| ≤ (32 * (r ^ 5 * L ^ 4 * A1) / 120) * (7 / 6 * (r * P1)) :=
          mul_le_mul hEa2' hbTp1 (abs_nonneg _) (by positivity)
      _ = (224 / 720) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  have b6 : |(Ba2 - Ta2) * (Bp1 - Tp1)| ≤ (32 / 14400) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by
    rw [abs_mul]
    refine (mul_le_mul hEa2' hEp1' (abs_nonneg _) (by positivity)).trans ?_
    calc (32 * (r ^ 5 * L ^ 4 * A1) / 120) * (r ^ 5 * L ^ 4 * P1 / 120)
        = (32 / 14400) * ((r ^ 6 * L ^ 4 * (A1 * P1)) * (r ^ 4 * L ^ 4)) := by ring
      _ ≤ (32 / 14400) * ((r ^ 6 * L ^ 4 * (A1 * P1)) * 1) := by linarith
      _ = (32 / 14400) * (r ^ 6 * L ^ 4 * (A1 * P1)) := by ring
  refine det_sign_from_bounds (S := r ^ 4 * (A1 * P3 - A3 * P1)) (Z := r ^ 6 * L ^ 4 * (A1 * P1))
    ?_ b1 b2 b3 b4 b5 b6 (by norm_num) hZ0 ?_
  · subst hTa1; subst hTa2; subst hTp1; subst hTp2; ring
  · calc r ^ 6 * L ^ 4 * (A1 * P1) = r ^ 4 * (r ^ 2 * L ^ 4 * (A1 * P1)) := by ring
      _ < r ^ 4 * (A1 * P3 - A3 * P1) := mul_lt_mul_of_pos_left hgap (by positivity)

/-! ## The actual finite-radius odd minor -/

/-- The two-height, two-radius odd minor at radii `r` and `2r`. -/
noncomputable def oddFiniteRadiusDeterminant (L : ℝ) (φ : ℝ → ℝ) (a p r : ℝ) : ℝ :=
  oddResponse L φ a r * oddResponse L φ p (2 * r)
    - oddResponse L φ a (2 * r) * oddResponse L φ p r

/-- **Finite-radius sign preservation.**  Under the relative smallness condition
`r² L⁴ N₁(a) N₁(p) < Δ_odd`, the actual finite-radius odd minor is strictly
negative. -/
theorem oddFiniteRadiusDeterminant_neg {L Cφ a p r : ℝ} {φ : ℝ → ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p) (hr : 0 < r) (hrL : r * L ≤ 1)
    (hgap : r ^ 2 * L ^ 4 * (oddMoment L φ 1 a * oddMoment L φ 1 p)
      < oddMoment L φ 1 a * oddMoment L φ 3 p - oddMoment L φ 3 a * oddMoment L φ 1 p) :
    oddFiniteRadiusDeterminant L φ a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  have hA3L : oddMoment L φ 3 a ≤ L ^ 2 * oddMoment L φ 1 a := by
    have h := oddMoment_le_of_support hφmeas hφ0 hφb hL ha 1 2
    norm_num at h
    exact h
  have hA5L : oddMoment L φ 5 a ≤ L ^ 4 * oddMoment L φ 1 a := by
    have h := oddMoment_le_of_support hφmeas hφ0 hφb hL ha 1 4
    norm_num at h
    exact h
  have hP3L : oddMoment L φ 3 p ≤ L ^ 2 * oddMoment L φ 1 p := by
    have h := oddMoment_le_of_support hφmeas hφ0 hφb hL hp 1 2
    norm_num at h
    exact h
  have hP5L : oddMoment L φ 5 p ≤ L ^ 4 * oddMoment L φ 1 p := by
    have h := oddMoment_le_of_support hφmeas hφ0 hφb hL hp 1 4
    norm_num at h
    exact h
  exact sign_transfer (A5 := oddMoment L φ 5 a) (P5 := oddMoment L φ 5 p)
    hL hr hrL
    (oddMoment_nonneg hφ0 ha 1) (oddMoment_nonneg hφ0 ha 3)
    (oddMoment_nonneg hφ0 hp 1) (oddMoment_nonneg hφ0 hp 3)
    hA3L hA5L hP3L hP5L rfl rfl rfl rfl
    (oddResponse_sub_trunc_abs_le (y := a) (r := r) hφmeas hφ0 hφb hL ha hr.le)
    (oddResponse_sub_trunc_abs_le (y := a) (r := 2 * r) hφmeas hφ0 hφb hL ha (by linarith))
    (oddResponse_sub_trunc_abs_le (y := p) (r := r) hφmeas hφ0 hφb hL hp hr.le)
    (oddResponse_sub_trunc_abs_le (y := p) (r := 2 * r) hφmeas hφ0 hφb hL hp (by linarith))
    hgap

/-- **The odd finite-radius minor has a strict sign at all small radii.**
Combining the continuum strict margin (`oddMomentDeterminant_strictPos`) with the
sign-preservation gate: for an admissible taper with a plateau and any
`0 < a < p`, there is an explicit threshold below which the actual finite-radius
odd minor is strictly negative. -/
theorem exists_radius_oddFiniteRadiusDeterminant_neg {L Cφ a p c d m : ℝ} {φ : ℝ → ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → oddFiniteRadiusDeterminant L φ a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  set Δ : ℝ := oddMoment L φ 1 a * oddMoment L φ 3 p - oddMoment L φ 3 a * oddMoment L φ 1 p
    with hΔdef
  have hΔ : 0 < Δ := by
    have h := oddMomentDeterminant_strictPos hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
    rw [hΔdef]
    linarith
  set K : ℝ := L ^ 4 * (oddMoment L φ 1 a * oddMoment L φ 1 p) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (oddMoment_nonneg hφ0 ha 1)
        (oddMoment_nonneg hφ0 hp 1))
  refine ⟨min (min (1 / L) 1) (Δ / (K + 1)), ?_, ?_⟩
  · refine lt_min (lt_min (by positivity) one_pos) (by positivity)
  · intro r hr hlt
    have h1 : r < 1 / L := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : r < 1 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have h3 : r < Δ / (K + 1) := lt_of_lt_of_le hlt (min_le_right _ _)
    have hrL : r * L ≤ 1 := le_of_lt ((lt_div_iff₀ hL).1 (by simpa [one_div] using h1))
    refine oddFiniteRadiusDeterminant_neg hφmeas hφ0 hφb hL ha hap hr hrL ?_
    have hrK : r * (K + 1) < Δ := (lt_div_iff₀ (by linarith : (0:ℝ) < K + 1)).1 h3
    have hrK0 : 0 ≤ r * K := mul_nonneg hr.le hK0
    have hr2 : r ^ 2 * K ≤ r * K := by
      calc r ^ 2 * K = r * (r * K) := by ring
        _ ≤ 1 * (r * K) := mul_le_mul_of_nonneg_right h2.le hrK0
        _ = r * K := one_mul _
    have hexp : r * (K + 1) = r * K + r := by ring
    calc r ^ 2 * L ^ 4 * (oddMoment L φ 1 a * oddMoment L φ 1 p) = r ^ 2 * K := by
          rw [hKdef]; ring
      _ ≤ r * K := hr2
      _ < Δ := by linarith
  
end OddTaylorDeterminant
end RiemannAnalytic
