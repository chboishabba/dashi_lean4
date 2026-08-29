/-
**Joint transverse-Lipschitz and horizontal decay of the interference kernel.**

`TransverseKernel.lean` proves two *separate* bounds for the imaginary part of
the complex extension of a real even taper:

* a transverse (vertical) Lipschitz bound `|Im Φ(x+iy)| ≤ 2|y| M₁`, and
* a horizontal decay bound `|Im Φ(x+iy)| ≤ M/|x|`.

Balancing them gives an interference envelope that is only *linear* in the
transverse offset, while the coercive Gram defect is quadratic — so the two
separate bounds cannot decide the competition.

This file proves the **joint** bound (milestone M4),

  `|Im Φ_ψ(x + iy)| ≤ |y| · K_ψ / |x|`,

with the explicit constant `K_ψ = 2∫|ψ'(u)||u| du + ∫|ψ(u)| e^{|u|} du`
(`transverseDecayConst`), valid for `|y| ≤ 1` and `|y| R ≤ 1`.  The proof is
the mechanism the programme predicts: `Im Φ_ψ` vanishes identically on the real
axis when `ψ` is even, so

  `Im Φ_ψ(x+iy) = Im Φ_{g_y}(x)`,   `g_y(t) = ψ(t)(e^{yt} - 1)`,

and `g_y` is itself a `C¹` taper whose derivative is `O(|y|)` in `L¹`; the
horizontal decay of `Φ_{g_y}` then supplies the `1/|x|`.

The consequence (milestone M5) is a **quadratic** interference envelope:

  `∑_σ (Im Φ(w_σ))² ≤ 2 y² K² / δ²`

for a `δ`-separated family of coordinate differences with transverse parts at
most `y` (`mixedInterference_envelope_quadratic`).  This is the same order in
the transverse offset as the Gram defect floor, so the comparison between
signal and interference is now a comparison of *explicit constants* rather than
of powers of `α` (`gramDefect_beats_interference`).
-/
import RiemannAnalytic.KernelEnvelope
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open MeasureTheory Complex

/-! ### The lifted taper `g_y(t) = ψ(t)(e^{yt} - 1)` -/

/-- The lifted taper `g_y(t) = ψ(t)(e^{yt} - 1)`, whose extension along the
real axis carries the whole imaginary part of `Φ_ψ` off the axis. -/
noncomputable def liftTaper (ψ : ℝ → ℝ) (y : ℝ) : ℝ → ℝ :=
  fun t => ψ t * (Real.exp (y * t) - 1)

theorem liftTaper_hasDerivAt {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R) (y t : ℝ) :
    HasDerivAt (liftTaper ψ y)
      (deriv ψ t * (Real.exp (y * t) - 1) + ψ t * (y * Real.exp (y * t))) t := by
  have h1 : HasDerivAt ψ (deriv ψ t) t := (hψ.diff t).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (y * s) - 1) (y * Real.exp (y * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ => y * s) y t := by
      simpa using (hasDerivAt_id t).const_mul y
    have := hlin.exp
    simpa [mul_comm] using this.sub_const 1
  simpa [liftTaper] using h1.mul h2

theorem liftTaper_deriv {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R) (y : ℝ) :
    deriv (liftTaper ψ y)
      = fun t => deriv ψ t * (Real.exp (y * t) - 1) + ψ t * (y * Real.exp (y * t)) :=
  funext fun t => (liftTaper_hasDerivAt hψ y t).deriv

/-- The lifted taper is again a `C¹` taper of the same radius. -/
theorem liftTaper_C1Taper {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R) (y : ℝ) :
    C1Taper (liftTaper ψ y) R where
  diff := fun t => (liftTaper_hasDerivAt hψ y t).differentiableAt
  contDeriv := by
    rw [liftTaper_deriv hψ y]
    exact (hψ.contDeriv.mul (by fun_prop)).add (hψ.cont.mul (by fun_prop))
  supp := fun t ht => by simp [liftTaper, hψ.supp t ht]

/-! ### The imaginary part off the axis is the lifted extension on the axis -/

/-- Splitting the extension at height `y` into the lifted taper on the real
axis plus the taper itself on the real axis. -/
theorem PhiExt_eq_lift_add {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R) (w : ℂ) :
    PhiExt ψ w = PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)
      + PhiExt ψ ((w.re : ℝ) : ℂ) := by
  have hint₁ : Integrable (twist (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)) :=
    twist_integrable (liftTaper_C1Taper hψ w.im).cont (liftTaper_C1Taper hψ w.im).supp _
  have hint₂ : Integrable (twist ψ ((w.re : ℝ) : ℂ)) :=
    twist_integrable hψ.cont hψ.supp _
  unfold PhiExt
  rw [show (∫ t : ℝ, (liftTaper ψ w.im t : ℂ)
        * Complex.exp (-(Complex.I * ((w.re : ℝ) : ℂ) * (t : ℂ))))
      = ∫ t : ℝ, twist (liftTaper ψ w.im) ((w.re : ℝ) : ℂ) t from rfl,
    show (∫ t : ℝ, (ψ t : ℂ) * Complex.exp (-(Complex.I * ((w.re : ℝ) : ℂ) * (t : ℂ))))
      = ∫ t : ℝ, twist ψ ((w.re : ℝ) : ℂ) t from rfl,
    ← integral_add hint₁ hint₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hexp : Complex.exp (-(Complex.I * w * (t : ℂ)))
      = Complex.exp ((w.im * t : ℝ)) * Complex.exp (-(Complex.I * ((w.re : ℝ) : ℂ) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  simp only [twist, liftTaper]
  rw [hexp]
  push_cast
  ring

/-- **The imaginary part off the real axis is entirely carried by the lifted
taper.**  For a real even taper `Im Φ_ψ` vanishes on the real axis, so the
whole imaginary part at height `y` comes from `g_y`. -/
theorem PhiExt_im_eq_lift {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R)
    (hev : ∀ t, ψ (-t) = ψ t) (w : ℂ) :
    (PhiExt ψ w).im = (PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)).im := by
  have haxis : (PhiExt ψ ((w.re : ℝ) : ℂ)).im = 0 := by
    rw [PhiExt_im_eq_integral hψ.toCompactTaper]
    have hodd : ∀ t : ℝ,
        ψ (-t) * (Real.exp (((w.re : ℝ) : ℂ).im * -t) * Real.sin (((w.re : ℝ) : ℂ).re * -t))
          = -(ψ t * (Real.exp (((w.re : ℝ) : ℂ).im * t) * Real.sin (((w.re : ℝ) : ℂ).re * t))) := by
      intro t
      simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, Real.exp_zero, one_mul,
        hev t]
      rw [show w.re * -t = -(w.re * t) by ring, Real.sin_neg]
      ring
    rw [integral_odd_eq_zero hodd]
    simp
  rw [PhiExt_eq_lift_add hψ w, Complex.add_im, haxis, add_zero]

/-! ### The `L¹` mass of the lifted derivative is `O(|y|)` -/

/-- The `L¹` mass of a taper against `e^{|u|}`. -/
noncomputable def tailMass (ψ : ℝ → ℝ) : ℝ := ∫ u : ℝ, |ψ u| * Real.exp |u|

theorem tailMass_nonneg (ψ : ℝ → ℝ) : 0 ≤ tailMass ψ :=
  integral_nonneg fun u => by positivity

/-- The explicit constant in the joint transverse/horizontal estimate:
`K_ψ = 2∫|ψ'(u)||u| du + ∫|ψ(u)| e^{|u|} du`. -/
noncomputable def transverseDecayConst (ψ : ℝ → ℝ) : ℝ :=
  2 * momentMass (deriv ψ) + tailMass ψ

theorem transverseDecayConst_nonneg (ψ : ℝ → ℝ) : 0 ≤ transverseDecayConst ψ := by
  unfold transverseDecayConst
  have := momentMass_nonneg (deriv ψ)
  have := tailMass_nonneg ψ
  linarith

/-- **The lifted derivative has `L¹` mass at most `|y| K_ψ`.** -/
theorem integral_abs_liftTaper_deriv_le {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R)
    {y : ℝ} (hy1 : |y| ≤ 1) (hyR : |y| * R ≤ 1) :
    ∫ u : ℝ, |deriv (liftTaper ψ y) u| ≤ |y| * transverseDecayConst ψ := by
  have hint : Integrable fun u : ℝ => |deriv (liftTaper ψ y) u| := by
    have := (liftTaper_C1Taper hψ y).integrable_absDeriv_mul (g := fun _ : ℝ => (1 : ℝ))
      continuous_const
    simpa using this
  have hmaj : Integrable fun u : ℝ =>
      |y| * (2 * (|deriv ψ u| * |u|) + |ψ u| * Real.exp |u|) := by
    have h1 : Integrable fun u : ℝ => |deriv ψ u| * |u| :=
      hψ.integrable_absDeriv_mul (by fun_prop)
    have h2 : Integrable fun u : ℝ => |ψ u| * Real.exp |u| :=
      hψ.toCompactTaper.integrable_abs_mul (by fun_prop)
    exact (((h1.const_mul 2).add h2).const_mul _)
  have hpt : ∀ u : ℝ, |deriv (liftTaper ψ y) u|
      ≤ |y| * (2 * (|deriv ψ u| * |u|) + |ψ u| * Real.exp |u|) := by
    intro u
    rw [liftTaper_deriv hψ y]
    by_cases hu : R < |u|
    · simp [hψ.supp u hu, hψ.derivSupp u hu]
    · have huR : |u| ≤ R := not_lt.1 hu
      have harg : |y * u| ≤ 1 := by
        rw [abs_mul]
        have h1 : |y| * |u| ≤ |y| * R := by
          have := abs_nonneg y
          nlinarith
        linarith
      have hexp1 : |Real.exp (y * u) - 1| ≤ 2 * (|y| * |u|) := by
        have := Real.abs_exp_sub_one_le harg
        rwa [abs_mul] at this
      have hexp2 : Real.exp (y * u) ≤ Real.exp |u| := by
        refine Real.exp_le_exp.2 ?_
        calc y * u ≤ |y * u| := le_abs_self _
          _ = |y| * |u| := abs_mul y u
          _ ≤ 1 * |u| := by nlinarith [abs_nonneg u]
          _ = |u| := one_mul _
      have hterm1 : |deriv ψ u * (Real.exp (y * u) - 1)|
          ≤ |y| * (2 * (|deriv ψ u| * |u|)) := by
        rw [abs_mul]
        have h0 : (0 : ℝ) ≤ |deriv ψ u| := abs_nonneg _
        nlinarith [hexp1, abs_nonneg (Real.exp (y * u) - 1)]
      have hterm2 : |ψ u * (y * Real.exp (y * u))| ≤ |y| * (|ψ u| * Real.exp |u|) := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (y * u))]
        have h0 : (0 : ℝ) ≤ |ψ u| := abs_nonneg _
        have h1 : (0 : ℝ) ≤ |y| := abs_nonneg _
        calc |ψ u| * (|y| * Real.exp (y * u)) = (|ψ u| * |y|) * Real.exp (y * u) := by ring
          _ ≤ (|ψ u| * |y|) * Real.exp |u| :=
              mul_le_mul_of_nonneg_left hexp2 (mul_nonneg h0 h1)
          _ = |y| * (|ψ u| * Real.exp |u|) := by ring
      calc |deriv ψ u * (Real.exp (y * u) - 1) + ψ u * (y * Real.exp (y * u))|
          ≤ |deriv ψ u * (Real.exp (y * u) - 1)| + |ψ u * (y * Real.exp (y * u))| :=
            abs_add_le _ _
        _ ≤ |y| * (2 * (|deriv ψ u| * |u|)) + |y| * (|ψ u| * Real.exp |u|) := by
            linarith
        _ = |y| * (2 * (|deriv ψ u| * |u|) + |ψ u| * Real.exp |u|) := by ring
  have hmono := integral_mono hint hmaj hpt
  have hval : ∫ u : ℝ, |y| * (2 * (|deriv ψ u| * |u|) + |ψ u| * Real.exp |u|)
      = |y| * transverseDecayConst ψ := by
    rw [integral_const_mul]
    congr 1
    have h1 : Integrable fun u : ℝ => 2 * (|deriv ψ u| * |u|) :=
      (hψ.integrable_absDeriv_mul (by fun_prop)).const_mul 2
    have h2 : Integrable fun u : ℝ => |ψ u| * Real.exp |u| :=
      hψ.toCompactTaper.integrable_abs_mul (by fun_prop)
    rw [integral_add h1 h2, integral_const_mul]
    rfl
  linarith [hmono, hval.le, hval.ge]

/-! ### The joint estimate -/

/-- **M4: joint transverse-Lipschitz and horizontal decay.**

For a `C¹` real even taper supported in `[-R, R]`, for `|y| ≤ 1`, `|y| R ≤ 1`
and `x ≠ 0`,

  `|Im Φ_ψ(x + iy)| ≤ |y| · K_ψ / |x|`.

The imaginary part vanishes on the real axis and decays horizontally *at the
same time*: the bound is simultaneously linear in the transverse displacement
and inverse-linear in the ordinate separation. -/
theorem abs_im_PhiExt_le_transverse_decay {ψ : ℝ → ℝ} {R : ℝ} (hψ : C1Taper ψ R)
    (hev : ∀ t, ψ (-t) = ψ t) {w : ℂ} (hy1 : |w.im| ≤ 1) (hyR : |w.im| * R ≤ 1)
    (hx : w.re ≠ 0) :
    |(PhiExt ψ w).im| ≤ |w.im| * transverseDecayConst ψ / |w.re| := by
  have hxpos : 0 < |w.re| := abs_pos.2 hx
  rw [PhiExt_im_eq_lift hψ hev w]
  have hle : |(PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)).im|
      ≤ ‖PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)‖ :=
    Complex.abs_im_le_norm _
  have hdecay := norm_PhiExt_mul_abs_re_le (liftTaper_C1Taper hψ w.im) ((w.re : ℝ) : ℂ)
  simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, Real.exp_zero, mul_one] at hdecay
  have hmass := integral_abs_liftTaper_deriv_le hψ hy1 hyR
  rw [le_div_iff₀ hxpos]
  calc |(PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)).im| * |w.re|
      ≤ ‖PhiExt (liftTaper ψ w.im) ((w.re : ℝ) : ℂ)‖ * |w.re| := by
        exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ ≤ ∫ u : ℝ, |deriv (liftTaper ψ w.im) u| := hdecay
    _ ≤ |w.im| * transverseDecayConst ψ := hmass

/-- The same estimate for the interference kernel `Φ_{φ²}`. -/
theorem abs_im_PhiKernel_le_transverse_decay {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {w : ℂ} (hy1 : |w.im| ≤ 1) (hyR : |w.im| * R ≤ 1)
    (hx : w.re ≠ 0) :
    |(PhiExt (fun t => φ t ^ 2) w).im|
      ≤ |w.im| * transverseDecayConst (fun t => φ t ^ 2) / |w.re| :=
  abs_im_PhiExt_le_transverse_decay hφ.sq (fun t => by rw [hev t]) hy1 hyR hx

/-! ### M5: the quadratic interference envelope -/

/-- **Quadratic mixed-interference envelope.**

Let `w : ℕ → ℂ` enumerate the coordinate differences of the other zeros from a
target zero, `δ`-separated in the ordinate and with transverse parts at most
`y ≤ 1` (with `y R ≤ 1`).  Then

  `∑_n (Im Φ(w n))² ≤ 2 y² K² / δ²`,

*quadratic* in the transverse offset, with `K = transverseDecayConst (φ²)`.
This is the same order in the offset as the Gram-defect floor, so the
comparison between signal and interference becomes a comparison of explicit
constants. -/
theorem mixedInterference_envelope_quadratic {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {δ y : ℝ} (hδ : 0 < δ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hyR : y * R ≤ 1) (w : ℕ → ℂ)
    (hre : ∀ n : ℕ, δ * ((n : ℝ) + 1) ≤ |(w n).re|)
    (him : ∀ n : ℕ, |(w n).im| ≤ y) :
    ∑' n : ℕ, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ 2 * y ^ 2 * transverseDecayConst (fun t => φ t ^ 2) ^ 2 / δ ^ 2 := by
  set K := transverseDecayConst (fun t => φ t ^ 2) with hK
  have hK0 : 0 ≤ K := transverseDecayConst_nonneg _
  set f : ℕ → ℝ := fun n => (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2 with hf
  have hfnn : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  set C : ℝ := y ^ 2 * K ^ 2 / δ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ n : ℕ, f n ≤ C * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hpos : (0 : ℝ) < δ * ((n : ℝ) + 1) := by positivity
    have hrepos : 0 < |(w n).re| := lt_of_lt_of_le hpos (hre n)
    have hx : (w n).re ≠ 0 := fun h0 => by simp [h0] at hrepos
    have hyn1 : |(w n).im| ≤ 1 := le_trans (him n) hy1
    have hynR : |(w n).im| * R ≤ 1 := by
      by_cases hR : R ≤ 0
      · have : |(w n).im| * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hR
        linarith
      · have hR' : 0 < R := lt_of_not_ge hR
        have := him n
        nlinarith [abs_nonneg (w n).im]
    have hstep := abs_im_PhiKernel_le_transverse_decay hφ hev hyn1 hynR hx
    have hnum : |(w n).im| * K ≤ y * K := mul_le_mul_of_nonneg_right (him n) hK0
    have hden : |(w n).im| * K / |(w n).re| ≤ y * K / (δ * ((n : ℝ) + 1)) := by
      calc |(w n).im| * K / |(w n).re| ≤ y * K / |(w n).re| := by gcongr
        _ ≤ y * K / (δ * ((n : ℝ) + 1)) := by
            refine div_le_div_of_nonneg_left ?_ hpos (hre n)
            exact mul_nonneg hy0 hK0
    have habs : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ y * K / (δ * ((n : ℝ) + 1)) :=
      hstep.trans hden
    have hsq : f n ≤ (y * K / (δ * ((n : ℝ) + 1))) ^ 2 := by
      have h1 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ^ 2 = f n := sq_abs _
      nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w n)).im,
        div_nonneg (mul_nonneg hy0 hK0) hpos.le]
    have hval : (y * K / (δ * ((n : ℝ) + 1))) ^ 2 = C * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
      rw [hC, div_pow, mul_pow, mul_pow]
      field_simp
    linarith [hsq, hval.le, hval.ge]
  have hshift : Summable fun n : ℕ => (1 : ℝ) / (((n : ℝ)) + 1) ^ 2 := by
    have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_nat_pow.2 (by norm_num)
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).2 hnat
    exact h.congr fun n => by push_cast; ring_nf
  have hmaj : Summable fun n : ℕ => C * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := hshift.mul_left _
  have hfsum : Summable f := hmaj.of_nonneg_of_le hfnn hbound
  have hle := Summable.tsum_le_tsum hbound hfsum hmaj
  have htsum : ∑' n : ℕ, C * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) ≤ 2 * C := by
    rw [tsum_mul_left]
    have := tsum_nat_inv_sq_shift_le
    nlinarith [hC0]
  have hfin : 2 * C = 2 * y ^ 2 * K ^ 2 / δ ^ 2 := by
    rw [hC]; ring
  linarith [hle, htsum, hfin.le, hfin.ge]

/-! ### Signal versus interference -/

/-- **The comparison is now between explicit constants, not powers of `α`.**

If the window is long enough that the lattice tail eats at most half the
retention floor, and if the interference constant obeys the `α`-independent
inequality `2K²/δ² < (81/16384) L⁶`, then for *every* nonzero transverse offset
`α` the total mixed interference of the target with the rest of the family is
strictly smaller than the target's own Gram defect on the one-sided source
window. -/
theorem gramDefect_beats_interference {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {α : ℝ} (hα : α ≠ 0)
    {m : ℕ} (hm : 1 ≤ m)
    (htail : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2)
    {δ : ℝ} (hδ : 0 < δ) (hα1 : |α| ≤ 1) (hαR : |α| * R ≤ 1) (w : ℕ → ℂ)
    (hre : ∀ n : ℕ, δ * ((n : ℝ) + 1) ≤ |(w n).re|)
    (him : ∀ n : ℕ, |(w n).im| ≤ |α|)
    (hratio : 2 * transverseDecayConst (fun t => φ t ^ 2) ^ 2 / δ ^ 2 < 81 / 16384 * L ^ 6) :
    ∑' n : ℕ, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      < finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  set K := transverseDecayConst (fun t => φ t ^ 2) with hK
  have hα2 : 0 < α ^ 2 := by positivity
  have henv := mixedInterference_envelope_quadratic hφ hev hδ (abs_nonneg α) hα1 hαR w hre him
  have habs2 : |α| ^ 2 = α ^ 2 := sq_abs α
  rw [habs2] at henv
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hstep : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
    nlinarith [htail, hL2]
  have hstrict : 2 * α ^ 2 * K ^ 2 / δ ^ 2 < 81 / 16384 * L ^ 6 * α ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hratio hα2
    have hL : 2 * K ^ 2 / δ ^ 2 * α ^ 2 = 2 * α ^ 2 * K ^ 2 / δ ^ 2 := by ring
    linarith [hmul, hL.le, hL.ge]
  linarith [henv, hstrict, hstep, hfloor]

/-- **The signal-to-interference ratio is independent of the transverse
offset.**  Under the same hypotheses (minus the strict constant inequality),
the total mixed interference is at most

  `η · ΔGram`,   `η = 32768 K² / (81 δ² L⁶)`,

with `η` free of `α`.  Localization therefore amounts to making this single
explicit constant smaller than `1`; no cancellation in `α` is available or
needed. -/
theorem interference_le_ratio_mul_gramDefect {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ)
    {m : ℕ} (hm : 1 ≤ m)
    (htail : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2)
    {δ : ℝ} (hδ : 0 < δ) (hα1 : |α| ≤ 1) (hαR : |α| * R ≤ 1) (w : ℕ → ℂ)
    (hre : ∀ n : ℕ, δ * ((n : ℝ) + 1) ≤ |(w n).re|)
    (him : ∀ n : ℕ, |(w n).im| ≤ |α|) :
    ∑' n : ℕ, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ 32768 * transverseDecayConst (fun t => φ t ^ 2) ^ 2 / (81 * δ ^ 2 * L ^ 6)
        * finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  set K := transverseDecayConst (fun t => φ t ^ 2) with hK
  have hK0 : 0 ≤ K := transverseDecayConst_nonneg _
  have henv := mixedInterference_envelope_quadratic hφ hev hδ (abs_nonneg α) hα1 hαR w hre him
  rw [sq_abs α] at henv
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hstep : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
    nlinarith [htail, hL2]
  have hgram : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by linarith
  have hcoef : (0 : ℝ) ≤ 32768 * K ^ 2 / (81 * δ ^ 2 * L ^ 6) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hgram hcoef
  have hval : 32768 * K ^ 2 / (81 * δ ^ 2 * L ^ 6) * (81 / 16384 * L ^ 6 * α ^ 2)
      = 2 * α ^ 2 * K ^ 2 / δ ^ 2 := by
    field_simp
    ring
  rw [hval] at hmul
  linarith [henv, hmul]

end RiemannAnalytic
