/-
Transverse (vertical) smallness of the complex-`Φ` interference kernel.

`KernelChannels.lean` identifies the two interference channels of a pair of
hypothetical zeros with the imaginary part of the complex kernel
`Φ = PhiExt (φ²)`, and proves the *horizontal* decay `|Im Φ(w)| ≤ M/|Re w|`.
That decay alone gives the uniform envelope of `KernelEnvelope.lean`, but it is
blind to the size of the transverse offsets: it does not see that the whole
interference must vanish when the zeros return to the critical line.

This file supplies the missing *vertical* estimate.  For a real **even** taper
the kernel is real on the real axis, so `Im Φ(x)` vanishes identically there;
consequently `Im Φ(x + iy)` is small with `y`.  Quantitatively, writing

  `Im Φ_ψ(x + iy) = -∫ ψ(t) (e^{yt} - 1) sin(xt) dt`

(the `e^{yt} ↦ 1` part of the integrand integrates to zero by oddness), the
elementary bound `|e^{s} - 1| ≤ 2|s|` for `|s| ≤ 1` gives

  `|Im Φ_ψ(x + iy)| ≤ 2 |y| ∫ |ψ(u)| |u| du`

for every taper supported where `|y u| ≤ 1`.  This is `Lipschitz in the
transverse direction`, with the explicit constant `momentMass ψ`.

Combining the two regimes — the vertical bound for the nearby zeros and the
horizontal bound for the distant ones — produces a *two-regime* envelope, and,
after balancing the split, an envelope which is **linear in the transverse
offset**:

  `∑_{σ ≠ ρ} (Im Φ(w_σ))² ≤ y (8 M₁² + M²/δ²)`,

for a `δ`-separated family whose transverse offsets are at most `y ≤ 1`.

This is strictly stronger than the uniform envelope, and it is the honest
comparison point for the coercive defect, which is *quadratic* in the offset:
at the level of the second moment the interference envelope proved here is
`O(α)` while the defect floor is `Θ(α²)`, so the envelope does **not** by
itself beat the defect for small `α`.  That is recorded here as a proved
quantitative fact rather than an assumption.
-/
import RiemannAnalytic.KernelEnvelope

namespace RiemannAnalytic

open MeasureTheory Complex Finset

/-! ### Integrability helpers -/

/-- A continuous function vanishing outside `[-R, R]` is integrable. -/
theorem integrable_of_compact_support {f : ℝ → ℝ} {R : ℝ} (hf : Continuous f)
    (hsupp : ∀ t, R < |t| → f t = 0) : Integrable f := by
  refine hf.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun x hx => ?_
  refine hsupp x ?_
  by_contra hcon
  exact hx (Set.mem_Icc.2
    ⟨by cases abs_le.1 (not_lt.1 hcon) with | intro h1 _ => linarith,
     by cases abs_le.1 (not_lt.1 hcon) with | intro _ h2 => linarith⟩)

/-- The product of a compact taper with any continuous function is integrable. -/
theorem CompactTaper.integrable_mul {ψ : ℝ → ℝ} {R : ℝ} (hψ : CompactTaper ψ R)
    {g : ℝ → ℝ} (hg : Continuous g) : Integrable fun t => ψ t * g t :=
  integrable_of_compact_support (R := R) (hψ.cont.mul hg)
    fun t ht => by simp [hψ.supp t ht]

/-- The product of the modulus of a compact taper with any continuous function is
integrable. -/
theorem CompactTaper.integrable_abs_mul {ψ : ℝ → ℝ} {R : ℝ} (hψ : CompactTaper ψ R)
    {g : ℝ → ℝ} (hg : Continuous g) : Integrable fun t => |ψ t| * g t :=
  integrable_of_compact_support (R := R) (hψ.cont.abs.mul hg)
    fun t ht => by simp [hψ.supp t ht]

/-! ### The first absolute moment of the taper -/

/-- The first absolute moment `∫ |ψ(u)| |u| du` of a taper: the explicit constant
in the transverse (vertical) estimate for the kernel. -/
noncomputable def momentMass (ψ : ℝ → ℝ) : ℝ := ∫ u : ℝ, |ψ u| * |u|

theorem momentMass_nonneg (ψ : ℝ → ℝ) : 0 ≤ momentMass ψ :=
  integral_nonneg fun u => by positivity

/-! ### The imaginary part of the extension as a real integral -/

/-- The imaginary part of the complex extension is the real oscillatory
integral `-∫ ψ(t) e^{yt} sin(xt) dt`. -/
theorem PhiExt_im_eq_integral {ψ : ℝ → ℝ} {R : ℝ} (hψ : CompactTaper ψ R) (w : ℂ) :
    (PhiExt ψ w).im
      = -∫ t : ℝ, ψ t * (Real.exp (w.im * t) * Real.sin (w.re * t)) := by
  have hint : Integrable (twist ψ w) := twist_integrable hψ.cont hψ.supp w
  have him : (PhiExt ψ w).im = ∫ t : ℝ, (twist ψ w t).im := by
    rw [← integral_twist, ← Complex.imCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm _ hint]
    rfl
  rw [him, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hre : (-(Complex.I * w * (t : ℂ))).re = w.im * t := by
    simp [Complex.mul_re, Complex.mul_im]
  have himz : (-(Complex.I * w * (t : ℂ))).im = -(w.re * t) := by
    simp [Complex.mul_re, Complex.mul_im]
  simp only [twist, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_im, Complex.exp_re, hre, himz, Real.sin_neg]
  ring

/-- The integral of an odd function vanishes. -/
theorem integral_odd_eq_zero {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t) :
    ∫ t : ℝ, f t = 0 := by
  have h := integral_neg_eq_self f volume
  have h2 : ∫ t : ℝ, f (-t) = -∫ t : ℝ, f t := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => hodd t)
  linarith

/-! ### The transverse estimate -/

/-- **Transverse (vertical) smallness of the extension of a real even taper.**

For a real even taper supported in `[-R, R]`, and a complex argument whose
imaginary part `y` satisfies `|y| R ≤ 1`,

  `|Im Φ_ψ(w)| ≤ 2 |Im w| · momentMass ψ`.

In particular the imaginary part vanishes on the real axis and is Lipschitz in
the transverse direction, with an explicit constant. -/
theorem abs_im_PhiExt_le_transverse {ψ : ℝ → ℝ} {R : ℝ} (hψ : CompactTaper ψ R)
    (hev : ∀ t, ψ (-t) = ψ t) {w : ℂ} (hwR : |w.im| * R ≤ 1) :
    |(PhiExt ψ w).im| ≤ 2 * |w.im| * momentMass ψ := by
  set x := w.re
  set y := w.im
  -- the three integrands
  set F : ℝ → ℝ := fun t => ψ t * (Real.exp (y * t) * Real.sin (x * t)) with hF
  set F₀ : ℝ → ℝ := fun t => ψ t * Real.sin (x * t) with hF₀
  set Fd : ℝ → ℝ := fun t => ψ t * ((Real.exp (y * t) - 1) * Real.sin (x * t)) with hFd
  have hFint : Integrable F := hψ.integrable_mul (by fun_prop)
  have hF₀int : Integrable F₀ := hψ.integrable_mul (by fun_prop)
  have hFdint : Integrable Fd := hψ.integrable_mul (by fun_prop)
  -- the `1` part integrates to zero by oddness
  have hzero : ∫ t : ℝ, F₀ t = 0 := by
    refine integral_odd_eq_zero fun t => ?_
    simp only [hF₀]
    rw [hev t, show x * -t = -(x * t) by ring, Real.sin_neg]
    ring
  have hsplit : ∫ t : ℝ, F t = ∫ t : ℝ, Fd t := by
    have hpt : ∀ t, F t = Fd t + F₀ t := by
      intro t; simp only [hF, hFd, hF₀]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hFdint hF₀int, hzero, add_zero]
  -- pointwise bound on the difference integrand
  have hbound : ∀ t : ℝ, |Fd t| ≤ 2 * |y| * (|ψ t| * |t|) := by
    intro t
    by_cases ht : R < |t|
    · simp [hFd, hψ.supp t ht]
    · have htR : |t| ≤ R := not_lt.1 ht
      have harg : |y * t| ≤ 1 := by
        rw [abs_mul]
        have h1 : |y| * |t| ≤ |y| * R := by
          have := abs_nonneg y
          nlinarith
        linarith
      have hexp : |Real.exp (y * t) - 1| ≤ 2 * (|y| * |t|) := by
        have := Real.abs_exp_sub_one_le harg
        rwa [abs_mul] at this
      have hsin : |Real.sin (x * t)| ≤ 1 := Real.abs_sin_le_one _
      calc |Fd t| = |ψ t| * (|Real.exp (y * t) - 1| * |Real.sin (x * t)|) := by
            simp only [hFd, abs_mul]
        _ ≤ |ψ t| * ((2 * (|y| * |t|)) * 1) := by
            have h0 : (0 : ℝ) ≤ |ψ t| := abs_nonneg _
            have h1 : (0 : ℝ) ≤ |Real.exp (y * t) - 1| := abs_nonneg _
            have h2 : (0 : ℝ) ≤ |Real.sin (x * t)| := abs_nonneg _
            have h3 : (0 : ℝ) ≤ 2 * (|y| * |t|) := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul hexp hsin h2 h3) h0
        _ = 2 * |y| * (|ψ t| * |t|) := by ring
  -- integrate the bound
  have hmajint : Integrable fun t : ℝ => 2 * |y| * (|ψ t| * |t|) := by
    have : Integrable fun t : ℝ => |ψ t| * |t| := hψ.integrable_abs_mul (by fun_prop)
    exact this.const_mul _
  have habs : |∫ t : ℝ, Fd t| ≤ ∫ t : ℝ, 2 * |y| * (|ψ t| * |t|) := by
    refine le_trans ?_ (integral_mono hFdint.abs hmajint hbound)
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume) Fd
  have hval : ∫ t : ℝ, 2 * |y| * (|ψ t| * |t|) = 2 * |y| * momentMass ψ := by
    rw [integral_const_mul]
    rfl
  rw [PhiExt_im_eq_integral hψ w, abs_neg]
  rw [show (∫ t : ℝ, ψ t * (Real.exp (w.im * t) * Real.sin (w.re * t))) = ∫ t : ℝ, F t from rfl,
    hsplit]
  linarith [habs, hval.le, hval.ge]

/-- The squared taper of a `C¹` taper is a compact taper. -/
theorem C1Taper.sqCompact {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) :
    CompactTaper (fun t => φ t ^ 2) R :=
  ⟨hφ.cont.pow 2, fun t ht => by simp [hφ.supp t ht]⟩

/-- **Transverse smallness of the interference kernel.** -/
theorem abs_im_PhiKernel_le_transverse {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {w : ℂ} (hwR : |w.im| * R ≤ 1) :
    |(PhiExt (fun t => φ t ^ 2) w).im|
      ≤ 2 * |w.im| * momentMass (fun t => φ t ^ 2) :=
  abs_im_PhiExt_le_transverse hφ.sqCompact (fun t => by rw [hev t]) hwR

/-! ### The two-regime envelope -/

/-- **Two-regime mixed-interference envelope.**

Let `w : ℕ → ℂ` enumerate the coordinate differences of the other zeros from a
target zero, `δ`-separated in the ordinate (`δ(n+1) ≤ |Re w n|`) and with
transverse offsets at most `y`.  Splitting the family at any index `N ≥ 1` and
using the transverse estimate below the split, the horizontal decay above it,

  `∑_n (Im Φ(w n))² ≤ 4 N y² M₁² + M²/(δ² N)`,

with `M₁ = momentMass (φ²)` and `M = kernelMass φ`. -/
theorem mixedInterference_envelope_transverse {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hR : 0 ≤ R) {δ y : ℝ} (hδ : 0 < δ)
    (hy1 : y ≤ 1) (hyR : y * R ≤ 1) (w : ℕ → ℂ)
    (hre : ∀ n : ℕ, δ * ((n : ℝ) + 1) ≤ |(w n).re|)
    (him : ∀ n : ℕ, |(w n).im| ≤ y) {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ 4 * N * y ^ 2 * momentMass (fun t => φ t ^ 2) ^ 2
        + kernelMass φ ^ 2 / (δ ^ 2 * N) := by
  set M := kernelMass φ with hM
  set M₁ := momentMass (fun t => φ t ^ 2) with hM₁
  have hM0 : 0 ≤ M := kernelMass_nonneg φ
  have hM₁0 : 0 ≤ M₁ := momentMass_nonneg _
  set f : ℕ → ℝ := fun n => (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2 with hf
  have hfnn : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  -- horizontal bound, valid for every index
  have hhor : ∀ n : ℕ, f n ≤ M ^ 2 / δ ^ 2 * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hsep := hre n
    have hpos : (0 : ℝ) < δ * ((n : ℝ) + 1) := by positivity
    have hrepos : 0 < |(w n).re| := lt_of_lt_of_le hpos hsep
    have hwre : (w n).re ≠ 0 := fun h0 => by simp [h0] at hrepos
    have him1 : |(w n).im| ≤ 1 := le_trans (him n) hy1
    have hb := abs_im_PhiKernel_le hφ hwre him1
    have hstep : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ M / (δ * ((n : ℝ) + 1)) := by
      refine hb.trans ?_
      gcongr
    have hsq : f n ≤ (M / (δ * ((n : ℝ) + 1))) ^ 2 := by
      have h1 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ^ 2 = f n := sq_abs _
      nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w n)).im,
        div_nonneg hM0 hpos.le]
    have hval : (M / (δ * ((n : ℝ) + 1))) ^ 2 = M ^ 2 / δ ^ 2 * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
      rw [div_pow, mul_pow]
      field_simp
    linarith [hsq, hval.le, hval.ge]
  -- vertical bound, valid for every index
  have hver : ∀ n : ℕ, f n ≤ 4 * y ^ 2 * M₁ ^ 2 := by
    intro n
    have hwR : |(w n).im| * R ≤ 1 := by
      have := him n
      nlinarith [abs_nonneg (w n).im]
    have hb := abs_im_PhiKernel_le_transverse hφ hev hwR
    have hb2 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ 2 * y * M₁ := by
      refine hb.trans ?_
      have := him n
      nlinarith [abs_nonneg (w n).im]
    have h1 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ^ 2 = f n := sq_abs _
    nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w n)).im]
  -- summability by comparison with the horizontal bound
  have hgsum : Summable fun n : ℕ => M ^ 2 / δ ^ 2 * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_nat_pow.2 (by norm_num)
    have hshift : Summable fun n : ℕ => (1 : ℝ) / (((n : ℝ)) + 1) ^ 2 := by
      have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).2 hnat
      exact h.congr fun n => by push_cast; ring_nf
    exact hshift.mul_left _
  have hfsum : Summable f := hgsum.of_nonneg_of_le hfnn hhor
  -- split the sum at `N`
  have hsplit := hfsum.sum_add_tsum_nat_add N
  -- head
  have hhead : ∑ i ∈ range N, f i ≤ 4 * N * y ^ 2 * M₁ ^ 2 := by
    calc ∑ i ∈ range N, f i ≤ ∑ _i ∈ range N, 4 * y ^ 2 * M₁ ^ 2 :=
          Finset.sum_le_sum fun i _ => hver i
      _ = N * (4 * y ^ 2 * M₁ ^ 2) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = 4 * N * y ^ 2 * M₁ ^ 2 := by ring
  -- tail
  have htail : ∑' n : ℕ, f (n + N) ≤ M ^ 2 / (δ ^ 2 * N) := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hbound : ∀ n : ℕ, f (n + N)
        ≤ M ^ 2 / δ ^ 2 * ((1 : ℝ) / (((n : ℝ)) + N + 1) ^ 2) := by
      intro n
      have h := hhor (n + N)
      have hcast : (((n + N : ℕ) : ℝ)) + 1 = ((n : ℝ)) + N + 1 := by push_cast; ring
      rw [hcast] at h
      exact h
    have hsum2 : Summable fun n : ℕ => M ^ 2 / δ ^ 2 * ((1 : ℝ) / (((n : ℝ)) + N + 1) ^ 2) := by
      have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + N + 1) ^ 2 := by
        have hnat0 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
          Real.summable_one_div_nat_pow.2 (by norm_num)
        have h := (summable_nat_add_iff
          (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) (N + 1)).2 hnat0
        exact h.congr fun n => by push_cast; ring_nf
      exact hnat.mul_left _
    have hfsumN : Summable fun n : ℕ => f (n + N) := (summable_nat_add_iff N).2 hfsum
    have hle := Summable.tsum_le_tsum hbound hfsumN hsum2
    have hgeo : ∑' n : ℕ, (1 : ℝ) / (((n : ℝ)) + N + 1) ^ 2 ≤ 1 / (N : ℝ) :=
      tsum_inv_sq_shift_le N hN
    have : ∑' n : ℕ, M ^ 2 / δ ^ 2 * ((1 : ℝ) / (((n : ℝ)) + N + 1) ^ 2)
        ≤ M ^ 2 / δ ^ 2 * (1 / (N : ℝ)) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left hgeo (by positivity)
    have hfin : M ^ 2 / δ ^ 2 * (1 / (N : ℝ)) = M ^ 2 / (δ ^ 2 * N) := by
      field_simp
    linarith [hle, this, hfin.le, hfin.ge]
  linarith [hsplit, hhead, htail]

/-- **Linear-in-offset mixed-interference envelope.**

Balancing the split of the two-regime envelope at `N = ⌈1/y⌉` gives an envelope
which is *linear* in the transverse offset `y`:

  `∑_n (Im Φ(w n))² ≤ y (8 M₁² + M²/δ²)`.

Since the coercive transverse defect is *quadratic* in the offset, this proves
that at the level of the second moment the interference envelope obtained from
horizontal decay plus vertical Lipschitz continuity alone is `O(α)` while the
defect is `Θ(α²)`: the envelope does not, by itself, beat the defect as
`α → 0`. -/
theorem mixedInterference_envelope_linear {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hR : 0 ≤ R) {δ y : ℝ} (hδ : 0 < δ) (hy0 : 0 < y)
    (hy1 : y ≤ 1) (hyR : y * R ≤ 1) (w : ℕ → ℂ)
    (hre : ∀ n : ℕ, δ * ((n : ℝ) + 1) ≤ |(w n).re|)
    (him : ∀ n : ℕ, |(w n).im| ≤ y) :
    ∑' n : ℕ, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ y * (8 * momentMass (fun t => φ t ^ 2) ^ 2 + kernelMass φ ^ 2 / δ ^ 2) := by
  set M := kernelMass φ with hM
  set M₁ := momentMass (fun t => φ t ^ 2) with hM₁
  have hM0 : 0 ≤ M := kernelMass_nonneg φ
  have hM₁0 : 0 ≤ M₁ := momentMass_nonneg _
  set N : ℕ := ⌈1 / y⌉₊ with hNdef
  have hinvpos : (0 : ℝ) < 1 / y := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by
    simp only [hNdef, ne_eq, Nat.ceil_eq_zero, not_le]
    exact hinvpos)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNle : (1 : ℝ) / y ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < 1 / y + 1 := Nat.ceil_lt_add_one hinvpos.le
  have hkey := mixedInterference_envelope_transverse hφ hev hR hδ hy1 hyR w hre him hN1
  have hhead : 4 * (N : ℝ) * y ^ 2 * M₁ ^ 2 ≤ 8 * y * M₁ ^ 2 := by
    have hy2 : y ^ 2 ≤ y := by nlinarith
    have h3 : (N : ℝ) * y ^ 2 ≤ (1 / y + 1) * y ^ 2 := by
      have hsq : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
      nlinarith
    have h4 : (1 / y + 1) * y ^ 2 = y + y ^ 2 := by field_simp
    have h5 : (N : ℝ) * y ^ 2 ≤ 2 * y := by
      rw [h4] at h3
      linarith
    nlinarith [sq_nonneg M₁]
  have htail : M ^ 2 / (δ ^ 2 * N) ≤ y * (M ^ 2 / δ ^ 2) := by
    have hinvN : 1 / (N : ℝ) ≤ y := by
      rw [div_le_iff₀ hNR]
      have : (1 : ℝ) / y * y ≤ N * y := by
        exact mul_le_mul_of_nonneg_right hNle hy0.le
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hy0)] at this
      linarith
    have heq : M ^ 2 / (δ ^ 2 * N) = M ^ 2 / δ ^ 2 * (1 / (N : ℝ)) := by field_simp
    rw [heq]
    have hc : (0 : ℝ) ≤ M ^ 2 / δ ^ 2 := by positivity
    calc M ^ 2 / δ ^ 2 * (1 / (N : ℝ)) ≤ M ^ 2 / δ ^ 2 * y :=
          mul_le_mul_of_nonneg_left hinvN hc
      _ = y * (M ^ 2 / δ ^ 2) := by ring
  have : y * (8 * M₁ ^ 2 + M ^ 2 / δ ^ 2) = 8 * y * M₁ ^ 2 + y * (M ^ 2 / δ ^ 2) := by ring
  linarith [hkey, hhead, htail]

end RiemannAnalytic
