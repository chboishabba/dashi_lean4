/-
Complex bilinear Poisson extension for a real even compactly supported taper.

This file proves, at literal analytic strength, the *complex-parameter*
extension of the bilinear Poisson identity:

  `∑_{k ∈ ℤ} φ̂(z - k h) φ̂(w - k h) = L · Φ(z - w)`,  `h = 2π/L`,

for **arbitrary complex** `z, w`, where `φ̂ = PhiExt φ` is the complex bilinear
(Fourier--Laplace) extension of a `C¹` taper `φ` supported in `[-R, R]` with
`2R ≤ L`, and `Φ = PhiExt (φ²)`.

The proof is the "complexified `G`-proof": the auxiliary function is the
convolution `K = (φ e^{-iz·}) ⋆ (φ e^{-iw·})`, whose Fourier transform
factorises as the product of the two shifted extensions and which is supported
in `[-2R, 2R] ⊆ [-L, L]`; Poisson summation for the rescaled kernel `x ↦ K(Lx)`
then has a single surviving term on the space side.

Specialising `w = conj z` gives the Hermitian identity

  `∑_k ‖φ̂(z - k h)‖² = L · Φ(z - conj z)`,

and for `z = γ - iα` this is exactly `∑_k ‖φ̂(γ - iα - k h)‖² = L · Φ(-2iα)`.
Combined with `RiemannAnalytic.TaperCoercivity` this yields the explicit
transverse-energy floor `(9/128) L⁴ α²` (see `transverseEnergy_floor`).
-/
import RiemannAnalytic.TaperCoercivity

namespace RiemannAnalytic

open MeasureTheory Convolution ContinuousLinearMap Complex Real FourierTransform

/-! ### `C¹` tapers -/

/-- A `C¹` taper of radius `R`: differentiable with continuous derivative and
vanishing outside `[-R, R]`. -/
structure C1Taper (φ : ℝ → ℝ) (R : ℝ) : Prop where
  diff : Differentiable ℝ φ
  contDeriv : Continuous (deriv φ)
  supp : ∀ t, R < |t| → φ t = 0

namespace C1Taper

variable {φ : ℝ → ℝ} {R : ℝ}

theorem cont (hφ : C1Taper φ R) : Continuous φ := hφ.diff.continuous

/-- A `C¹` taper is in particular a compact taper in the sense of
`RiemannAnalytic.CompactTaper`. -/
theorem toCompactTaper (hφ : C1Taper φ R) : CompactTaper φ R :=
  ⟨hφ.cont, hφ.supp⟩

theorem derivSupp (hφ : C1Taper φ R) : ∀ t, R < |t| → deriv φ t = 0 := by
  intro t ht
  have hnhds : ∀ᶠ s in nhds t, φ s = 0 := by
    have hopen : IsOpen {s : ℝ | R < |s|} := isOpen_lt continuous_const continuous_abs
    exact Filter.eventually_of_mem (hopen.mem_nhds ht) fun s hs => hφ.supp s hs
  have : deriv φ t = deriv (fun _ : ℝ => (0 : ℝ)) t := Filter.EventuallyEq.deriv_eq hnhds
  simpa using this

end C1Taper

/-! ### The twisted taper -/

/-- The taper twisted by a complex frequency: `u ↦ φ(u) e^{-i z u}`.  Its
integral is `PhiExt φ z`. -/
noncomputable def twist (φ : ℝ → ℝ) (z : ℂ) : ℝ → ℂ :=
  fun u => (φ u : ℂ) * Complex.exp (-(Complex.I * z * (u : ℂ)))

theorem integral_twist (φ : ℝ → ℝ) (z : ℂ) : ∫ u : ℝ, twist φ z u = PhiExt φ z := rfl

theorem twist_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (z : ℂ) :
    Continuous (twist φ z) := by
  unfold twist
  fun_prop

theorem twist_eq_zero {φ : ℝ → ℝ} {R : ℝ} (hsupp : ∀ t, R < |t| → φ t = 0) (z : ℂ)
    {u : ℝ} (hu : R < |u|) : twist φ z u = 0 := by
  simp [twist, hsupp u hu]

theorem twist_hasCompactSupport {φ : ℝ → ℝ} {R : ℝ} (hsupp : ∀ t, R < |t| → φ t = 0)
    (z : ℂ) : HasCompactSupport (twist φ z) := by
  refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun x hx => ?_
  refine twist_eq_zero hsupp z ?_
  by_contra hcon
  exact hx (Set.mem_Icc.2 ⟨by cases abs_le.1 (not_lt.1 hcon) with | intro h1 _ => linarith,
    by cases abs_le.1 (not_lt.1 hcon) with | intro _ h2 => linarith⟩)

theorem twist_integrable {φ : ℝ → ℝ} {R : ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t, R < |t| → φ t = 0) (z : ℂ) : Integrable (twist φ z) :=
  (twist_continuous hφ z).integrable_of_hasCompactSupport (twist_hasCompactSupport hsupp z)

/-- The Fourier transform of the twisted taper is the extension shifted by the
real frequency. -/
theorem fourier_twist {φ : ℝ → ℝ} (z : ℂ) (ξ : ℝ) :
    𝓕 (twist φ z) ξ = PhiExt φ (z + 2 * Real.pi * ξ) := by
  rw [Real.fourier_real_eq]
  unfold PhiExt twist
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show (𝐞 (-(v * ξ))) • ((φ v : ℂ) * Complex.exp (-(Complex.I * z * (v : ℂ))))
      = (φ v : ℂ) * Complex.exp (-(Complex.I * (z + 2 * Real.pi * ξ) * (v : ℂ)))
  rw [show ((𝐞 (-(v * ξ))) • ((φ v : ℂ) * Complex.exp (-(Complex.I * z * (v : ℂ)))))
      = Complex.exp ((2 * Real.pi * (-(v * ξ)) : ℝ) * Complex.I)
        * ((φ v : ℂ) * Complex.exp (-(Complex.I * z * (v : ℂ)))) by
    simp [Real.fourierChar_apply, Circle.smul_def]]
  have hcomb : Complex.exp ((2 * Real.pi * (-(v * ξ)) : ℝ) * Complex.I)
        * ((φ v : ℂ) * Complex.exp (-(Complex.I * z * (v : ℂ))))
      = (φ v : ℂ) * Complex.exp (((2 * Real.pi * (-(v * ξ)) : ℝ) * Complex.I)
          + (-(Complex.I * z * (v : ℂ)))) := by
    rw [Complex.exp_add]; ring
  rw [hcomb]
  congr 1
  push_cast
  ring_nf

/-! ### The convolution kernel -/

/-- The auxiliary convolution kernel `K = (φ e^{-iz·}) ⋆ (φ e^{-iw·})`. -/
noncomputable def convKernel (φ : ℝ → ℝ) (z w : ℂ) : ℝ → ℂ :=
  (twist φ z) ⋆[mul ℂ ℂ] (twist φ w)

theorem convKernel_apply (φ : ℝ → ℝ) (z w : ℂ) (s : ℝ) :
    convKernel φ z w s = ∫ t : ℝ, twist φ z t * twist φ w (s - t) := by
  unfold convKernel
  rw [convolution_def]
  simp

/-- **Factorisation of the Fourier transform of the kernel.** -/
theorem fourier_convKernel {φ : ℝ → ℝ} {R : ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t, R < |t| → φ t = 0) (z w : ℂ) (ξ : ℝ) :
    𝓕 (convKernel φ z w) ξ
      = PhiExt φ (z + 2 * Real.pi * ξ) * PhiExt φ (w + 2 * Real.pi * ξ) := by
  unfold convKernel
  rw [Real.fourier_mul_convolution_eq (twist_integrable hφ hsupp z)
    (twist_integrable hφ hsupp w) (twist_continuous hφ z) (twist_continuous hφ w) ξ,
    fourier_twist, fourier_twist]

/-- The kernel is continuous. -/
theorem convKernel_continuous {φ : ℝ → ℝ} {R : ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t, R < |t| → φ t = 0) (z w : ℂ) : Continuous (convKernel φ z w) :=
  HasCompactSupport.continuous_convolution_right _ (twist_hasCompactSupport hsupp w)
    (twist_integrable hφ hsupp z).locallyIntegrable (twist_continuous hφ w)

/-- **The kernel vanishes at and beyond twice the taper radius.** -/
theorem convKernel_eq_zero {φ : ℝ → ℝ} {R : ℝ} (hsupp : ∀ t, R < |t| → φ t = 0)
    (z w : ℂ) {s : ℝ} (hs : 2 * R ≤ |s|) : convKernel φ z w s = 0 := by
  rw [convKernel_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (s / 2))] with t ht
  have htne : t ≠ s / 2 := ht
  by_cases h1 : R < |t|
  · simp [twist_eq_zero hsupp z h1]
  · by_cases h2 : R < |s - t|
    · simp [twist_eq_zero hsupp w h2]
    · exfalso
      push_neg at h1 h2
      apply htne
      rcases abs_cases s with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩ <;>
        rcases abs_cases t with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩ <;>
          rcases abs_cases (s - t) with ⟨hst1, hst2⟩ | ⟨hst1, hst2⟩ <;>
            rw [hs1] at hs <;> rw [ht1] at h1 <;> rw [hst1] at h2 <;> linarith

/-- The kernel has compact support. -/
theorem convKernel_hasCompactSupport {φ : ℝ → ℝ} {R : ℝ}
    (hsupp : ∀ t, R < |t| → φ t = 0) (z w : ℂ) :
    HasCompactSupport (convKernel φ z w) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(2 * R)) (2 * R)) isCompact_Icc fun x hx => ?_
  refine convKernel_eq_zero hsupp z w ?_
  by_contra hcon
  push_neg at hcon
  exact hx (Set.mem_Icc.2 ⟨by cases abs_lt.1 hcon with | intro h1 _ => linarith,
    by cases abs_lt.1 hcon with | intro _ h2 => linarith⟩)

/-- **Value of the kernel at the origin:** for an even taper it is the
extension of `φ²` at the difference of the two frequencies. -/
theorem convKernel_zero {φ : ℝ → ℝ} (hev : ∀ t, φ (-t) = φ t) (z w : ℂ) :
    convKernel φ z w 0 = PhiExt (fun t => φ t ^ 2) (z - w) := by
  rw [convKernel_apply]
  unfold PhiExt twist
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hφt : φ (0 - t) = φ t := by
    rw [zero_sub, hev t]
  show (φ t : ℂ) * Complex.exp (-(Complex.I * z * (t : ℂ)))
        * ((φ (0 - t) : ℂ) * Complex.exp (-(Complex.I * w * ((0 - t : ℝ) : ℂ))))
      = ((φ t ^ 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (z - w) * (t : ℂ)))
  rw [hφt]
  have hcomb : (φ t : ℂ) * Complex.exp (-(Complex.I * z * (t : ℂ)))
        * ((φ t : ℂ) * Complex.exp (-(Complex.I * w * ((0 - t : ℝ) : ℂ))))
      = ((φ t : ℂ) * (φ t : ℂ))
        * Complex.exp ((-(Complex.I * z * (t : ℂ)))
            + (-(Complex.I * w * ((0 - t : ℝ) : ℂ)))) := by
    rw [Complex.exp_add]; ring
  rw [hcomb]
  push_cast
  ring_nf

/-! ### Decay of the extension along horizontal lines -/

/-- Pointwise modulus of the twisted taper. -/
theorem norm_twist (φ : ℝ → ℝ) (z : ℂ) (u : ℝ) :
    ‖twist φ z u‖ = |φ u| * Real.exp (z.im * u) := by
  unfold twist
  rw [norm_mul, Complex.norm_real, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Trivial modulus bound for the extension. -/
theorem norm_PhiExt_le (φ : ℝ → ℝ) (z : ℂ) :
    ‖PhiExt φ z‖ ≤ ∫ u : ℝ, |φ u| * Real.exp (z.im * u) := by
  have h := norm_integral_le_integral_norm (μ := volume) (f := twist φ z)
  rw [integral_twist] at h
  refine h.trans (le_of_eq ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => norm_twist φ z u)

/-- **Integration by parts for the complex extension:**
`∫ φ' e^{-izu} du = i z ∫ φ e^{-izu} du`. -/
theorem PhiExt_deriv {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (z : ℂ) :
    PhiExt (deriv φ) z = Complex.I * z * PhiExt φ z := by
  have hder : ∀ u : ℝ, HasDerivAt (twist φ z)
      (twist (deriv φ) z u - Complex.I * z * twist φ z u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => ((φ u : ℝ) : ℂ)) (((deriv φ u : ℝ) : ℂ)) u :=
      ((hφ.diff u).hasDerivAt).ofReal_comp
    have h2 : HasDerivAt (fun u : ℝ => -(Complex.I * z * (u : ℂ))) (-(Complex.I * z)) u := by
      have h0 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa using ((h0.const_mul (Complex.I * z)).neg)
    have h4 := h1.mul h2.cexp
    unfold twist
    convert h4 using 1
    ring
  have hint1 : Integrable (twist φ z) := twist_integrable hφ.cont hφ.supp z
  have hintd : Integrable (twist (deriv φ) z) :=
    twist_integrable hφ.contDeriv hφ.derivSupp z
  have hint2 : Integrable (fun u : ℝ => twist (deriv φ) z u - Complex.I * z * twist φ z u) :=
    hintd.sub (hint1.const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hder hint2 hint1
  rw [integral_sub hintd (hint1.const_mul _), integral_const_mul, integral_twist,
    integral_twist] at h0
  linear_combination h0

/-- **Horizontal decay of the complex extension of a `C¹` taper.**  The modulus
of the extension times the distance to the imaginary axis is bounded by the
`L¹` mass of the twisted derivative. -/
theorem norm_PhiExt_mul_abs_re_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (z : ℂ) :
    ‖PhiExt φ z‖ * |z.re| ≤ ∫ u : ℝ, |deriv φ u| * Real.exp (z.im * u) := by
  have hd := PhiExt_deriv hφ z
  have hnorm : ‖PhiExt (deriv φ) z‖ = ‖z‖ * ‖PhiExt φ z‖ := by
    rw [hd, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hpos : 0 ≤ ‖PhiExt φ z‖ := norm_nonneg _
  have hstep : ‖PhiExt φ z‖ * |z.re| ≤ ‖PhiExt (deriv φ) z‖ := by
    rw [hnorm]
    nlinarith
  exact hstep.trans (norm_PhiExt_le (deriv φ) z)

/-! ### Summability along the grid -/

/-- A ratio-free comparison test: a two-sided sequence whose modulus times a
product of two linearly growing factors stays bounded is summable. -/
theorem summable_of_grid_decay {F : ℤ → ℂ} {C p q hs : ℝ} (hh : 0 < hs)
    (hb : ∀ n : ℤ, ‖F n‖ * (|p + n * hs| * |q + n * hs|) ≤ C) :
    Summable F := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((|p| + |q|) / hs + 1)
  have hNp : |p| < ((N : ℝ) - 1) * hs := by
    have h1 : (|p| + |q|) / hs + 1 < N := hN
    have h2 : (|p| + |q|) / hs < (N : ℝ) - 1 := by linarith
    have h3 : |p| + |q| < ((N : ℝ) - 1) * hs := by
      rw [div_lt_iff₀ hh] at h2
      linarith
    have : 0 ≤ |q| := abs_nonneg q
    linarith
  have hNq : |q| < ((N : ℝ) - 1) * hs := by
    have h1 : (|p| + |q|) / hs + 1 < N := hN
    have h2 : (|p| + |q|) / hs < (N : ℝ) - 1 := by linarith
    have h3 : |p| + |q| < ((N : ℝ) - 1) * hs := by
      rw [div_lt_iff₀ hh] at h2
      linarith
    have : 0 ≤ |p| := abs_nonneg p
    linarith
  -- lower bound for the two linear factors on the shifted grid
  have hfactor : ∀ (r : ℝ) (n : ℝ), |r| < ((N : ℝ) - 1) * hs → 0 ≤ n →
      ((n : ℝ) + 1) * hs ≤ |r + (n + N) * hs| ∧ ((n : ℝ) + 1) * hs ≤ |r - (n + N) * hs| := by
    intro r n hr hn
    have hrle : -(((N : ℝ) - 1) * hs) < r := (abs_lt.1 hr).1
    have hrge : r < ((N : ℝ) - 1) * hs := lt_of_le_of_lt (le_abs_self r) hr
    constructor
    · have : (n + 1) * hs ≤ r + (n + N) * hs := by nlinarith
      exact le_trans this (le_abs_self _)
    · have : (n + 1) * hs ≤ -(r - (n + N) * hs) := by nlinarith
      exact le_trans this (neg_le_abs _)
  -- the summable majorant
  have hmaj : Summable fun n : ℕ => C / hs ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hbase : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
      have h2 := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      refine ((summable_nat_add_iff 1).2 h2).congr fun n => ?_
      push_cast
      ring_nf
    exact hbase.mul_left _
  have hpos2 : (0 : ℝ) < hs ^ 2 := by positivity
  -- the two half-series
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
      Summable fun n : ℕ => F (ε * ((n : ℤ) + (N : ℤ))) := by
    intro ε hε
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmaj)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hbn := hb (ε * ((n : ℤ) + (N : ℤ)))
    have hgen : ∀ r : ℝ, |r| < ((N : ℝ) - 1) * hs →
        ((n : ℝ) + 1) * hs ≤ |r + ((ε * ((n : ℤ) + (N : ℤ)) : ℤ) : ℝ) * hs| := by
      intro r hr
      have hf := hfactor r n hr hn0
      rcases hε with rfl | rfl
      · have hc : ((1 * ((n : ℤ) + (N : ℤ)) : ℤ) : ℝ) = (n : ℝ) + (N : ℝ) := by
          push_cast; ring
        rw [hc]
        exact hf.1
      · have hc : (((-1) * ((n : ℤ) + (N : ℤ)) : ℤ) : ℝ) * hs
            = -(((n : ℝ) + (N : ℝ)) * hs) := by push_cast; ring
        rw [hc, ← sub_eq_add_neg]
        exact hf.2
    have h1 : 0 ≤ ((n : ℝ) + 1) * hs := by positivity
    have hlow : ((n : ℝ) + 1) * hs * (((n : ℝ) + 1) * hs)
        ≤ |p + ((ε * ((n : ℤ) + (N : ℤ)) : ℤ) : ℝ) * hs|
          * |q + ((ε * ((n : ℤ) + (N : ℤ)) : ℤ) : ℝ) * hs| :=
      mul_le_mul (hgen p hNp) (hgen q hNq) h1 (le_trans h1 (hgen p hNp))
    have hFnn : 0 ≤ ‖F (ε * ((n : ℤ) + (N : ℤ)))‖ := norm_nonneg _
    have hprod : ‖F (ε * ((n : ℤ) + (N : ℤ)))‖ * (((n : ℝ) + 1) * hs * (((n : ℝ) + 1) * hs))
        ≤ C := le_trans (by nlinarith) hbn
    have hden : (0 : ℝ) < ((n : ℝ) + 1) * hs * (((n : ℝ) + 1) * hs) := by positivity
    rw [← le_div_iff₀ hden] at hprod
    refine le_trans hprod (le_of_eq ?_)
    field_simp
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  have hpos : Summable fun n : ℕ => F ((n : ℤ)) := by
    refine (summable_nat_add_iff N).1 ?_
    refine h1.congr fun n => ?_
    congr 1
    push_cast
    ring
  have hneg : Summable fun n : ℕ => F (-(n : ℤ)) := by
    refine (summable_nat_add_iff N).1 ?_
    refine h2.congr fun n => ?_
    congr 1
    push_cast
    ring
  exact Summable.of_nat_of_neg hpos hneg

/-- **Summability of the complex grid product.**  For a `C¹` taper and any two
complex frequencies, the bilinear grid products are absolutely summable. -/
theorem summable_grid_product {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {hs : ℝ}
    (hh : 0 < hs) (z w : ℂ) :
    Summable fun n : ℤ => PhiExt φ (z + (n : ℝ) * hs) * PhiExt φ (w + (n : ℝ) * hs) := by
  set Cz := ∫ u : ℝ, |deriv φ u| * Real.exp (z.im * u) with hCz
  set Cw := ∫ u : ℝ, |deriv φ u| * Real.exp (w.im * u) with hCw
  have hCz0 : 0 ≤ Cz := integral_nonneg fun u => by positivity
  have hCw0 : 0 ≤ Cw := integral_nonneg fun u => by positivity
  refine summable_of_grid_decay (C := Cz * Cw) (p := z.re) (q := w.re) hh fun n => ?_
  have hzre : (z + (n : ℝ) * hs).re = z.re + (n : ℝ) * hs := by simp
  have hzim : (z + (n : ℝ) * hs).im = z.im := by simp
  have hwre : (w + (n : ℝ) * hs).re = w.re + (n : ℝ) * hs := by simp
  have hwim : (w + (n : ℝ) * hs).im = w.im := by simp
  have h1 := norm_PhiExt_mul_abs_re_le hφ (z + (n : ℝ) * hs)
  have h2 := norm_PhiExt_mul_abs_re_le hφ (w + (n : ℝ) * hs)
  rw [hzre, hzim] at h1
  rw [hwre, hwim] at h2
  rw [← hCz] at h1
  rw [← hCw] at h2
  have hn1 : 0 ≤ ‖PhiExt φ (z + (n : ℝ) * hs)‖ * |z.re + (n : ℝ) * hs| := by positivity
  have hn2 : 0 ≤ ‖PhiExt φ (w + (n : ℝ) * hs)‖ * |w.re + (n : ℝ) * hs| := by positivity
  have hmul := mul_le_mul h1 h2 hn2 hCz0
  rw [norm_mul]
  calc ‖PhiExt φ (z + (n : ℝ) * hs)‖ * ‖PhiExt φ (w + (n : ℝ) * hs)‖
        * (|z.re + (n : ℝ) * hs| * |w.re + (n : ℝ) * hs|)
      = (‖PhiExt φ (z + (n : ℝ) * hs)‖ * |z.re + (n : ℝ) * hs|)
          * (‖PhiExt φ (w + (n : ℝ) * hs)‖ * |w.re + (n : ℝ) * hs|) := by ring
    _ ≤ Cz * Cw := hmul

/-! ### The complex bilinear Poisson identity -/

/-- **Complex bilinear Poisson extension.**

For a `C¹` real even taper supported in `[-R, R]` with `2R ≤ L`, and for
*arbitrary complex* frequencies `z, w`,

  `∑_{n ∈ ℤ} φ̂(z + n·2π/L) φ̂(w + n·2π/L) = L · Φ(z - w)`,

where `φ̂ = PhiExt φ` and `Φ = PhiExt (φ²)`. -/
theorem complex_bilinear_poisson {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (z w : ℂ) :
    ∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
        * PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L))
      = (L : ℂ) * PhiExt (fun t => φ t ^ 2) (z - w) := by
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
  set K := convKernel φ z w with hK
  set g : ℝ → ℂ := fun x => K (L * x) with hg
  have hKcont : Continuous K := convKernel_continuous hφ.cont hφ.supp z w
  have hgcont : Continuous g := hKcont.comp (by fun_prop)
  -- the rescaled kernel vanishes outside the unit interval
  have hgzero : ∀ x : ℝ, (1 : ℝ) ≤ |x| → g x = 0 := by
    intro x hx
    refine convKernel_eq_zero hφ.supp z w ?_
    rw [abs_mul, abs_of_pos hL]
    nlinarith
  have hgO : g =O[Filter.cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
    have h : g =ᶠ[Filter.cocompact ℝ] 0 := by
      refine Filter.eventually_of_mem
        (?_ : {x : ℝ | (1 : ℝ) ≤ |x|} ∈ Filter.cocompact ℝ) fun x hx => hgzero x hx
      rw [Filter.mem_cocompact]
      refine ⟨Set.Icc (-1) 1, isCompact_Icc, fun x hx => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      simp only [Set.mem_setOf_eq]
      rcases hx with h | h
      · calc (1 : ℝ) ≤ -x := by linarith
          _ ≤ |x| := neg_le_abs x
      · exact le_of_lt (lt_of_lt_of_le h (le_abs_self x))
    exact h.trans_isBigO (Asymptotics.isBigO_zero _ _)
  -- Fourier transform of the rescaled kernel
  have hfg : ∀ ξ : ℝ, 𝓕 g ξ
      = ((L : ℂ))⁻¹ * (PhiExt φ (z + 2 * Real.pi * (ξ / L)) * PhiExt φ (w + 2 * Real.pi * (ξ / L))) := by
    intro ξ
    have hstep : 𝓕 g ξ = (|L⁻¹| : ℝ) • 𝓕 K (ξ / L) := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq]
      have hpt : ∀ x : ℝ, (𝐞 (-(x * ξ))) • g x
          = (fun y : ℝ => (𝐞 (-(y * (ξ / L)))) • K y) (L * x) := by
        intro x
        simp only [hg]
        congr 2
        field_simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        Measure.integral_comp_mul_left (fun y : ℝ => (𝐞 (-(y * (ξ / L)))) • K y) L]
    rw [hstep, fourier_convKernel hφ.cont hφ.supp z w (ξ / L)]
    rw [abs_of_pos (inv_pos.2 hL)]
    simp only [Complex.real_smul]
    push_cast
    ring
  -- summability of the Fourier coefficients along ℤ
  have hsummable : Summable fun n : ℤ => 𝓕 g (n : ℝ) := by
    have hbase := summable_grid_product hφ (hs := 2 * Real.pi / L)
      (by positivity) z w
    refine (hbase.mul_left ((L : ℂ))⁻¹).congr fun n => ?_
    rw [hfg]
    congr 2 <;> · congr 1; push_cast; ring
  -- Poisson summation
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgcont
    (b := 2) one_lt_two hgO hsummable 0
  -- the space side has a single surviving term
  have hspace : ∑' n : ℤ, g (0 + (n : ℝ)) = K 0 := by
    have hsingle : ∀ n : ℤ, n ≠ 0 → g (0 + (n : ℝ)) = 0 := by
      intro n hn
      refine hgzero _ ?_
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
      simpa using h1
    calc ∑' n : ℤ, g (0 + (n : ℝ)) = g (0 + ((0 : ℤ) : ℝ)) := tsum_eq_single 0 hsingle
      _ = K 0 := by simp [hg]
  -- the frequency side is the grid sum
  have hone : ∀ n : ℤ, (_root_.fourier n) (((0 : ℝ) : UnitAddCircle)) = 1 := by
    intro n
    simp
  have hfreq : ∑' n : ℤ, 𝓕 g (n : ℝ) * (_root_.fourier n) (((0 : ℝ) : UnitAddCircle))
      = ((L : ℂ))⁻¹ * ∑' n : ℤ, PhiExt φ (z + (n : ℝ) * (2 * Real.pi / L))
          * PhiExt φ (w + (n : ℝ) * (2 * Real.pi / L)) := by
    simp only [hone, mul_one]
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hfg]
    congr 2 <;> · congr 1; push_cast; ring
  rw [hspace, hfreq] at hpois
  have hK0 : K 0 = PhiExt (fun t => φ t ^ 2) (z - w) := convKernel_zero hev z w
  rw [hK0] at hpois
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hLne
  rw [hpois]
  exact (mul_inv_cancel_left₀ hLc _).symm

end RiemannAnalytic
