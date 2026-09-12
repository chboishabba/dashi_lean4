import RiemannAnalytic.SubexponentialTaperGate

/-!
# Spectral valleys of compactly supported tapers: the top-window floor is false

`compactTaper_gate_verdict` (in `RiemannAnalytic/SubexponentialTaperGate.lean`)
closes the source-normalization gate for a compactly supported taper `ψ` in two
regimes, but its red branch carries one hypothesis that G16 left unexamined: a
**pointwise floor**

```
κ_φ · exp (-(r * u))  ≤  taperTransformAbs ψ u      for every u in the top window
                                                    [log N - log 4, log N].
```

This module decides whether that hypothesis can be assumed for free.  It cannot:

* `valleyTaper_fourier` — the transform of `t ↦ φ t - (φ (t-s) + φ (t+s))/2`
  is `(1 - cos (2π s ξ)) · 𝓕φ(ξ)`, so it vanishes at every `ξ ∈ (1/s)ℤ`;
* `valleyCounterTaper` — the explicit compactly supported plateau taper
  obtained from the trapezoid with `s = 2`; its transform vanishes on the
  half-integers, hence in **every** window of length `log 4`;
* `compactTaper_topWindowFloor_counterexample` — consequently there is a
  compactly supported taper, equal to `1` on a plateau, for which the pointwise
  top-window floor fails at every height `R`, for every rate `r` and every
  constant `κ > 0`.

So the universal pointwise floor is **false**, and the no-go argument cannot be
completed in that form.  What survives is the integrated (`L²`) statement, which
is proved here:

* `compactTaper_fourier_ne_zero_on_interval` — the transform of a compactly
  supported, somewhere nonzero taper cannot vanish identically on any nonempty
  open interval (a Paley–Wiener rigidity statement, proved from the analytic
  extension of `TaperAnalyticIncompatibility.lean`);
* `spectralWindowMass` and `compactTaper_spectralWindowMass_pos` — hence every
  spectral window carries *positive* `L²` mass.

Finally, the source-parameter (aperture) freedom is enough to select a frequency
scale at which the prime side is not spectrally blind:

* `exists_aperture_with_positive_spectral_mass` — for every compactly supported,
  somewhere nonzero taper and every frequency `u₀ > 0` there is an aperture
  `λ ∈ (0,1)` with `𝓕ψ(λ u₀) ≠ 0`;
* `exists_aperture_primeWindow_spectral_mass` — the version carrying a whole
  weighted prime-frequency sum.

What is **not** proved: any *quantitative* lower bound (`exp (-o(R))` or
otherwise) for the window mass, uniformly in the height, and therefore no
unconditional no-go theorem for the compact-taper gate.  Nothing here proves,
or assumes, the Riemann Hypothesis.
-/

namespace RiemannAnalytic

open MeasureTheory Real Set Complex ArithmeticFunction

/-! ### Translation and the valley construction -/

/-- Translation turns into a phase factor under the Fourier transform.  No
integrability hypothesis is needed: both sides are `0` when the integral does
not converge, and the change of variables is measure preserving. -/
theorem fourier_shift (f : ℝ → ℂ) (s w : ℝ) :
    FourierTransform.fourier (fun t => f (t - s)) w
      = Complex.exp ((-2 * π * s * w : ℝ) * Complex.I) * FourierTransform.fourier f w := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun v : ℝ => Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v - s)) s]
  rw [← MeasureTheory.integral_const_mul]
  congr 1 with v
  rw [add_sub_cancel_right, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The valley identity.**  Subtracting the mean of the two translates by `±s`
multiplies the transform by `1 - cos (2π s ξ)`, which vanishes on the lattice
`(1/s)ℤ`. -/
theorem fourier_valley (f : ℝ → ℂ) (hf : Integrable f) (s w : ℝ) :
    FourierTransform.fourier (fun t => f t - (f (t - s) + f (t + s)) / 2) w
      = ((1 : ℂ) - (Real.cos (2 * π * s * w) : ℝ)) * FourierTransform.fourier f w := by
  have hker : Continuous (fun v : ℝ => Complex.exp ((-2 * π * v * w : ℝ) * Complex.I)) := by
    fun_prop
  have hkerb : ∀ v : ℝ, ‖Complex.exp ((-2 * π * v * w : ℝ) * Complex.I)‖ = 1 := by
    intro v
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hint : ∀ g : ℝ → ℂ, Integrable g →
      Integrable (fun v : ℝ => Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * g v) := by
    intro g hg
    exact hg.bdd_mul hker.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (hkerb x))
  have h1 : Integrable (fun t => f (t - s)) := hf.comp_sub_right s
  have h2 : Integrable (fun t => f (t + s)) := hf.comp_add_right s
  have hFs := fourier_shift f s w
  have hFn := fourier_shift f (-s) w
  simp only [sub_neg_eq_add] at hFn
  have key : FourierTransform.fourier (fun t => f t - (f (t - s) + f (t + s)) / 2) w
      = FourierTransform.fourier f w
        - (FourierTransform.fourier (fun t => f (t - s)) w
            + FourierTransform.fourier (fun t => f (t + s)) w) / 2 := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    have e0 : ∀ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I)
          * (f v - (f (v - s) + f (v + s)) / 2)
        = Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f v
          - (Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v - s)
              + Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v + s)) / 2 := by
      intro v; ring
    calc ∫ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I)
            * (f v - (f (v - s) + f (v + s)) / 2)
        = ∫ v : ℝ, (Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f v
            - (Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v - s)
              + Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v + s)) / 2) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall e0)
      _ = (∫ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f v)
            - ∫ v : ℝ, (Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v - s)
              + Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v + s)) / 2 :=
          MeasureTheory.integral_sub (hint f hf) (((hint _ h1).add (hint _ h2)).div_const 2)
      _ = (∫ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f v)
            - ((∫ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v - s))
              + ∫ v : ℝ, Complex.exp ((-2 * π * v * w : ℝ) * Complex.I) * f (v + s)) / 2 := by
          rw [MeasureTheory.integral_div, MeasureTheory.integral_add (hint _ h1) (hint _ h2)]
  rw [key, hFs, hFn]
  have hcos : Complex.exp ((-2 * π * s * w : ℝ) * Complex.I)
      + Complex.exp ((-2 * π * (-s) * w : ℝ) * Complex.I)
      = 2 * (Real.cos (2 * π * s * w) : ℝ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  linear_combination (-(FourierTransform.fourier f w) / 2) * hcos

/-! ### The compact tapers themselves -/

/-- The trapezoidal plateau taper: `1` on `|t| ≤ 1/2`, `0` outside `|t| ≤ 1`. -/
noncomputable def plateauBase : ℝ → ℝ := fun t => min 1 (max 0 (2 - 2 * |t|))

theorem plateauBase_continuous : Continuous plateauBase := by
  unfold plateauBase; fun_prop

theorem plateauBase_eq_zero {t : ℝ} (ht : 1 < |t|) : plateauBase t = 0 := by
  have h : max 0 (2 - 2 * |t|) = 0 := max_eq_left (by linarith)
  simp [plateauBase, h]

theorem plateauBase_eq_one {t : ℝ} (ht : |t| ≤ 1 / 2) : plateauBase t = 1 := by
  have h : (1 : ℝ) ≤ max 0 (2 - 2 * |t|) := le_max_of_le_right (by linarith)
  simp [plateauBase, min_eq_left h]

theorem compactTaper_plateauBase : CompactTaper plateauBase 1 :=
  ⟨plateauBase_continuous, fun _ ht => plateauBase_eq_zero ht⟩

/-- The valley modification of a taper: subtract the mean of its translates by
`±s`. -/
noncomputable def valleyTaper (φ : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun t => φ t - (φ (t - s) + φ (t + s)) / 2

theorem compactTaper_valleyTaper {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) (s : ℝ) :
    CompactTaper (valleyTaper φ s) (R + |s|) := by
  refine ⟨?_, ?_⟩
  · unfold valleyTaper
    exact hφ.cont.sub (((hφ.cont.comp (continuous_id.sub continuous_const)).add
      (hφ.cont.comp (continuous_id.add continuous_const))).div_const 2)
  · intro t ht
    have h0 : R < |t| := lt_of_le_of_lt (by linarith [abs_nonneg s]) ht
    have h1 : R < |t - s| := by
      have : |t| - |s| ≤ |t - s| := by
        have := abs_sub_abs_le_abs_sub t s
        linarith
      linarith
    have h2 : R < |t + s| := by
      have : |t| - |s| ≤ |t + s| := by
        have := abs_sub_abs_le_abs_sub t (-s)
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
      linarith
    simp [valleyTaper, hφ.supp t h0, hφ.supp _ h1, hφ.supp _ h2]

/-- The valley modification keeps the plateau, provided the translation distance
clears the support. -/
theorem valleyTaper_plateau {φ : ℝ → ℝ} {R a s : ℝ} (hφ : CompactTaper φ R)
    (hplat : ∀ t, |t| ≤ a → φ t = 1) (hs : R + a < |s|) {t : ℝ} (ht : |t| ≤ a) :
    valleyTaper φ s t = 1 := by
  have h1 : R < |t - s| := by
    have : |s| - |t| ≤ |t - s| := by
      have := abs_sub_abs_le_abs_sub s t
      rw [abs_sub_comm s t] at this
      linarith
    linarith
  have h2 : R < |t + s| := by
    have : |s| - |t| ≤ |t + s| := by
      have h := abs_sub_abs_le_abs_sub s (-t)
      rw [sub_neg_eq_add, abs_neg, add_comm] at h
      linarith
    linarith
  simp [valleyTaper, hplat t ht, hφ.supp _ h1, hφ.supp _ h2]

/-- **The counterexample taper**: the trapezoid with its translates by `±2`
subtracted off.  It is continuous, supported in `|t| ≤ 3`, equal to `1` on the
plateau `|t| ≤ 1/2`, and its Fourier transform vanishes at every half-integer. -/
noncomputable def valleyCounterTaper : ℝ → ℝ := valleyTaper plateauBase 2

theorem compactTaper_valleyCounterTaper : CompactTaper valleyCounterTaper 3 := by
  have h := compactTaper_valleyTaper compactTaper_plateauBase 2
  have h2 : (1 : ℝ) + |(2 : ℝ)| = 3 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [h2] at h
  exact h

theorem valleyCounterTaper_plateau {t : ℝ} (ht : |t| ≤ 1 / 2) : valleyCounterTaper t = 1 :=
  valleyTaper_plateau compactTaper_plateauBase (fun _ h => plateauBase_eq_one h)
    (by rw [show |(2 : ℝ)| = 2 from abs_of_nonneg (by norm_num)]; norm_num) ht

/-! ### The transform of the counterexample taper vanishes in every window -/

theorem integrable_ofReal_of_compactTaper {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) :
    Integrable (fun u => (φ u : ℂ)) volume := by
  have hcont : Continuous (fun u => (φ u : ℂ)) := Complex.continuous_ofReal.comp hφ.cont
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-|R| - 1) (|R| + 1)) isCompact_Icc ?_
  intro x hx
  have hR : R < |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have habs : |R| + 1 < |x| := by
      rcases hx with h | h
      · have h1 : |R| + 1 < -x := by linarith
        exact lt_of_lt_of_le h1 (neg_le_abs x)
      · exact lt_of_lt_of_le h (le_abs_self x)
    exact lt_of_le_of_lt (le_abs_self R) (by linarith)
  simp [hφ.supp x hR]

/-- The Fourier transform of the valley taper, in the `taperTransformAbs`
normalization. -/
theorem taperTransformAbs_valleyTaper {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) (s w : ℝ) :
    taperTransformAbs (valleyTaper φ s) w
      = |1 - Real.cos (2 * π * s * w)| * taperTransformAbs φ w := by
  have hcast : (fun t => ((valleyTaper φ s t : ℝ) : ℂ))
      = fun t => (φ t : ℂ) - ((φ (t - s) : ℂ) + (φ (t + s) : ℂ)) / 2 := by
    funext t
    simp only [valleyTaper]
    push_cast
    ring
  unfold taperTransformAbs
  rw [hcast, fourier_valley _ (integrable_ofReal_of_compactTaper hφ) s w, norm_mul]
  congr 1
  rw [show ((1 : ℂ) - (Real.cos (2 * π * s * w) : ℝ))
      = ((1 - Real.cos (2 * π * s * w) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_real _

/-- At every half-integer the transform of the counterexample taper vanishes. -/
theorem taperTransformAbs_valleyCounterTaper_halfInt (k : ℤ) :
    taperTransformAbs valleyCounterTaper ((k : ℝ) / 2) = 0 := by
  rw [valleyCounterTaper, taperTransformAbs_valleyTaper compactTaper_plateauBase]
  have : 2 * π * 2 * ((k : ℝ) / 2) = (k : ℝ) * (2 * π) := by ring
  rw [this, Real.cos_int_mul_two_pi]
  simp

/-- Every window of length `log 4` contains a half-integer. -/
theorem exists_halfInt_mem_topWindow (R : ℝ) :
    ∃ k : ℤ, R - Real.log 4 ≤ (k : ℝ) / 2 ∧ (k : ℝ) / 2 ≤ R := by
  refine ⟨⌊2 * R⌋, ?_, ?_⟩
  · have h1 : 2 * R - 1 < (⌊2 * R⌋ : ℝ) := by
      have := Int.sub_one_lt_floor (2 * R)
      linarith
    have hlog : (1 : ℝ) / 2 ≤ Real.log 4 := by
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      rw [this]; linarith
    linarith
  · have := Int.floor_le (2 * R)
    linarith

/-- **The counterexample.**  There is a compactly supported taper, equal to `1`
on the plateau `|t| ≤ 1/2` required by the source-side Gram floor, whose
transform vanishes somewhere in *every* top window `[R - log 4, R]`.  Hence the
pointwise floor hypothesis of `compactTaper_gate_verdict` fails for it, at every
height, for every rate and every positive constant. -/
theorem compactTaper_topWindowFloor_counterexample :
    CompactTaper valleyCounterTaper 3
      ∧ (∀ t, |t| ≤ 1 / 2 → valleyCounterTaper t = 1)
      ∧ (∀ R : ℝ, ∃ u : ℝ, R - Real.log 4 ≤ u ∧ u ≤ R
            ∧ taperTransformAbs valleyCounterTaper u = 0)
      ∧ (∀ R r κ : ℝ, 0 < κ →
          ¬ (∀ u : ℝ, R - Real.log 4 ≤ u → u ≤ R →
              κ * Real.exp (-(r * u)) ≤ taperTransformAbs valleyCounterTaper u)) := by
  refine ⟨compactTaper_valleyCounterTaper, fun t ht => valleyCounterTaper_plateau ht, ?_, ?_⟩
  · intro R
    obtain ⟨k, hk1, hk2⟩ := exists_halfInt_mem_topWindow R
    exact ⟨(k : ℝ) / 2, hk1, hk2, taperTransformAbs_valleyCounterTaper_halfInt k⟩
  · intro R r κ hκ hfloor
    obtain ⟨k, hk1, hk2⟩ := exists_halfInt_mem_topWindow R
    have h := hfloor ((k : ℝ) / 2) hk1 hk2
    rw [taperTransformAbs_valleyCounterTaper_halfInt k] at h
    have : 0 < κ * Real.exp (-(r * ((k : ℝ) / 2))) := by positivity
    linarith

/-! ### Rigidity: no window is spectrally void -/

/-- **The mirror Paley–Wiener step.**  If a continuous integrable function
decays exponentially, then its Fourier transform is the restriction of a
function analytic on a strip; so if that transform vanishes on a nonempty open
interval of frequencies, the function itself vanishes identically. -/
theorem eq_zero_of_expDecay_of_fourier_vanishing_interval {g : ℝ → ℂ}
    (hcont : Continuous g) (hint : Integrable g volume) {C a : ℝ} (ha : 0 < a)
    (hbd : ∀ v, ‖g v‖ ≤ C * Real.exp (-(a * |v|)))
    {c d : ℝ} (hcd : c < d) (hzero : ∀ ξ ∈ Ioo c d, FourierTransform.fourier g ξ = 0) :
    ∀ x, g x = 0 := by
  have hpi : 0 < π := Real.pi_pos
  set b : ℝ := a / (4 * π) with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  have hab : 2 * π * b < a := by
    rw [hb_def]
    have h : 2 * π * (a / (4 * π)) = a / 2 := by field_simp; ring
    rw [h]; linarith
  have hana : AnalyticOnNhd ℂ (invFourierExt g) (expStrip b) :=
    analyticOnNhd_invFourierExt hab hcont.aestronglyMeasurable hbd
  have hreal : ∀ x : ℝ, invFourierExt g (x : ℂ) = FourierTransform.fourier g (-x) := by
    intro x
    rw [invFourierExt_ofReal, Real.fourierInv_eq_fourier_neg]
  -- the extension vanishes on the reflected interval
  set p : ℝ := -((c + d) / 2) with hp_def
  have hpmem : p ∈ Ioo (-d) (-c) := by
    constructor <;> · rw [hp_def]; linarith
  have hz₀ : ((p : ℂ)) ∈ expStrip b := ofReal_mem_expStrip hb p
  have htend : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhdsWithin p {p}ᶜ)
      (nhdsWithin (p : ℂ) {(p : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.tendsto p |>.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using fun h => hx (by exact_mod_cast h)
  have hfreqReal : ∃ᶠ x : ℝ in nhdsWithin p {p}ᶜ, invFourierExt g (x : ℂ) = 0 := by
    have hev : ∀ᶠ x : ℝ in nhdsWithin p {p}ᶜ, invFourierExt g (x : ℂ) = 0 := by
      have hmem : Ioo (-d) (-c) ∈ nhdsWithin p ({p}ᶜ : Set ℝ) :=
        nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hpmem)
      filter_upwards [hmem] with x hx
      rw [hreal x]
      exact hzero (-x) ⟨by simpa using neg_lt_neg hx.2, by simpa using neg_lt_neg hx.1⟩
    exact hev.frequently
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin (p : ℂ) {(p : ℂ)}ᶜ, invFourierExt g z = 0 :=
    htend.frequently hfreqReal
  have hEq : Set.EqOn (invFourierExt g) 0 (expStrip b) :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_expStrip b) hz₀ hfreq
  -- hence the transform vanishes everywhere, and inversion kills `g`
  have hFzero : FourierTransform.fourier g = fun _ => (0 : ℂ) := by
    funext ξ
    have h := hEq (ofReal_mem_expStrip hb (-ξ))
    rw [hreal (-ξ)] at h
    simpa using h
  have hgint : Integrable (FourierTransform.fourier g) volume := by
    rw [hFzero]; exact integrable_zero _ _ _
  have hinv := hcont.fourierInv_fourier_eq hint hgint
  rw [hFzero] at hinv
  intro x
  rw [← hinv]
  simp [Real.fourierInv_eq]

/-- A compactly supported continuous function obeys every exponential decay
bound, with a suitable constant. -/
theorem compactTaper_expDecay_bound {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) :
    ∃ C : ℝ, ∀ v : ℝ, ‖(φ v : ℂ)‖ ≤ C * Real.exp (-(1 * |v|)) := by
  have hcont : Continuous (fun u => (φ u : ℂ)) := Complex.continuous_ofReal.comp hφ.cont
  have hsupp : HasCompactSupport (fun u => (φ u : ℂ)) := by
    refine HasCompactSupport.intro (K := Set.Icc (-|R| - 1) (|R| + 1)) isCompact_Icc ?_
    intro x hx
    have hR : R < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      have habs : |R| + 1 < |x| := by
        rcases hx with h | h
        · have h1 : |R| + 1 < -x := by linarith
          exact lt_of_lt_of_le h1 (neg_le_abs x)
        · exact lt_of_lt_of_le h (le_abs_self x)
      exact lt_of_le_of_lt (le_abs_self R) (by linarith)
    simp [hφ.supp x hR]
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hcont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨M * Real.exp (|R| + 1), fun v => ?_⟩
  by_cases hv : |v| ≤ |R| + 1
  · have h1 : Real.exp (|R| + 1) * Real.exp (-(1 * |v|)) ≥ 1 := by
      rw [← Real.exp_add]
      have : (0 : ℝ) ≤ |R| + 1 + -(1 * |v|) := by linarith
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (|R| + 1 + -(1 * |v|)) := Real.exp_le_exp.mpr this
    calc ‖(φ v : ℂ)‖ ≤ M := hM v
      _ = M * 1 := by ring
      _ ≤ M * (Real.exp (|R| + 1) * Real.exp (-(1 * |v|))) :=
          mul_le_mul_of_nonneg_left h1 hM0
      _ = M * Real.exp (|R| + 1) * Real.exp (-(1 * |v|)) := by ring
  · push_neg at hv
    have hR : R < |v| := lt_of_le_of_lt (le_abs_self R) (by linarith)
    rw [hφ.supp v hR]
    simp only [Complex.ofReal_zero, norm_zero]
    positivity

/-- **Spectral rigidity of the compact taper class.**  The Fourier transform of
a compactly supported, somewhere nonzero taper cannot vanish identically on any
nonempty open interval of frequencies: however deep the valleys, no window is
spectrally void. -/
theorem compactTaper_fourier_ne_zero_on_interval {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) {c d : ℝ} (hcd : c < d) :
    ∃ ξ ∈ Ioo c d, taperTransformAbs φ ξ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hC⟩ := compactTaper_expDecay_bound hφ
  have hcont : Continuous (fun u => (φ u : ℂ)) := Complex.continuous_ofReal.comp hφ.cont
  have hint := integrable_ofReal_of_compactTaper hφ
  have hzero : ∀ ξ ∈ Ioo c d, FourierTransform.fourier (fun u => (φ u : ℂ)) ξ = 0 := by
    intro ξ hξ
    have := hcon ξ hξ
    rwa [taperTransformAbs, norm_eq_zero] at this
  have := eq_zero_of_expDecay_of_fourier_vanishing_interval hcont hint one_pos hC hcd hzero x₀
  exact hx₀ (by exact_mod_cast this)

/-! ### The integrated window mass -/

/-- The `L²` mass carried by the transform of a taper on the frequency window
`(c, d)` — the quantity the prime side of the explicit formula actually sees,
as opposed to a pointwise value. -/
noncomputable def spectralWindowMass (φ : ℝ → ℝ) (c d : ℝ) : ℝ :=
  ∫ ξ in Ioo c d, (taperTransformAbs φ ξ) ^ 2

theorem continuous_taperTransformAbs {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) :
    Continuous (taperTransformAbs φ) := by
  have hint := integrable_ofReal_of_compactTaper hφ
  have hF : Continuous (FourierTransform.fourier (fun u => (φ u : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hint
  exact hF.norm

/-- **Every spectral window carries positive mass.**  This is the integrated
replacement for the (false) pointwise floor: for a compactly supported,
somewhere nonzero taper the `L²` mass of the transform on any nonempty window is
strictly positive — the valleys are never wide enough to empty a window. -/
theorem compactTaper_spectralWindowMass_pos {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) {c d : ℝ} (hcd : c < d) :
    0 < spectralWindowMass φ c d := by
  obtain ⟨ξ₀, hξ₀, hne⟩ := compactTaper_fourier_ne_zero_on_interval hφ hx₀ hcd
  have hcontF : Continuous (fun ξ => (taperTransformAbs φ ξ) ^ 2) :=
    (continuous_taperTransformAbs hφ).pow 2
  have hint : IntegrableOn (fun ξ => (taperTransformAbs φ ξ) ^ 2) (Ioo c d) volume :=
    (hcontF.continuousOn.integrableOn_Icc (a := c) (b := d)).mono_set Ioo_subset_Icc_self
  have hnn : ∀ ξ : ℝ, 0 ≤ (taperTransformAbs φ ξ) ^ 2 := fun ξ => sq_nonneg _
  rw [spectralWindowMass,
    setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint]
  have hopen : IsOpen (Function.support (fun ξ => (taperTransformAbs φ ξ) ^ 2) ∩ Ioo c d) :=
    hcontF.isOpen_support.inter isOpen_Ioo
  refine hopen.measure_pos volume ⟨ξ₀, ?_, hξ₀⟩
  simpa [Function.mem_support] using hne

/-! ### Aperture selection -/

/-- **The aperture freedom defeats the valleys.**  For a compactly supported,
somewhere nonzero taper and any positive frequency `u₀`, there is an aperture
`λ ∈ (0,1)` at which the transform does not vanish.  (In the source family
`L = λ log (T/2π)`, `λ` is exactly the free Fourier scale.) -/
theorem exists_aperture_with_positive_spectral_mass {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ taperTransformAbs φ (lam * u₀) ≠ 0 := by
  obtain ⟨ξ, hξ, hne⟩ := compactTaper_fourier_ne_zero_on_interval hφ hx₀ hu₀
  refine ⟨ξ / u₀, div_pos hξ.1 hu₀, (div_lt_one hu₀).mpr hξ.2, ?_⟩
  rwa [div_mul_cancel₀ _ (ne_of_gt hu₀)]

/-- **The aperture-selected prime-frequency mass is positive.**  For any finite
set of integer frequencies with nonnegative weights, one of which is a genuine
frequency (`n₀ > 1`) with positive weight, some admissible aperture
`λ ∈ (0,1)` makes the weighted prime-frequency spectral sum strictly positive.
This is the qualitative form of the aperture-selection statement: it shows the
prime side is never spectrally blind for a suitable `λ`.  It carries **no**
quantitative scale, and therefore does not by itself feed the contraction
gate. -/
theorem exists_aperture_primeWindow_spectral_mass {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n)
    {n₀ : ℕ} (hn₀ : n₀ ∈ S) (hn₀one : 1 < n₀) (hw₀ : 0 < w n₀) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
      0 < ∑ n ∈ S, w n * (taperTransformAbs φ (lam * Real.log n)) ^ 2 := by
  have hu₀ : 0 < Real.log n₀ := Real.log_pos (by exact_mod_cast hn₀one)
  obtain ⟨lam, hlam0, hlam1, hne⟩ := exists_aperture_with_positive_spectral_mass hφ hx₀ hu₀
  refine ⟨lam, hlam0, hlam1, Finset.sum_pos' (fun n hn => ?_) ⟨n₀, hn₀, ?_⟩⟩
  · exact mul_nonneg (hw n hn) (sq_nonneg _)
  · exact mul_pos hw₀ (by positivity)

/-! ### Valleys cannot be deep at every height -/

/-- For a real taper the transform modulus is even. -/
theorem taperTransformAbs_neg (φ : ℝ → ℝ) (ξ : ℝ) :
    taperTransformAbs φ (-ξ) = taperTransformAbs φ ξ := by
  have key : FourierTransform.fourier (fun u => (φ u : ℂ)) (-ξ)
      = (starRingEnd ℂ) (FourierTransform.fourier (fun u => (φ u : ℂ)) ξ) := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    rw [← integral_conj]
    congr 1 with v
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    · congr 1
      simp [Complex.ext_iff]
    · simp
  unfold taperTransformAbs
  rw [key, RCLike.norm_conj]

/-- **No taper has exponentially deep valleys at every height.**  If the window
supremum of the transform were smaller than `C e^{-aR}` for *all* heights
`R ≥ R₀`, the transform would obey a global exponential bound, which
`compactTaper_fourier_not_expDecay` forbids for a compactly supported taper.

So the spectral-valley loophole, if it exists at all, is necessarily *sparse* in
the height: at any fixed exponential rate there are arbitrarily large heights at
which the top window is **not** that small.  (This does not exclude deep valleys
along a thin sequence of heights.) -/
theorem compactTaper_topWindow_not_uniformly_expSmall {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ¬ ∃ C a R₀ : ℝ, 0 < a ∧
        ∀ S : ℝ, R₀ ≤ S → ∀ ξ : ℝ, S - Δ ≤ ξ → ξ ≤ S →
          taperTransformAbs φ ξ ≤ C * Real.exp (-(a * S)) := by
  rintro ⟨C, a, R₀, ha, hsmall⟩
  refine compactTaper_fourier_not_expDecay hφ hx₀ ?_
  -- the uniform window bound upgrades to a global exponential bound
  set M : ℝ := ∫ v : ℝ, ‖(φ v : ℂ)‖ with hM_def
  have hM0 : 0 ≤ M := by
    rw [hM_def]
    exact integral_nonneg fun v => norm_nonneg _
  have hMbd : ∀ ξ : ℝ, taperTransformAbs φ ξ ≤ M :=
    fun ξ => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  refine ⟨max C (M * Real.exp (a * |R₀|)), a, ha, fun ξ => ?_⟩
  have hkey : ∀ η : ℝ, 0 ≤ η →
      taperTransformAbs φ η ≤ max C (M * Real.exp (a * |R₀|)) * Real.exp (-(a * η)) := by
    intro η hη0
    have hexp : 0 < Real.exp (-(a * η)) := Real.exp_pos _
    by_cases h : R₀ ≤ η
    · have := hsmall η h η (by linarith) le_rfl
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hexp.le
    · push_neg at h
      have hηR : η ≤ |R₀| := le_trans h.le (le_abs_self R₀)
      have h1 : M * Real.exp (a * η) ≤ M * Real.exp (a * |R₀|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hηR ha.le)) hM0
      have h2 : M ≤ M * Real.exp (a * |R₀|) * Real.exp (-(a * η)) := by
        have hsplit : M * Real.exp (a * η) * Real.exp (-(a * η)) = M := by
          rw [mul_assoc, ← Real.exp_add]
          simp
        calc M = M * Real.exp (a * η) * Real.exp (-(a * η)) := hsplit.symm
          _ ≤ M * Real.exp (a * |R₀|) * Real.exp (-(a * η)) :=
              mul_le_mul_of_nonneg_right h1 hexp.le
      refine (hMbd η).trans (h2.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hexp.le
  rcases le_or_gt 0 ξ with h | h
  · rw [abs_of_nonneg h]
    exact hkey ξ h
  · rw [abs_of_neg h]
    have hneg := hkey (-ξ) (by linarith)
    rw [taperTransformAbs_neg] at hneg
    exact hneg

/-- **Positive form**: at every exponential rate the top window is large at
arbitrarily great heights. -/
theorem compactTaper_topWindow_sup_large_frequently {φ : ℝ → ℝ} {R : ℝ}
    (hφ : CompactTaper φ R) {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (C a R₀ : ℝ) (ha : 0 < a) :
    ∃ S : ℝ, R₀ ≤ S ∧ ∃ ξ : ℝ, S - Δ ≤ ξ ∧ ξ ≤ S ∧
      C * Real.exp (-(a * S)) < taperTransformAbs φ ξ := by
  by_contra hcon
  push_neg at hcon
  exact compactTaper_topWindow_not_uniformly_expSmall hφ hx₀ hΔ ⟨C, a, R₀, ha, hcon⟩

/-! ### A valley-tolerant replacement for the pointwise gate hypothesis -/

/-- The gate computation, isolated from the hypothesis that produced the mass
bound.  Whatever the taper, a lower bound `κ'/4 · N^{1/2-r}` for the tapered
Weil mass with a subcritical rate `r < 1/2` defeats the contraction condition,
subject only to the explicit constant comparison. -/
theorem taperedWeil_gate_fails_of_mass_lower {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {phi : ℝ → ℝ} {α t c κ κ' Csrc r : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hr : r < 1 / 2)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hlow : κ' / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ taperedWeilMass phi N α)
    (hκ' : 0 < κ')
    (hthr : c * (((A : ℝ) + 4) / (1 - 2 * r)) ^ (A + 4)
      ≤ 120000 * (κ * κ' ^ 2 * t ^ 2 / 16)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (taperedWeilMass phi N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set P : ℝ := taperedWeilMass phi N α with hP
  have hsq : ((N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 = (N : ℝ) ^ (1 - 2 * r : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 - r : ℝ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hPsq : κ' ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ) ≤ P ^ 2 := by
    have h0 : (0 : ℝ) ≤ κ' / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
      have := Real.rpow_pos_of_pos hN0 (1 / 2 - r : ℝ)
      positivity
    have hmono : (κ' / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 ≤ P ^ 2 := by
      nlinarith [hlow, h0]
    calc κ' ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)
        = (κ' / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 := by rw [mul_pow, hsq]; ring
      _ ≤ P ^ 2 := hmono
  refine gate_fails_of_power_gain (A := A) (δ := 1 - 2 * r) hN hc (by linarith) ?_ hthr
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h1 : κ * (κ' ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)) ≤ κ * P ^ 2 :=
    mul_le_mul_of_nonneg_left hPsq hκ.le
  have h2 : κ * P ^ 2 ≤ Csrc * (Real.log N) ^ A * P ^ 2 :=
    mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
  calc κ * κ' ^ 2 * t ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)
      = κ * (κ' ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)) * t ^ 2 := by ring
    _ ≤ Csrc * (Real.log N) ^ A * P ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) ht2
    _ = Csrc * (Real.log N) ^ A * (t ^ 2 * P ^ 2) := by ring

/-- **The valley-tolerant mass bound.**  The taper transform need not stay above
`κ e^{-ru}` on the *whole* top window: it is enough that it does so on a set of
prime frequencies carrying a proportion `θ` of the Chebyshev block mass of
`(N/4, N]`.  Valleys are then harmless as long as they do not swallow that
proportion. -/
theorem taperedWeilMass_lower_of_valleyFreeSubset {phi : ℝ → ℝ} {N : ℕ} {α r κ θ : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (T : Finset ℕ) (hT : T ⊆ Finset.Ioc (N / 4) N)
    (hmass : θ * ((N : ℝ) / 4) ≤ ∑ n ∈ T, Λ n)
    (hphi : ∀ n ∈ T, κ * Real.exp (-(r * Real.log n)) ≤ |phi (Real.log n)|) :
    θ * κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ taperedWeilMass phi N α := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hsubIcc : T ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp (hT hn)
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by omega), h2⟩
  have hsplit : (N : ℝ) ^ (-(1/2) - r : ℝ) = (N : ℝ) ^ (-(1/2) : ℝ) * (N : ℝ) ^ (-r) := by
    rw [← Real.rpow_add hN0, show (-(1/2) : ℝ) + (-r) = -(1/2) - r by ring]
  have hexpN : Real.exp (-(r * Real.log N)) = (N : ℝ) ^ (-r) := by
    rw [Real.rpow_def_of_pos hN0]; congr 1; ring
  have hterm : ∀ n ∈ T,
      Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) ≤ weilWeight α n * |phi (Real.log n)| := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp (hT hn)
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    have hlogle : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN
    have htap : κ * Real.exp (-(r * Real.log N)) ≤ |phi (Real.log n)| := by
      refine le_trans ?_ (hphi n hn)
      have hmono : Real.exp (-(r * Real.log N)) ≤ Real.exp (-(r * Real.log n)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_le_mul_of_nonneg_left hlogle hr]
      exact mul_le_mul_of_nonneg_left hmono hκ
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hw : Λ n * (N : ℝ) ^ (-(1/2) : ℝ) ≤ weilWeight α n := by
      unfold weilWeight
      have hcosh : (1 : ℝ) ≤ Real.cosh (2 * α * Real.log n) := Real.one_le_cosh _
      have hrp : (N : ℝ) ^ (-(1/2) : ℝ) ≤ (n : ℝ) ^ (-(1/2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hn0 hnN (by norm_num)
      have h3 : (0:ℝ) ≤ (n:ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg hn0.le _
      nlinarith [mul_le_mul_of_nonneg_left hrp hΛ, mul_nonneg hΛ h3]
    have h0 : (0:ℝ) ≤ Λ n * (N : ℝ) ^ (-(1/2) : ℝ) :=
      mul_nonneg hΛ (Real.rpow_nonneg hN0.le _)
    have h1' : (0:ℝ) ≤ κ * Real.exp (-(r * Real.log N)) := by positivity
    calc Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
        = (Λ n * (N : ℝ) ^ (-(1/2) : ℝ)) * (κ * Real.exp (-(r * Real.log N))) := by
          rw [hexpN, hsplit]; ring
      _ ≤ weilWeight α n * |phi (Real.log n)| :=
          mul_le_mul hw htap h1' (le_trans h0 hw)
  have hstep1 : ∑ n ∈ T, Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      ≤ taperedWeilMass phi N α := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    unfold taperedWeilMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubIcc
      (fun n _ _ => mul_nonneg (weilWeight_nonneg α n) (abs_nonneg _))
  have hfactor : ∑ n ∈ T, Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      = (∑ n ∈ T, Λ n) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) := by
    rw [Finset.sum_mul]
  have hpos : (0:ℝ) ≤ κ * (N : ℝ) ^ (-(1/2) - r : ℝ) := by positivity
  have hlow : θ * ((N : ℝ) / 4) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      ≤ (∑ n ∈ T, Λ n) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) :=
    mul_le_mul_of_nonneg_right hmass hpos
  have hcomb : θ * ((N : ℝ) / 4) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      = θ * κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
    have h1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    calc θ * ((N : ℝ) / 4) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
        = θ * κ / 4 * ((N : ℝ) ^ (1:ℝ) * (N : ℝ) ^ (-(1/2) - r : ℝ)) := by rw [← h1]; ring
      _ = θ * κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  rw [← hcomb]
  exact le_trans hlow (hfactor ▸ hstep1)

/-- **The valley-tolerant red verdict.**  This is the repaired form of the
second half of `compactTaper_gate_verdict`: the pointwise floor on the whole top
window — which `compactTaper_topWindowFloor_counterexample` shows cannot be
assumed — is replaced by a floor on a set of prime frequencies carrying a
proportion `θ` of the Chebyshev block mass.  Under that weaker hypothesis the
contraction condition still fails. -/
theorem taperedWeil_gate_fails_of_valleyFreeSubset {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {phi : ℝ → ℝ} {α t c κ κphi Csrc r θ : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hκphi : 0 < κphi) (hθ : 0 < θ) (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (T : Finset ℕ) (hT : T ⊆ Finset.Ioc (N / 4) N)
    (hmass : θ * ((N : ℝ) / 4) ≤ ∑ n ∈ T, Λ n)
    (hphi : ∀ n ∈ T, κphi * Real.exp (-(r * Real.log n)) ≤ |phi (Real.log n)|)
    (hthr : c * (((A : ℝ) + 4) / (1 - 2 * r)) ^ (A + 4)
      ≤ 120000 * (κ * (θ * κphi) ^ 2 * t ^ 2 / 16)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (taperedWeilMass phi N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hlow := taperedWeilMass_lower_of_valleyFreeSubset (α := α) hN hκphi.le hr0 T hT hmass hphi
  have hlow' : (θ * κphi) / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ taperedWeilMass phi N α := by
    calc (θ * κphi) / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ)
        = θ * κphi / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by ring
      _ ≤ taperedWeilMass phi N α := hlow
  exact taperedWeil_gate_fails_of_mass_lower hN hc hκ hr hCsrc hlow' (mul_pos hθ hκphi) hthr

/-! ### The packaged answer -/

/-- **Counterexample or rigidity, decided.**  For the compactly supported
plateau taper class:

1. the *pointwise* top-window floor is **false** — there is a compactly
   supported taper with the plateau `ψ ≡ 1` on `|t| ≤ 1/2` whose transform
   vanishes somewhere in every window `[R - log 4, R]`, so no bound
   `κ e^{-r u} ≤ |𝓕ψ(u)|` can hold on such a window;
2. the *integrated* floor is **true qualitatively** — for every compactly
   supported, somewhere nonzero taper, every nonempty frequency window carries
   strictly positive `L²` mass.

The pointwise hypothesis of `compactTaper_gate_verdict` therefore cannot be
assumed for free, and the unconditional no-go verdict must be routed through the
integrated mass.  No quantitative lower bound for that mass is proved here. -/
theorem compactTaper_topWindowFloor_counterexampleOrRigidity :
    (∀ R r κ : ℝ, 0 < κ →
        ¬ (∀ u : ℝ, R - Real.log 4 ≤ u → u ≤ R →
            κ * Real.exp (-(r * u)) ≤ taperTransformAbs valleyCounterTaper u))
      ∧ (∀ (φ : ℝ → ℝ) (R : ℝ), CompactTaper φ R → (∃ x₀, φ x₀ ≠ 0) →
          ∀ c d : ℝ, c < d → 0 < spectralWindowMass φ c d)
      ∧ (∀ (φ : ℝ → ℝ) (R : ℝ), CompactTaper φ R → (∃ x₀, φ x₀ ≠ 0) →
          ∀ C a R₀ : ℝ, 0 < a → ∃ S : ℝ, R₀ ≤ S ∧ ∃ ξ : ℝ,
            S - Real.log 4 ≤ ξ ∧ ξ ≤ S ∧ C * Real.exp (-(a * S)) < taperTransformAbs φ ξ) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  refine ⟨(compactTaper_topWindowFloor_counterexample).2.2.2, ?_, ?_⟩
  · rintro φ R hφ ⟨x₀, hx₀⟩ c d hcd
    exact compactTaper_spectralWindowMass_pos hφ hx₀ hcd
  · rintro φ R hφ ⟨x₀, hx₀⟩ C a R₀ ha
    exact compactTaper_topWindow_sup_large_frequently hφ hx₀ hlog4 C a R₀ ha

end RiemannAnalytic
