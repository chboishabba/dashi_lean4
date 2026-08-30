import RiemannAnalytic.TaperCoercivity

/-!
# Compactly supported tapers cannot have exponentially decaying transforms

The G15 source-normalization analysis (`RiemannAnalytic/SourceCoefficient.lean`)
localized the binary gate of the anchored second-moment route as follows.  The
gate fails — the route is *red* — for every taper whose transform decays only
polynomially along the prime frequencies `u = log n`
(`taperedWeil_gate_fails_of_polyDecay`); the only remaining possibility for a
green gate is a taper whose transform decays **exponentially**, at a rate
exceeding `1/2 + 2|α|`, i.e. a taper extending analytically to a horizontal
strip.  The G15 report recorded, as an assessment rather than a theorem, that
such a taper is incompatible with the compact-support/plateau hypotheses under
which `finiteGridGramDefect_source_floor` establishes the `L⁶` Gram floor.

This module proves that incompatibility.  It is a Paley–Wiener-type statement,
proved here from scratch (Mathlib has the Fourier inversion theorem, but not
this consequence of it):

* `expStrip` — the open horizontal strip `{z : |Im z| < b}`, with `isOpen_expStrip`,
  `convex_expStrip`, `isPreconnected_expStrip`;
* `invFourierExt` — the complex extension `z ↦ ∫ g(v) e^{2πi v z} dv` of the
  inverse Fourier transform of `g`;
* `differentiableOn_invFourierExt` / `analyticOnNhd_invFourierExt` — if
  `‖g v‖ ≤ C e^{-a|v|}` then this extension is holomorphic, hence analytic, on
  every strip of half-width `b` with `2πb < a`;
* `eq_zero_of_expDecay_fourier_of_vanishing_interval` — **the Paley–Wiener
  step**: a continuous integrable `φ : ℝ → ℂ` whose Fourier transform is
  bounded by `C e^{-a|ξ|}` with `a > 0`, and which vanishes on *some* nonempty
  open interval, vanishes identically;
* `not_expDecay_fourier_of_vanishing_interval` — the contrapositive form: a
  function that vanishes on an interval but is somewhere nonzero has no
  exponentially decaying transform;
* `compactTaper_fourier_not_expDecay` — the statement for the taper class of
  this tree: a `CompactTaper φ R` which is not identically zero (in particular
  one satisfying the plateau hypothesis `φ t = 1` for `|t| ≤ a` of
  `finiteGridGramDefect_source_floor`) has **no** exponentially decaying
  Fourier transform, at any rate;
* `plateau_taper_fourier_not_expDecay` — the same statement phrased directly in
  the plateau normalization used by the Gram floor.

Consequence for the programme: the one class of tapers left open by the G15
verdict — those with exponentially decaying transforms — is disjoint from the
class for which the source-side `L⁶` floor is proved.  Nothing here proves the
Riemann Hypothesis, and nothing here is assumed elsewhere.
-/

namespace RiemannAnalytic

open MeasureTheory Real Set Complex

/-! ### The strip and its topology -/

/-- The open horizontal strip of half-width `b` in `ℂ`. -/
def expStrip (b : ℝ) : Set ℂ := {z : ℂ | |z.im| < b}

theorem mem_expStrip {b : ℝ} {z : ℂ} : z ∈ expStrip b ↔ |z.im| < b := Iff.rfl

theorem isOpen_expStrip (b : ℝ) : IsOpen (expStrip b) := by
  have h : Continuous fun z : ℂ => |z.im| := by fun_prop
  simpa [expStrip, Set.preimage, Iio] using isOpen_lt h continuous_const

theorem convex_expStrip (b : ℝ) : Convex ℝ (expStrip b) := by
  intro x hx y hy s t hs ht hst
  simp only [expStrip, Set.mem_setOf_eq] at *
  have him : (s • x + t • y).im = s * x.im + t * y.im := by simp
  rw [him]
  calc |s * x.im + t * y.im| ≤ |s * x.im| + |t * y.im| := abs_add_le _ _
    _ = s * |x.im| + t * |y.im| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < s * b + t * b := by
        rcases eq_or_lt_of_le hs with h | h
        · have h' : 0 < t := by rw [← h] at hst; linarith
          have e1 : s * |x.im| ≤ s * b := by rw [← h]; simp
          exact add_lt_add_of_le_of_lt e1 (mul_lt_mul_of_pos_left hy h')
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx h)
            (mul_le_mul_of_nonneg_left (le_of_lt hy) ht)
    _ = b := by rw [← add_mul, hst, one_mul]

theorem isPreconnected_expStrip (b : ℝ) : IsPreconnected (expStrip b) :=
  (convex_expStrip b).isPreconnected

theorem ofReal_mem_expStrip {b : ℝ} (hb : 0 < b) (x : ℝ) : (x : ℂ) ∈ expStrip b := by
  simpa [expStrip] using hb

/-! ### Two integrability facts about exponentially decaying weights -/

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => Real.exp (-(c * |v|))) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have h := (exp_neg_integrableOn_Ioi (0 : ℝ) hc).comp_neg
    rw [show (-Ioi (0 : ℝ)) = Iio 0 from by simp [neg_Ioi]] at h
    have h2 : IntegrableOn (fun v : ℝ => Real.exp (-(c * |v|))) (Iio 0) := by
      refine h.congr_fun ?_ measurableSet_Iio
      intro x hx
      simp [abs_of_neg (mem_Iio.mp hx)]
    have hs : Iic (0 : ℝ) = Iio 0 ∪ {0} := by ext x; simp [le_iff_lt_or_eq]
    rw [hs, integrableOn_union]
    exact ⟨h2, by simp [IntegrableOn, Measure.restrict_singleton]⟩
  · refine (exp_neg_integrableOn_Ioi (0 : ℝ) hc).congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (mem_Ioi.mp hx)]

private theorem abs_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (v : ℝ) :
    |v| * Real.exp (-(c * |v|)) ≤ (2 / c) * Real.exp (-((c / 2) * |v|)) := by
  have key : |v| * Real.exp (-((c / 2) * |v|)) ≤ 2 / c := by
    have h1 : (c / 2) * |v| ≤ Real.exp ((c / 2) * |v|) := by
      have := Real.add_one_le_exp ((c / 2) * |v|); linarith
    have h2 : 0 < Real.exp ((c / 2) * |v|) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ h2]
    calc |v| = (2 / c) * ((c / 2) * |v|) := by field_simp
      _ ≤ (2 / c) * Real.exp ((c / 2) * |v|) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsplit : Real.exp (-(c * |v|))
      = Real.exp (-((c / 2) * |v|)) * Real.exp (-((c / 2) * |v|)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right key (le_of_lt (Real.exp_pos _))

theorem integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => |v| * Real.exp (-(c * |v|))) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (by linarith : (0 : ℝ) < c / 2)).const_mul (2 / c))
    (by fun_prop) ?_
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact abs_mul_exp_neg_le hc v

/-! ### The holomorphic extension of an inverse Fourier transform -/

/-- The complex extension of the inverse Fourier transform of `g`. -/
noncomputable def invFourierExt (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ v : ℝ, Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v

theorem invFourierExt_ofReal (g : ℝ → ℂ) (x : ℝ) :
    invFourierExt g (x : ℂ) = FourierTransformInv.fourierInv g x := by
  rw [Real.fourierInv_eq']
  simp only [invFourierExt, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1
  ext v
  congr 2
  push_cast
  ring

private theorem norm_expKernel (v : ℝ) (z : ℂ) :
    ‖Complex.exp ((2 * π * v : ℝ) * z * Complex.I)‖ = Real.exp (-(2 * π * v * z.im)) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private theorem hasDerivAt_expKernel (v : ℝ) (z w : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * w)
      ((2 * π * v : ℝ) * Complex.I * Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * w) z := by
  have h1 : HasDerivAt (fun z : ℂ => ((2 * π * v : ℝ) : ℂ) * z * Complex.I)
      (((2 * π * v : ℝ) : ℂ) * Complex.I) z := by
    simpa using (((hasDerivAt_id z).const_mul ((2 * π * v : ℝ) : ℂ)).mul_const Complex.I)
  simpa [mul_comm, mul_assoc, mul_left_comm] using (h1.cexp.mul_const w)

/-- **Holomorphy of the extension.**  If `g` decays at exponential rate `a`, its
inverse-Fourier extension is holomorphic on every strip of half-width `b` with
`2πb < a`. -/
theorem differentiableOn_invFourierExt {g : ℝ → ℂ} {C a b : ℝ}
    (hab : 2 * π * b < a) (hg : AEStronglyMeasurable g volume)
    (hbd : ∀ v, ‖g v‖ ≤ C * Real.exp (-(a * |v|))) :
    DifferentiableOn ℂ (invFourierExt g) (expStrip b) := by
  have hpi : 0 < π := Real.pi_pos
  have hC : 0 ≤ C := by
    have := hbd 0
    simpa using le_trans (norm_nonneg _) this
  set c : ℝ := a - 2 * π * b with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  intro z₀ hz₀
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun v : ℝ => Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v) volume :=
    fun z => (Continuous.aestronglyMeasurable (by fun_prop)).mul hg
  have hnormker : ∀ (v : ℝ) (z : ℂ), z ∈ expStrip b →
      ‖Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v‖ ≤ C * Real.exp (-(c * |v|)) := by
    intro v z hz
    rw [norm_mul, norm_expKernel]
    have h1 : -(2 * π * v * z.im) ≤ 2 * π * b * |v| := by
      have h2 : |2 * π * v * z.im| ≤ 2 * π * b * |v| := by
        rw [abs_mul, abs_mul, abs_mul]
        have hzb : |z.im| ≤ b := le_of_lt hz
        have h3 : |(2 : ℝ)| * |π| = 2 * π := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (le_of_lt hpi)]
        calc |(2 : ℝ)| * |π| * |v| * |z.im| = (2 * π) * |v| * |z.im| := by rw [h3]
          _ ≤ (2 * π) * |v| * b := mul_le_mul_of_nonneg_left hzb (by positivity)
          _ = 2 * π * b * |v| := by ring
      calc -(2 * π * v * z.im) ≤ |2 * π * v * z.im| := neg_le_abs _
        _ ≤ 2 * π * b * |v| := h2
    calc Real.exp (-(2 * π * v * z.im)) * ‖g v‖
        ≤ Real.exp (2 * π * b * |v|) * (C * Real.exp (-(a * |v|))) :=
          mul_le_mul (Real.exp_le_exp.mpr h1) (hbd v) (norm_nonneg _)
            (le_of_lt (Real.exp_pos _))
      _ = C * (Real.exp (2 * π * b * |v|) * Real.exp (-(a * |v|))) := by ring
      _ = C * Real.exp (-(c * |v|)) := by
          rw [← Real.exp_add]; congr 1; rw [hc_def]; ring_nf
  have hint : ∀ z ∈ expStrip b, Integrable
      (fun v : ℝ => Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v) volume := by
    intro z hz
    refine Integrable.mono' ((integrable_exp_neg_mul_abs hc).const_mul C) (hmeas z) ?_
    filter_upwards with v using hnormker v z hz
  have hmeas' : AEStronglyMeasurable
      (fun v : ℝ => ((2 * π * v : ℝ) : ℂ) * Complex.I *
        Complex.exp ((2 * π * v : ℝ) * z₀ * Complex.I) * g v) volume :=
    (Continuous.aestronglyMeasurable (by fun_prop)).mul hg
  have hboundint : Integrable
      (fun v : ℝ => 2 * π * C * (|v| * Real.exp (-(c * |v|)))) volume :=
    (integrable_abs_mul_exp_neg_mul_abs hc).const_mul _
  have hderivbd : ∀ v : ℝ, ∀ z ∈ expStrip b,
      ‖((2 * π * v : ℝ) : ℂ) * Complex.I *
          Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v‖
        ≤ 2 * π * C * (|v| * Real.exp (-(c * |v|))) := by
    intro v z hz
    have hre : ((2 * π * v : ℝ) : ℂ) * Complex.I *
        Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v
        = ((2 * π * v : ℝ) : ℂ) * Complex.I *
          (Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v) := by ring
    rw [hre, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    have h2 : ‖(2 * π * v : ℝ)‖ = 2 * π * |v| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (le_of_lt hpi)]
    rw [h2]
    calc 2 * π * |v| * ‖Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v‖
        ≤ 2 * π * |v| * (C * Real.exp (-(c * |v|))) :=
          mul_le_mul_of_nonneg_left (hnormker v z hz) (by positivity)
      _ = 2 * π * C * (|v| * Real.exp (-(c * |v|))) := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun (z : ℂ) (v : ℝ) => Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v)
    (F' := fun (z : ℂ) (v : ℝ) => ((2 * π * v : ℝ) : ℂ) * Complex.I *
      Complex.exp ((2 * π * v : ℝ) * z * Complex.I) * g v)
    (x₀ := z₀) (s := expStrip b)
    (bound := fun v => 2 * π * C * (|v| * Real.exp (-(c * |v|))))
    ((isOpen_expStrip b).mem_nhds hz₀)
    (Filter.Eventually.of_forall (fun z => hmeas z))
    (hint z₀ hz₀) hmeas'
    (Filter.Eventually.of_forall (fun v z hz => hderivbd v z hz))
    hboundint
    (Filter.Eventually.of_forall (fun v z _ => hasDerivAt_expKernel v z (g v)))
  exact key.2.differentiableAt.differentiableWithinAt

theorem analyticOnNhd_invFourierExt {g : ℝ → ℂ} {C a b : ℝ}
    (hab : 2 * π * b < a) (hg : AEStronglyMeasurable g volume)
    (hbd : ∀ v, ‖g v‖ ≤ C * Real.exp (-(a * |v|))) :
    AnalyticOnNhd ℂ (invFourierExt g) (expStrip b) :=
  (differentiableOn_invFourierExt hab hg hbd).analyticOnNhd (isOpen_expStrip b)

/-! ### The Paley–Wiener step -/

/-- **A continuous integrable function with an exponentially decaying Fourier
transform that vanishes on a nonempty open interval vanishes identically.**

This is the analytic-continuation obstruction: exponential decay of the
transform forces the function to extend holomorphically to a strip, and a
holomorphic function vanishing on a real interval vanishes on the whole
(connected) strip. -/
theorem eq_zero_of_expDecay_fourier_of_vanishing_interval {φ : ℝ → ℂ}
    (hcont : Continuous φ) (hint : Integrable φ volume) {C a : ℝ} (ha : 0 < a)
    (hbd : ∀ ξ, ‖FourierTransform.fourier φ ξ‖ ≤ C * Real.exp (-(a * |ξ|)))
    {c d : ℝ} (hcd : c < d) (hzero : ∀ x ∈ Ioo c d, φ x = 0) :
    ∀ x, φ x = 0 := by
  have hpi : 0 < π := Real.pi_pos
  set g : ℝ → ℂ := FourierTransform.fourier φ with hg_def
  have hgcont : Continuous g := by
    rw [hg_def]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hint
  have hgint : Integrable g volume := by
    refine Integrable.mono' ((integrable_exp_neg_mul_abs ha).const_mul C)
      hgcont.aestronglyMeasurable ?_
    filter_upwards with ξ using hbd ξ
  -- the strip on which the extension is analytic
  set b : ℝ := a / (4 * π) with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  have hab : 2 * π * b < a := by
    rw [hb_def]
    have : 2 * π * (a / (4 * π)) = a / 2 := by field_simp; ring
    rw [this]; linarith
  have hana : AnalyticOnNhd ℂ (invFourierExt g) (expStrip b) :=
    analyticOnNhd_invFourierExt hab hgcont.aestronglyMeasurable hbd
  -- the extension restricts to `φ` on the real line
  have hreal : ∀ x : ℝ, invFourierExt g (x : ℂ) = φ x := by
    intro x
    rw [invFourierExt_ofReal, hg_def, hcont.fourierInv_fourier_eq hint hgint]
  -- it vanishes frequently near an interior point of the interval
  set p : ℝ := (c + d) / 2 with hp_def
  have hpmem : p ∈ Ioo c d := by
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
      have hmem : Ioo c d ∈ nhdsWithin p ({p}ᶜ : Set ℝ) :=
        nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hpmem)
      filter_upwards [hmem] with x hx
      rw [hreal x]
      exact hzero x hx
    exact hev.frequently
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin (p : ℂ) {(p : ℂ)}ᶜ, invFourierExt g z = 0 :=
    htend.frequently hfreqReal
  have hEq : Set.EqOn (invFourierExt g) 0 (expStrip b) :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_expStrip b) hz₀ hfreq
  intro x
  have := hEq (ofReal_mem_expStrip hb x)
  rw [hreal x] at this
  simpa using this

/-- **Contrapositive form.**  A continuous integrable function that vanishes on
a nonempty open interval but is not identically zero has no exponentially
decaying Fourier transform. -/
theorem not_expDecay_fourier_of_vanishing_interval {φ : ℝ → ℂ}
    (hcont : Continuous φ) (hint : Integrable φ volume)
    {c d : ℝ} (hcd : c < d) (hzero : ∀ x ∈ Ioo c d, φ x = 0)
    {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) :
    ¬ ∃ C a : ℝ, 0 < a ∧
      ∀ ξ, ‖FourierTransform.fourier φ ξ‖ ≤ C * Real.exp (-(a * |ξ|)) := by
  rintro ⟨C, a, ha, hbd⟩
  exact hx₀ (eq_zero_of_expDecay_fourier_of_vanishing_interval hcont hint ha hbd hcd hzero x₀)

/-! ### The taper class of this tree -/

/-- **The incompatibility, for the taper class of the source floor.**  A
compactly supported continuous taper which is somewhere nonzero has no
exponentially decaying Fourier transform, at any rate.

Together with `taperedWeil_gate_fails_of_polyDecay` this closes the taper
dichotomy left open by the G15 report: polynomial decay makes the
source-normalization gate fail, and exponential decay is unavailable for a
compactly supported taper. -/
theorem compactTaper_fourier_not_expDecay {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    {x₀ : ℝ} (hx₀ : φ x₀ ≠ 0) :
    ¬ ∃ C a : ℝ, 0 < a ∧
      ∀ ξ, ‖FourierTransform.fourier (fun u => (φ u : ℂ)) ξ‖
              ≤ C * Real.exp (-(a * |ξ|)) := by
  have hcont : Continuous (fun u => (φ u : ℂ)) :=
    Complex.continuous_ofReal.comp hφ.cont
  have hsupp : HasCompactSupport (fun u => (φ u : ℂ)) := by
    refine HasCompactSupport.intro (K := Set.Icc (-|R| - 1) (|R| + 1)) isCompact_Icc ?_
    intro x hx
    have hR : R < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · have : |R| + 1 < |x| := by
          have := neg_lt_neg h
          calc |R| + 1 < -x := by linarith
            _ ≤ |x| := neg_le_abs x
        calc R ≤ |R| := le_abs_self R
          _ < |R| + 1 := by linarith
          _ < |x| := this
      · have : |R| + 1 < |x| :=
          lt_of_lt_of_le h (le_abs_self x)
        calc R ≤ |R| := le_abs_self R
          _ < |R| + 1 := by linarith
          _ < |x| := this
    simp [hφ.supp x hR]
  have hint : Integrable (fun u => (φ u : ℂ)) volume :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hx₀' : ((φ x₀ : ℂ)) ≠ 0 := by
    simpa using hx₀
  refine not_expDecay_fourier_of_vanishing_interval hcont hint
    (c := |R| + 1) (d := |R| + 2) (by linarith) ?_ hx₀'
  intro x hx
  have hR : R < |x| := by
    have h1 : |R| + 1 < x := hx.1
    have : |R| + 1 < |x| := lt_of_lt_of_le h1 (le_abs_self x)
    calc R ≤ |R| := le_abs_self R
      _ < |R| + 1 := by linarith
      _ < |x| := this
  simp [hφ.supp x hR]

/-- **The plateau normalization.**  A compactly supported taper that equals `1`
on a plateau `|t| ≤ a` — exactly the hypothesis under which
`finiteGridGramDefect_source_floor` proves the `L⁶` Gram floor — has no
exponentially decaying Fourier transform. -/
theorem plateau_taper_fourier_not_expDecay {φ : ℝ → ℝ} {R a : ℝ} (hφ : CompactTaper φ R)
    (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) :
    ¬ ∃ C r : ℝ, 0 < r ∧
      ∀ ξ, ‖FourierTransform.fourier (fun u => (φ u : ℂ)) ξ‖
              ≤ C * Real.exp (-(r * |ξ|)) := by
  refine compactTaper_fourier_not_expDecay hφ (x₀ := 0) ?_
  rw [hplat 0 (by simpa using ha)]
  norm_num

end RiemannAnalytic
