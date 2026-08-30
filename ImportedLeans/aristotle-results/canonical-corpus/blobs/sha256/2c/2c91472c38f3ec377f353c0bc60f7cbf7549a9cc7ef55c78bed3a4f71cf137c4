/-
**G8-B — the directional (one-sided damped) taper, and what it repairs.**

Lane A is closed for *even* tapers: `no_uniform_quadratic_bound_of_fixed_offset`
(`TwistedTaperUniformity.lean`) proves that `Bφ(α,L) ≤ Cb L²` is **false** for
every fixed `α ≠ 0`, because pairing `u` with `−u` produces the positive weight
`cosh(αu)` and hence `e^{Θ(|α|L)}`.  That is a defect of the *symmetry*, not of
the estimate.

This file changes the test family in exactly the way the obstruction indicates:
a taper supported on one side and damped there,

    `|ψ(u)| ≤ K e^{-cu}` on `[0, R]`,  `ψ = 0` elsewhere,

so that the twisted weight `e^{-αu}` is met by `e^{-(c+α)u} ≤ 1` for every
`α ≥ −c`.  With `c = 1/2` that covers the whole right half of the critical
strip, uniformly.

Proved here:

* `integral_twisted_le_of_oneSided_damped` — the basic uniform estimate: any
  one-sided `K e^{-cu}`-dominated profile has twisted `L¹` mass at most `K·R`,
  *uniformly for all `α ≥ −c`*; and `integral_twisted_le_inv_of_oneSided_damped`
  gives `≤ K/(c+α)`, a bound free of the support length altogether;
* `taperMass_le_of_oneSidedDamped`, `derivMass_le_of_oneSidedDamped` — hence
  both taper masses that enter the window energy are uniformly controlled;
* `windowEnergyBound_le_quadratic_oneSided` — **the α-uniform quadratic bound
  that the even family provably cannot satisfy**:

      `Bψ(α,L) ≤ Cb·L²`  for all `α ≥ −c` and all `L ≥ 1`,

  with `Cb = K₁²/4 + K₂²/(8π²)` explicit, for a one-sided damped taper of
  radius `R = L/2`;
* `exists_oneSidedDampedTaper` — such `C¹` tapers exist at every scale, with a
  full plateau `ψ(u) = e^{-cu}` on `[R/4, 3R/4]`, so the class is not empty and
  the taper is not degenerate;
* `gridSample_zero_im_of_real` — and, independently of all of the above, the
  **anchor coordinate argument does not need evenness**: for *any* real taper
  the central grid sample `Φ(-iα)` is real, so `b₀ = 0` and the anchored minor
  identity `finiteGridAnchorMinorSum_eq_of_real` holds with no symmetry
  hypothesis.  This is what makes a directional family admissible for the
  anchored observable at all.

**What is *not* proved, stated plainly.**  The coercive floor
(`anchoredMinorSum_source_floor`) is *not* available for this family: its proof
runs through `transverseEnergy_twoSided` and `taperExcess`, both of which use
evenness essentially, and the plateau mass of a `c`-damped taper is `O(1/(c+α))`
rather than `≍ L`.  So the directional family buys the uniform ceiling and
currently loses the floor; obtaining a floor for a one-sided damped taper is the
open obligation this file isolates.  Nothing here assumes it.

Nothing in this file refers to `ζ`.
-/
import RiemannAnalytic.TwistedTaperUniformity
import RiemannAnalytic.ShortWindowPrimeTarget

namespace RiemannAnalytic

open MeasureTheory Finset

/-! ### The uniform twisted mass of a one-sided damped profile -/

/-- **The basic uniform estimate.**  A profile supported in `[0, R]` and
dominated there by `K e^{-cu}` has twisted `L¹` mass at most `K·R`, *uniformly
in the twist* `α ≥ −c`: on the support the twisted weight is
`e^{-(c+α)u} ≤ 1`.  Contrast `taperMass_ge_plateau_exp`, where an even taper's
mass grows like `e^{|α|R}`. -/
theorem integral_twisted_le_of_oneSided_damped {f : ℝ → ℝ} {c R K α : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hsupp : ∀ u, u < 0 → f u = 0) (hsuppR : ∀ u, R < u → f u = 0)
    (hdom : ∀ u, 0 ≤ u → u ≤ R → |f u| ≤ K * Real.exp (-c * u))
    (hα : -c ≤ α) :
    (∫ u : ℝ, |f u| * Real.exp (-α * u)) ≤ K * R := by
  classical
  set g : ℝ → ℝ := Set.indicator (Set.Icc 0 R) (fun _ => K) with hg
  have hgint : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Icc]
    exact Continuous.integrableOn_Icc (by fun_prop)
  have hgval : (∫ u : ℝ, g u) = K * R := by
    rw [hg, integral_indicator measurableSet_Icc]
    simp [hR, mul_comm]
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ => |f u| * Real.exp (-α * u) :=
    Filter.Eventually.of_forall fun u => by positivity
  have hle : (fun u : ℝ => |f u| * Real.exp (-α * u)) ≤ᵐ[volume] g := by
    refine Filter.Eventually.of_forall fun u => ?_
    show |f u| * Real.exp (-α * u) ≤ g u
    by_cases hu0 : u < 0
    · rw [hsupp u hu0]
      simp only [abs_zero, zero_mul, hg]
      exact Set.indicator_apply_nonneg fun _ => hK
    · push_neg at hu0
      by_cases huR : R < u
      · rw [hsuppR u huR]
        simp only [abs_zero, zero_mul, hg]
        exact Set.indicator_apply_nonneg fun _ => hK
      · push_neg at huR
        have hmem : u ∈ Set.Icc (0 : ℝ) R := ⟨hu0, huR⟩
        rw [hg, Set.indicator_of_mem hmem]
        have hd := hdom u hu0 huR
        have hexp : Real.exp (-c * u) * Real.exp (-α * u) ≤ 1 := by
          rw [← Real.exp_add]
          refine Real.exp_le_one_iff.2 ?_
          have : 0 ≤ (c + α) * u := mul_nonneg (by linarith) hu0
          nlinarith
        calc |f u| * Real.exp (-α * u)
            ≤ (K * Real.exp (-c * u)) * Real.exp (-α * u) :=
              mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
          _ = K * (Real.exp (-c * u) * Real.exp (-α * u)) := by ring
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hexp hK
          _ = K := by ring
  calc (∫ u : ℝ, |f u| * Real.exp (-α * u)) ≤ ∫ u : ℝ, g u :=
        integral_mono_of_nonneg hnn hgint hle
    _ = K * R := hgval

/-- The closed form of the damped tail integral. -/
theorem integral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * x)) = 1 / b := by
  have h := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := fun x => Real.exp (b * x))
  simp only [neg_zero] at h
  have h3 : (fun x : ℝ => Real.exp (b * -x)) = fun x : ℝ => Real.exp (-b * x) := by
    funext x; ring_nf
  rw [h3] at h
  rw [h, integral_exp_mul_Iic hb 0]
  simp

/-- **A bound free of the support length.**  For a strict twist `α > −c` the
same profile has twisted mass at most `K/(c+α)`, with no reference to `R`: the
damping alone controls the mass, uniformly in the window scale. -/
theorem integral_twisted_le_inv_of_oneSided_damped {f : ℝ → ℝ} {c R K α : ℝ}
    (hK : 0 ≤ K) (hsupp : ∀ u, u < 0 → f u = 0) (hsuppR : ∀ u, R < u → f u = 0)
    (hdom : ∀ u, 0 ≤ u → u ≤ R → |f u| ≤ K * Real.exp (-c * u))
    (hα : -c < α) :
    (∫ u : ℝ, |f u| * Real.exp (-α * u)) ≤ K / (c + α) := by
  classical
  set b : ℝ := c + α with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  set g : ℝ → ℝ := Set.indicator (Set.Ici (0 : ℝ)) (fun u => K * Real.exp (-b * u)) with hg
  have hgintOn : IntegrableOn (fun u : ℝ => K * Real.exp (-b * u)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (exp_neg_integrableOn_Ioi (0 : ℝ) hbpos).const_mul K
  have hgint : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Ici]
    exact hgintOn
  have hgval : (∫ u : ℝ, g u) = K / b := by
    rw [hg, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_neg_mul_Ioi_zero hbpos]
    ring
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ => |f u| * Real.exp (-α * u) :=
    Filter.Eventually.of_forall fun u => by positivity
  have hle : (fun u : ℝ => |f u| * Real.exp (-α * u)) ≤ᵐ[volume] g := by
    refine Filter.Eventually.of_forall fun u => ?_
    show |f u| * Real.exp (-α * u) ≤ g u
    by_cases hu0 : u < 0
    · rw [hsupp u hu0]
      simp only [abs_zero, zero_mul, hg]
      exact Set.indicator_apply_nonneg fun _ => by positivity
    · push_neg at hu0
      have hmem : u ∈ Set.Ici (0 : ℝ) := hu0
      rw [hg, Set.indicator_of_mem hmem]
      by_cases huR : R < u
      · rw [hsuppR u huR]
        simp only [abs_zero, zero_mul]
        positivity
      · push_neg at huR
        have hd := hdom u hu0 huR
        calc |f u| * Real.exp (-α * u)
            ≤ (K * Real.exp (-c * u)) * Real.exp (-α * u) :=
              mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
          _ = K * Real.exp (-b * u) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              rw [hb]
              ring
  calc (∫ u : ℝ, |f u| * Real.exp (-α * u)) ≤ ∫ u : ℝ, g u :=
        integral_mono_of_nonneg hnn hgint hle
    _ = K / b := hgval

/-! ### The one-sided damped taper class -/

/-- A one-sided `c`-damped taper of radius `R`: `C¹`, supported in `[0, R]`,
with value and derivative dominated by `K₁ e^{-cu}` and `K₂ e^{-cu}` there. -/
structure OneSidedDamped (ψ : ℝ → ℝ) (c R K₁ K₂ : ℝ) : Prop where
  c1 : C1Taper ψ R
  suppNeg : ∀ u, u < 0 → ψ u = 0
  dom : ∀ u, 0 ≤ u → u ≤ R → |ψ u| ≤ K₁ * Real.exp (-c * u)
  derivSuppNeg : ∀ u, u < 0 → deriv ψ u = 0
  derivDom : ∀ u, 0 ≤ u → u ≤ R → |deriv ψ u| ≤ K₂ * Real.exp (-c * u)

namespace OneSidedDamped

variable {ψ : ℝ → ℝ} {c R K₁ K₂ : ℝ}

theorem suppPos (h : OneSidedDamped ψ c R K₁ K₂) (hR : 0 ≤ R) : ∀ u, R < u → ψ u = 0 := by
  intro u hu
  refine h.c1.supp u ?_
  rw [abs_of_nonneg (by linarith)]
  exact hu

theorem derivSuppPos (h : OneSidedDamped ψ c R K₁ K₂) (hR : 0 ≤ R) :
    ∀ u, R < u → deriv ψ u = 0 := by
  intro u hu
  refine h.c1.derivSupp u ?_
  rw [abs_of_nonneg (by linarith)]
  exact hu

/-- **Uniform twisted taper mass.**  `taperMass ψ α ≤ K₁ R` for every `α ≥ −c`. -/
theorem taperMass_le (h : OneSidedDamped ψ c R K₁ K₂) (hR : 0 ≤ R) (hK : 0 ≤ K₁)
    {α : ℝ} (hα : -c ≤ α) : taperMass ψ α ≤ K₁ * R :=
  integral_twisted_le_of_oneSided_damped hR hK h.suppNeg (h.suppPos hR) h.dom hα

/-- **Uniform twisted derivative mass.**  `derivMass ψ α ≤ K₂ R` for every
`α ≥ −c`. -/
theorem derivMass_le (h : OneSidedDamped ψ c R K₁ K₂) (hR : 0 ≤ R) (hK : 0 ≤ K₂)
    {α : ℝ} (hα : -c ≤ α) : derivMass ψ α ≤ K₂ * R :=
  integral_twisted_le_of_oneSided_damped hR hK h.derivSuppNeg (h.derivSuppPos hR)
    h.derivDom hα

/-- The support-free version of the mass bound. -/
theorem taperMass_le_inv (h : OneSidedDamped ψ c R K₁ K₂) (hK : 0 ≤ K₁)
    {α : ℝ} (hα : -c < α) : taperMass ψ α ≤ K₁ / (c + α) := by
  by_cases hR : 0 ≤ R
  · exact integral_twisted_le_inv_of_oneSided_damped hK h.suppNeg (h.suppPos hR) h.dom hα
  · push_neg at hR
    refine integral_twisted_le_inv_of_oneSided_damped hK h.suppNeg (fun u hu => ?_) h.dom hα
    rcases lt_or_ge u 0 with hu0 | hu0
    · exact h.suppNeg u hu0
    · exact h.c1.supp u (by rw [abs_of_nonneg hu0]; linarith)

/-- The support-free version of the derivative-mass bound. -/
theorem derivMass_le_inv (h : OneSidedDamped ψ c R K₁ K₂) (hK : 0 ≤ K₂)
    {α : ℝ} (hα : -c < α) : derivMass ψ α ≤ K₂ / (c + α) := by
  by_cases hR : 0 ≤ R
  · exact integral_twisted_le_inv_of_oneSided_damped hK h.derivSuppNeg (h.derivSuppPos hR)
      h.derivDom hα
  · push_neg at hR
    refine integral_twisted_le_inv_of_oneSided_damped hK h.derivSuppNeg (fun u hu => ?_)
      h.derivDom hα
    rcases lt_or_ge u 0 with hu0 | hu0
    · exact h.derivSuppNeg u hu0
    · exact h.c1.derivSupp u (by rw [abs_of_nonneg hu0]; linarith)

end OneSidedDamped

/-! ### The α-uniform quadratic window-energy bound -/

/-- **The bound the even family provably cannot satisfy.**  For a one-sided
`c`-damped taper with damping `c ≥ 1`, every offset in the closed strip
`|α| ≤ 1/2` satisfies `c + α ≥ 1/2`, so both taper masses are bounded by
`2K₁, 2K₂` *uniformly in `α` and in the window scale*, and hence

    `Bψ(α, L) ≤ (4K₁² + 2K₂²/π²) · L²`   for all `L ≥ 1`.

Compare `no_uniform_quadratic_bound_of_fixed_offset`: for an **even** taper no
such constant exists, for any fixed `α ≠ 0`.  The exponential catastrophe is
removed by the directional damping, not by a better estimate. -/
theorem windowEnergyBound_le_quadratic_oneSided {ψ : ℝ → ℝ} {c R L K₁ K₂ : ℝ}
    (h : OneSidedDamped ψ c R K₁ K₂) (hc : 1 ≤ c) (hL : 1 ≤ L) (hK1 : 0 ≤ K₁) (hK2 : 0 ≤ K₂)
    {α : ℝ} (hα : |α| ≤ 1 / 2) :
    windowEnergyBound ψ L α ≤ (4 * K₁ ^ 2 + 2 * K₂ ^ 2 / Real.pi ^ 2) * L ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : -(1 / 2 : ℝ) ≤ α := neg_le_of_abs_le hα
  have hcα : (1 : ℝ) / 2 ≤ c + α := by linarith
  have hlt : -c < α := by linarith
  have hm := h.taperMass_le_inv hK1 hlt
  have hd := h.derivMass_le_inv hK2 hlt
  have hm2 : taperMass ψ α ≤ 2 * K₁ := by
    refine hm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hd2 : derivMass ψ α ≤ 2 * K₂ := by
    refine hd.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hm0 : 0 ≤ taperMass ψ α := taperMass_nonneg ψ α
  have hd0 : 0 ≤ derivMass ψ α := derivMass_nonneg ψ α
  have hmsq : taperMass ψ α ^ 2 ≤ 4 * K₁ ^ 2 := by nlinarith
  have hdsq : derivMass ψ α ^ 2 ≤ 4 * K₂ ^ 2 := by nlinarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  unfold windowEnergyBound
  have hterm : derivMass ψ α ^ 2 * L ^ 2 / (2 * Real.pi ^ 2)
      ≤ 4 * K₂ ^ 2 * L ^ 2 / (2 * Real.pi ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hdsq (by positivity)
  have hfirst : taperMass ψ α ^ 2 ≤ 4 * K₁ ^ 2 * L ^ 2 := by nlinarith
  have hval : 4 * K₂ ^ 2 * L ^ 2 / (2 * Real.pi ^ 2) = 2 * K₂ ^ 2 / Real.pi ^ 2 * L ^ 2 := by
    field_simp
    ring
  nlinarith [hterm, hfirst, hval]

/-! ### Non-vacuity: one-sided damped tapers exist, with explicit constants -/

/-- The derivative of Mathlib's smooth transition function is globally bounded. -/
theorem smoothTransition_deriv_bounded :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · have hzero : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.1 hx with hlt | hgt
      · push_neg at hlt
        have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 := by
          filter_upwards [eventually_lt_nhds hlt] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        rw [hev.deriv_eq]
        simp
      · push_neg at hgt
        have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => 1 := by
          filter_upwards [eventually_gt_nhds hgt] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        rw [hev.deriv_eq]
        simp
    rw [hzero]
    simp

/-- The derivative of the transition function vanishes to the left of `0`. -/
theorem deriv_smoothTransition_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [hev.deriv_eq]
  simp

/-- The explicit one-sided damped taper: a smooth transition up on `[0,1]`, the
damped profile `e^{-cu}` on the plateau, and a smooth transition down on
`[R−1, R]`. -/
noncomputable def oneSidedTaper (c R : ℝ) : ℝ → ℝ := fun u =>
  Real.smoothTransition u * Real.smoothTransition (R - u) * Real.exp (-c * u)

theorem oneSidedTaper_hasDerivAt (c R u : ℝ) : HasDerivAt (oneSidedTaper c R)
    ((deriv Real.smoothTransition u * Real.smoothTransition (R - u)
        + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u))))
        * Real.exp (-c * u)
      + Real.smoothTransition u * Real.smoothTransition (R - u) * (-c * Real.exp (-c * u))) u := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
    (hdiff u).hasDerivAt
  have hinner : HasDerivAt (fun u : ℝ => R - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub R
  have h2 : HasDerivAt (fun u : ℝ => Real.smoothTransition (R - u))
      (-(deriv Real.smoothTransition (R - u))) u := by
    have := (hdiff (R - u)).hasDerivAt.comp u hinner
    simpa [mul_comm] using this
  have hg : HasDerivAt (fun u : ℝ => Real.exp (-c * u)) (-c * Real.exp (-c * u)) u := by
    have := ((hasDerivAt_id u).const_mul (-c)).exp
    simpa [mul_comm] using this
  exact (h1.mul h2).mul hg

theorem deriv_oneSidedTaper (c R u : ℝ) :
    deriv (oneSidedTaper c R) u
      = (deriv Real.smoothTransition u * Real.smoothTransition (R - u)
          + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u))))
          * Real.exp (-c * u)
        + Real.smoothTransition u * Real.smoothTransition (R - u)
          * (-c * Real.exp (-c * u)) :=
  (oneSidedTaper_hasDerivAt c R u).deriv

/-- **One-sided damped tapers exist at every scale, with constants independent
of the scale.**  For every damping `c ≥ 0` and radius `R ≥ 0` there is a `C¹`
taper supported in `[0, R]`, dominated by `e^{-cu}`, with derivative dominated
by `(2S + c) e^{-cu}` for a constant `S` independent of `R` and `c`, and equal
to the full damped profile `e^{-cu}` on the plateau `[1, R−1]`. -/
theorem exists_oneSidedDampedTaper {c R : ℝ} (hc : 0 ≤ c) :
    ∃ (ψ : ℝ → ℝ) (K₂ : ℝ), OneSidedDamped ψ c R 1 K₂ ∧ 0 ≤ K₂ ∧
      (∀ u, 0 ≤ ψ u) ∧ (∀ u, 1 ≤ u → u ≤ R - 1 → ψ u = Real.exp (-c * u)) := by
  obtain ⟨S, hS0, hS⟩ := smoothTransition_deriv_bounded
  refine ⟨oneSidedTaper c R, 2 * S + c, ?_, by linarith, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact fun u => (oneSidedTaper_hasDerivAt c R u).differentiableAt
    · have hcont : Continuous (deriv Real.smoothTransition) :=
        (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
      have hst : Continuous Real.smoothTransition :=
        (Real.smoothTransition.contDiff (n := 1)).continuous
      have : deriv (oneSidedTaper c R) = fun u =>
          (deriv Real.smoothTransition u * Real.smoothTransition (R - u)
              + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u))))
              * Real.exp (-c * u)
            + Real.smoothTransition u * Real.smoothTransition (R - u)
              * (-c * Real.exp (-c * u)) := funext (deriv_oneSidedTaper c R)
      rw [this]
      fun_prop
    · intro t ht
      unfold oneSidedTaper
      rcases lt_or_ge t 0 with htneg | htpos
      · rw [Real.smoothTransition.zero_of_nonpos htneg.le]
        ring
      · have htR : R < t := by
          rwa [abs_of_nonneg htpos] at ht
        rw [Real.smoothTransition.zero_of_nonpos (by linarith : R - t ≤ 0)]
        ring
    · intro u hu
      unfold oneSidedTaper
      rw [Real.smoothTransition.zero_of_nonpos hu.le]
      ring
    · intro u hu0 _
      unfold oneSidedTaper
      have h1 : |Real.smoothTransition u * Real.smoothTransition (R - u)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
          abs_of_nonneg (Real.smoothTransition.nonneg _)]
        nlinarith [Real.smoothTransition.le_one u, Real.smoothTransition.le_one (R - u),
          Real.smoothTransition.nonneg u, Real.smoothTransition.nonneg (R - u)]
      rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      nlinarith [Real.exp_pos (-c * u), h1]
    · intro u hu
      rw [deriv_oneSidedTaper]
      rw [Real.smoothTransition.zero_of_nonpos hu.le, deriv_smoothTransition_of_neg hu]
      ring
    · intro u hu0 _
      rw [deriv_oneSidedTaper]
      have hs1 := Real.smoothTransition.nonneg u
      have hs1' := Real.smoothTransition.le_one u
      have hs2 := Real.smoothTransition.nonneg (R - u)
      have hs2' := Real.smoothTransition.le_one (R - u)
      have hd1 := hS u
      have hd2 := hS (R - u)
      have hexp : 0 < Real.exp (-c * u) := Real.exp_pos _
      have habs1 : |deriv Real.smoothTransition u * Real.smoothTransition (R - u)
          + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u)))| ≤ 2 * S := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul, abs_neg]
        rw [abs_of_nonneg hs2, abs_of_nonneg hs1]
        nlinarith [abs_nonneg (deriv Real.smoothTransition u),
          abs_nonneg (deriv Real.smoothTransition (R - u))]
      have habs2 : |Real.smoothTransition u * Real.smoothTransition (R - u) * (-c)| ≤ c := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs1, abs_of_nonneg hs2, abs_of_nonneg hc]
        have hprod : Real.smoothTransition u * Real.smoothTransition (R - u) ≤ 1 := by nlinarith
        have hprod0 : 0 ≤ Real.smoothTransition u * Real.smoothTransition (R - u) := by positivity
        nlinarith [hprod, hprod0, hc]
      calc |(deriv Real.smoothTransition u * Real.smoothTransition (R - u)
              + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u))))
              * Real.exp (-c * u)
            + Real.smoothTransition u * Real.smoothTransition (R - u)
              * (-c * Real.exp (-c * u))|
          ≤ |(deriv Real.smoothTransition u * Real.smoothTransition (R - u)
                + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u))))
                * Real.exp (-c * u)|
            + |Real.smoothTransition u * Real.smoothTransition (R - u)
                * (-c * Real.exp (-c * u))| := abs_add_le _ _
        _ = |deriv Real.smoothTransition u * Real.smoothTransition (R - u)
                + Real.smoothTransition u * (-(deriv Real.smoothTransition (R - u)))|
              * Real.exp (-c * u)
            + |Real.smoothTransition u * Real.smoothTransition (R - u) * (-c)|
              * Real.exp (-c * u) := by
            rw [abs_mul, abs_of_nonneg hexp.le]
            congr 1
            rw [show Real.smoothTransition u * Real.smoothTransition (R - u)
                * (-c * Real.exp (-c * u))
              = (Real.smoothTransition u * Real.smoothTransition (R - u) * (-c))
                * Real.exp (-c * u) by ring, abs_mul, abs_of_nonneg hexp.le]
        _ ≤ 2 * S * Real.exp (-c * u) + c * Real.exp (-c * u) := by
            have := mul_le_mul_of_nonneg_right habs1 hexp.le
            have := mul_le_mul_of_nonneg_right habs2 hexp.le
            linarith
        _ = (2 * S + c) * Real.exp (-c * u) := by ring
  · intro u
    unfold oneSidedTaper
    have := Real.smoothTransition.nonneg u
    have := Real.smoothTransition.nonneg (R - u)
    have := (Real.exp_pos (-c * u)).le
    positivity
  · intro u hu1 hu2
    unfold oneSidedTaper
    rw [Real.smoothTransition.one_of_one_le hu1,
      Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ R - u)]
    ring

/-! ### The anchor argument does not need evenness -/

/-- **The central grid sample of any real taper is real.**  At the central grid
point the twisted exponential `e^{-i(-iα)u} = e^{-αu}` is real, so `Φ(-iα)` is
the integral of a real function: `b₀ = 0` with no symmetry hypothesis at all.
This is what allows the anchored observable to be used with a directional
(non-even) taper. -/
theorem gridSample_zero_im_of_real (φ : ℝ → ℝ) (h α : ℝ) :
    (gridSample φ h α 0).im = 0 := by
  have hval : gridSample φ h α 0 = ((∫ t : ℝ, φ t * Real.exp (-(α * t)) : ℝ) : ℂ) := by
    unfold gridSample PhiExt
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (φ t : ℂ) * Complex.exp (-(Complex.I * ((((0 : ℤ) : ℝ) : ℂ) * (h : ℂ)
        - Complex.I * (α : ℂ)) * (t : ℂ))) = ((φ t * Real.exp (-(α * t)) : ℝ) : ℂ)
    have harg : (-(Complex.I * ((((0 : ℤ) : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)) * (t : ℂ)))
        = ((-(α * t) : ℝ) : ℂ) := by
      push_cast
      simp [Complex.ext_iff]
    rw [harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  rw [hval]
  simp

/-- The imaginary part of the anchor coordinate of the window vector vanishes
for every real taper. -/
theorem imOf_gridVec_head_of_real (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) :
    imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (d + 1)) 0 = 0 := by
  unfold imOf
  rw [gridVec_head φ h α d, gridSample_zero_im_of_real φ h α]

/-- **The anchored minor identity without evenness.**  For an arbitrary real
taper the anchored observable of the source window is still exactly
`a₀²‖b‖²` — the anchor argument survives the loss of symmetry, so a directional
family is admissible for the anchored consumer. -/
theorem finiteGridAnchorMinorSum_eq_of_real (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) :
    finiteGridAnchorMinorSum φ h α m
      = (gridSample φ h α 0).re ^ 2
        * (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
            ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))) := by
  unfold finiteGridAnchorMinorSum
  rw [coordAnchorMinorSum_eq_of_anchor _ _ 0 (imOf_gridVec_head_of_real φ h α m),
    reOf_gridVec_head φ h α m]

end RiemannAnalytic
