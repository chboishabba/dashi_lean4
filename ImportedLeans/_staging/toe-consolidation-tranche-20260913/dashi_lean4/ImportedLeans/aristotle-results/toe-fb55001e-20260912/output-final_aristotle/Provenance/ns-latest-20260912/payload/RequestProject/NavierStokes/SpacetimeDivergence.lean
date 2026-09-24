/-
# The divergence theorem on spacetime `ℝ × ℝ³` for compactly supported `C¹` fluxes

`CompactDivergence.lean` gives the purely spatial statement: for a `C¹` flux on
`ℝ³` vanishing outside a ball, `∫ ∑ᵢ ∂ᵢFᵢ = 0`.  The *parabolic* scale probe
needs the spacetime version, on `STime = ℝ × E3`, for the full space-time
divergence `∂_t F₀ + ∑ᵢ ∂ᵢFᵢ`.

The proof does not need a four-dimensional box theorem.  It splits the
divergence into its time part and its space part and integrates each in the
convenient order:

* the time part is handled by Fubini in the order `∫_x ∫_t` and the fundamental
  theorem of calculus on a large interval, the endpoints contributing nothing
  because the flux is compactly supported;
* the space part is handled by Fubini in the order `∫_t ∫_x` and the already
  proved three-dimensional statement applied to the time slice.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CompactDivergence

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Slices of a spacetime field -/

/-- The spatial slice map `y ↦ (t, y)` is differentiable with derivative the
inclusion of the space factor. -/
lemma hasFDerivAt_pair_right (t : ℝ) (x : E3) :
    HasFDerivAt (fun y : E3 => ((t : ℝ), y))
      ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3)) x :=
  (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)

/-- The time slice map `s ↦ (s, x)` has derivative `(1, 0)`. -/
lemma hasDerivAt_pair_left (t : ℝ) (x : E3) :
    HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E3)) t :=
  (hasDerivAt_id t).prodMk (hasDerivAt_const t x)

/-- The `i`-th spatial partial derivative of a spacetime field is the `i`-th
partial derivative of its time slice. -/
lemma fderiv_slice_space {g : STime → ℝ} (hg : Differentiable ℝ g) (t : ℝ) (x : E3)
    (i : Fin 3) :
    fderiv ℝ (fun y : E3 => g (t, y)) x (ee i) = fderiv ℝ g (t, x) (0, ee i) := by
  have h : HasFDerivAt (fun y : E3 => g (t, y))
      ((fderiv ℝ g (t, x)).comp ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3))) x :=
    (hg (t, x)).hasFDerivAt.comp x (hasFDerivAt_pair_right t x)
  rw [h.fderiv]
  rfl

/-- The time partial derivative of a spacetime field is the derivative of its
space slice. -/
lemma hasDerivAt_slice_time {g : STime → ℝ} (hg : Differentiable ℝ g) (t : ℝ) (x : E3) :
    HasDerivAt (fun s : ℝ => g (s, x)) (fderiv ℝ g (t, x) (1, 0)) t :=
  (hg (t, x)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pair_left t x)

/-! ## Vanishing of the derivative off the support -/

/-- If a `C¹` function vanishes on `{L ≤ ‖z‖}` then its derivative vanishes on
the open set `{L < ‖z‖}`. -/
lemma fderiv_eq_zero_of_vanishing_outside {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g : X → ℝ} {L : ℝ}
    (hsupp : ∀ z : X, L ≤ ‖z‖ → g z = 0) {z : X} (hz : L < ‖z‖) :
    fderiv ℝ g z = 0 := by
  have hnb : {y : X | L < ‖y‖} ∈ nhds z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hev : g =ᶠ[nhds z] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem hnb fun y hy => hsupp y (le_of_lt hy)
  rw [Filter.EventuallyEq.fderiv_eq hev]
  simp

/-! ## Integrability -/

lemma integrable_of_continuous_of_vanishing {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {g : X → ℝ} (hg : Continuous g) {L : ℝ}
    (hsupp : ∀ z : X, L < ‖z‖ → g z = 0) : Integrable g μ := by
  refine hg.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : X) L) ?_
  intro x hx
  refine hsupp x ?_
  simpa [Metric.mem_closedBall, dist_zero_right] using not_le.1 (by simpa using hx)

/-! ## The spacetime divergence theorem -/

/-- **Divergence theorem on `ℝ × ℝ³` for a compactly supported flux.**  If the
time flux `F₀` and the spatial fluxes `F i` are `C¹` and vanish outside a
bounded set of spacetime, then the integral of the spacetime divergence
`∂_t F₀ + ∑ᵢ ∂ᵢ F i` over all of `ℝ × ℝ³` vanishes. -/
theorem integral_spacetime_divergence_eq_zero
    (F0 : STime → ℝ) (F : Fin 3 → STime → ℝ)
    (hF0 : ContDiff ℝ (1 : ℕ) F0) (hF : ∀ i, ContDiff ℝ (1 : ℕ) (F i))
    {L : ℝ} (hL : 0 < L)
    (h0supp : ∀ z : STime, L ≤ ‖z‖ → F0 z = 0)
    (hsupp : ∀ (i : Fin 3) (z : STime), L ≤ ‖z‖ → F i z = 0) :
    ∫ z : STime, (fderiv ℝ F0 z (1, 0) + ∑ i, fderiv ℝ (F i) z (0, ee i)) = 0 := by
  classical
  have hd0 : Differentiable ℝ F0 := hF0.differentiable (by simp)
  have hdF : ∀ i, Differentiable ℝ (F i) := fun i => (hF i).differentiable (by simp)
  have hc0 : Continuous fun z : STime => fderiv ℝ F0 z (1, 0) :=
    (hF0.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcF : ∀ i, Continuous fun z : STime => fderiv ℝ (F i) z (0, ee i) :=
    fun i => ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  -- the derivatives vanish off a bounded set
  have hz0 : ∀ z : STime, L < ‖z‖ → fderiv ℝ F0 z (1, 0) = 0 := by
    intro z hz
    rw [fderiv_eq_zero_of_vanishing_outside h0supp hz]; rfl
  have hzF : ∀ (i : Fin 3) (z : STime), L < ‖z‖ → fderiv ℝ (F i) z (0, ee i) = 0 := by
    intro i z hz
    rw [fderiv_eq_zero_of_vanishing_outside (hsupp i) hz]; rfl
  -- integrability
  have hint0 : Integrable (fun z : STime => fderiv ℝ F0 z (1, 0)) :=
    integrable_of_continuous_of_vanishing hc0 hz0
  have hintF : Integrable (fun z : STime => ∑ i, fderiv ℝ (F i) z (0, ee i)) :=
    integrable_of_continuous_of_vanishing (continuous_finset_sum _ fun i _ => hcF i)
      (fun z hz => Finset.sum_eq_zero fun i _ => hzF i z hz)
  rw [integral_add hint0 hintF]
  have htime : ∫ z : STime, fderiv ℝ F0 z (1, 0) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, integral_prod_symm _
      (by rwa [← MeasureTheory.Measure.volume_eq_prod])]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    -- the time integral of an exact derivative with compact support
    set L' : ℝ := L + 1 with hL'
    have hL'0 : (0 : ℝ) < L' := by positivity
    have hLL' : L < L' := by simp [hL']
    have hbig : ∀ t : ℝ, L' ≤ |t| → L < ‖((t : ℝ), x)‖ := by
      intro t ht
      have : |t| ≤ ‖((t : ℝ), x)‖ := by
        simp [Prod.norm_def, Real.norm_eq_abs]
      linarith
    have hzero : ∀ t : ℝ, t ∉ Ioc (-L') L' → fderiv ℝ F0 (t, x) (1, 0) = 0 := by
      intro t ht
      refine hz0 _ (hbig t ?_)
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    have hslice : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F0 (s, x)) (fderiv ℝ F0 (t, x) (1, 0)) t :=
      fun t => hasDerivAt_slice_time hd0 t x
    have hcont : Continuous fun t : ℝ => fderiv ℝ F0 (t, x) (1, 0) :=
      hc0.comp (continuous_id.prodMk continuous_const)
    have hii : IntervalIntegrable (fun t : ℝ => fderiv ℝ F0 (t, x) (1, 0)) volume (-L') L' :=
      hcont.intervalIntegrable _ _
    have hsub : (∫ t in (-L')..L', fderiv ℝ F0 (t, x) (1, 0)) = F0 (L', x) - F0 (-L', x) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hslice t) hii
    have hend1 : F0 (L', x) = 0 := h0supp _ (by
      have : |L'| ≤ ‖((L' : ℝ), x)‖ := by
        simp [Prod.norm_def, Real.norm_eq_abs]
      rw [abs_of_nonneg hL'0.le] at this; linarith)
    have hend2 : F0 (-L', x) = 0 := h0supp _ (by
      have : |(-L')| ≤ ‖((-L' : ℝ), x)‖ := by
        simp [Prod.norm_def, Real.norm_eq_abs]
      rw [abs_of_nonpos (by linarith)] at this; linarith)
    calc (∫ t : ℝ, fderiv ℝ F0 (t, x) (1, 0))
        = ∫ t in Ioc (-L') L', fderiv ℝ F0 (t, x) (1, 0) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ t in (-L')..L', fderiv ℝ F0 (t, x) (1, 0) :=
          (intervalIntegral.integral_of_le (by linarith)).symm
      _ = F0 (L', x) - F0 (-L', x) := hsub
      _ = 0 := by rw [hend1, hend2]; ring
  have hspace : ∫ z : STime, ∑ i, fderiv ℝ (F i) z (0, ee i) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _
      (by rwa [← MeasureTheory.Measure.volume_eq_prod])]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    have hslice : ∀ (i : Fin 3), ContDiff ℝ (1 : ℕ) (fun y : E3 => F i (t, y)) := by
      intro i
      exact (hF i).comp ((contDiff_const (c := t)).prodMk contDiff_id)
    have hsl_supp : ∀ (i : Fin 3) (y : E3), L ≤ ‖y‖ → F i (t, y) = 0 := by
      intro i y hy
      refine hsupp i _ ?_
      have : ‖y‖ ≤ ‖((t : ℝ), y)‖ := by
        simp [Prod.norm_def, Real.norm_eq_abs]
      linarith
    have hkey := integral_divergence_eq_zero_of_vanishing_outside
      (fun i => fun y : E3 => F i (t, y)) hslice hL hsl_supp
    calc (∫ y : E3, ∑ i, fderiv ℝ (F i) (t, y) (0, ee i))
        = ∫ y : E3, ∑ i, fderiv ℝ (fun w : E3 => F i (t, w)) y (ee i) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          exact Finset.sum_congr rfl fun i _ => (fderiv_slice_space (hdF i) t y i).symm
      _ = 0 := hkey
  rw [htime, hspace]; ring

end ClayNS
