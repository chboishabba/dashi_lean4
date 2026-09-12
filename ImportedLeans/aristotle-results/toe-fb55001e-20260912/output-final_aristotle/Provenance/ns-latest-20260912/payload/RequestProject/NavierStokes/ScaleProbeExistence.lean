/-
# Existence of a separating scale probe

`ScaleProbeRadial.lean` reduces the anchor question to a *criterion*: the cut-off
homogeneous probe `L(V) = ∫(χ(r)/r²)·V(r)·r²dr` separates the profile from its
scaling derivative as soon as

  `∫|χ'|·r·|V| < ∫χ·V`,

the left side being supported only where the cut-off varies.  That criterion is
an assumption there.  This file *discharges* it: for any nonnegative profile with
finite total mass and a nonvanishing core, a separating cut-off actually exists.

The mechanism is the logarithmic (Landis) pigeonhole, which is the radial
analogue of the geometric-tail/finite-occupation move already used elsewhere in
this development: the transition cost of a dyadic cut-off carries no net power of
`r` (the annulus width equals the radius), so the *total* cost of `N` disjoint
dyadic transitions is bounded by the total mass; hence some single transition
costs at most `mass/N`, and `N` is ours to choose.

* `ClayNS.exists_smoothTransition_deriv_bound` — the universal constant `K`
  bounding the derivative of Mathlib's smooth transition.  The two endpoint
  cases are handled by the observation that every point of `[1,∞)` is a global
  maximum and every point of `(−∞,0]` a global minimum, so the derivative
  vanishes there.
* `ClayNS.plateauCut` — the two-sided plateau cut-off `s((r−a₁)/(a₂−a₁))·
  s((b₂−r)/(b₂−b₁))`: it vanishes at `a₁` and `b₂`, equals `1` on `[a₂,b₁]`, and
  its derivative is supported in the two transition annuli with the sharp bounds
  `K/(a₂−a₁)` and `K/(b₂−b₁)`.
* `ClayNS.exists_good_dyadic_annulus` — the pigeonhole: among `N` consecutive
  dyadic annuli the profile's mass is at most `T/N` on one of them.
* `ClayNS.exists_small_residual_radial_probe` — **the quantitative conclusion**:
  for every tolerance `ε > 0` there is a cut-off `χ` with `|L(ΛV)| ≤ ε` while
  `L(V)` is still at least the core mass.  This is exactly the pair `(δ, a₀)`
  required by `ClayNS.gram_anchor_lower_bound_approx`, with `δ` as small as one
  likes and `a₀` fixed.
* `ClayNS.exists_separating_radial_probe` — the qualitative corollary: a cut-off
  for which the sharp separation criterion of
  `ClayNS.radial_probe_separates_sharp` actually holds, `|L(ΛV)| < L(V)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleProbeRadial

open MeasureTheory intervalIntegral Set

noncomputable section

namespace ClayNS

/-! ## The universal transition constant -/

/-- The derivative of Mathlib's smooth transition. -/
def sTrans' : ℝ → ℝ := deriv Real.smoothTransition

lemma hasDerivAt_sTrans (x : ℝ) : HasDerivAt Real.smoothTransition (sTrans' x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) x).hasDerivAt

lemma continuous_sTrans' : Continuous sTrans' :=
  (Real.smoothTransition.contDiff (n := 2)).continuous_deriv
    (by exact_mod_cast (by norm_num : (1 : ℕ∞) ≤ 2))

/-- Every point of `[1,∞)` is a global maximum of the transition, so the
derivative vanishes there — including at the junction `x = 1`. -/
lemma sTrans'_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : sTrans' x = 0 := by
  have hmax : IsLocalMax Real.smoothTransition x := by
    have hx1 : Real.smoothTransition x = 1 := Real.smoothTransition.one_of_one_le hx
    filter_upwards with y
    simpa [hx1] using Real.smoothTransition.le_one y
  exact hmax.deriv_eq_zero

/-- Every point of `(−∞,0]` is a global minimum of the transition. -/
lemma sTrans'_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : sTrans' x = 0 := by
  have hmin : IsLocalMin Real.smoothTransition x := by
    have hx1 : Real.smoothTransition x = 0 := Real.smoothTransition.zero_of_nonpos hx
    filter_upwards with y
    simpa [hx1] using Real.smoothTransition.nonneg y
  exact hmin.deriv_eq_zero

/-- **The universal transition constant.**  The transition's derivative is
globally bounded: it is continuous and vanishes off `[0,1]`. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x, |sTrans' x| ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_sTrans'.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  rcases le_or_gt x 0 with h | h
  · simp only [sTrans'_eq_zero_of_nonpos h, abs_zero]
    positivity
  rcases le_or_gt 1 x with h1 | h1
  · simp only [sTrans'_eq_zero_of_one_le h1, abs_zero]
    positivity
  · have hx := hC x ⟨le_of_lt h, le_of_lt h1⟩
    rw [Real.norm_eq_abs] at hx
    exact hx.trans (le_max_left _ _)

/-! ## The plateau cut-off -/

/-- The two-sided plateau cut-off: it rises from `0` at `a₁` to `1` at `a₂` and
falls back from `1` at `b₁` to `0` at `b₂`. -/
def plateauCut (a1 a2 b1 b2 : ℝ) : ℝ → ℝ := fun r =>
  Real.smoothTransition ((r - a1) / (a2 - a1)) * Real.smoothTransition ((b2 - r) / (b2 - b1))

/-- The derivative of the plateau cut-off. -/
def plateauCut' (a1 a2 b1 b2 : ℝ) : ℝ → ℝ := fun r =>
  sTrans' ((r - a1) / (a2 - a1)) / (a2 - a1) * Real.smoothTransition ((b2 - r) / (b2 - b1))
    - Real.smoothTransition ((r - a1) / (a2 - a1)) * (sTrans' ((b2 - r) / (b2 - b1)) / (b2 - b1))

lemma hasDerivAt_plateauCut {a1 a2 b1 b2 : ℝ} (h1 : a1 < a2) (h2 : b1 < b2) (r : ℝ) :
    HasDerivAt (plateauCut a1 a2 b1 b2) (plateauCut' a1 a2 b1 b2 r) r := by
  have hd1 : a2 - a1 ≠ 0 := sub_ne_zero.2 (ne_of_gt h1)
  have hd2 : b2 - b1 ≠ 0 := sub_ne_zero.2 (ne_of_gt h2)
  have hu : HasDerivAt (fun r : ℝ => (r - a1) / (a2 - a1)) (1 / (a2 - a1)) r := by
    simpa using ((hasDerivAt_id r).sub_const a1).div_const (a2 - a1)
  have hv : HasDerivAt (fun r : ℝ => (b2 - r) / (b2 - b1)) (-1 / (b2 - b1)) r := by
    simpa using ((hasDerivAt_id r).const_sub b2).div_const (b2 - b1)
  have hA := (hasDerivAt_sTrans ((r - a1) / (a2 - a1))).comp r hu
  have hB := (hasDerivAt_sTrans ((b2 - r) / (b2 - b1))).comp r hv
  have hm := hA.mul hB
  simp only [Function.comp_apply] at hm
  have hfun : ((Real.smoothTransition ∘ fun r : ℝ => (r - a1) / (a2 - a1)) *
      (Real.smoothTransition ∘ fun r : ℝ => (b2 - r) / (b2 - b1)))
      = plateauCut a1 a2 b1 b2 := rfl
  rw [hfun] at hm
  refine hm.congr_deriv ?_
  simp only [plateauCut']
  field_simp
  ring

lemma continuous_plateauCut (a1 a2 b1 b2 : ℝ) : Continuous (plateauCut a1 a2 b1 b2) :=
  (Real.smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)).mul
    (Real.smoothTransition.continuous.comp ((continuous_const.sub continuous_id).div_const _))

lemma continuous_plateauCut' (a1 a2 b1 b2 : ℝ) :
    Continuous (plateauCut' a1 a2 b1 b2) := by
  have hc1 : Continuous fun r : ℝ => (r - a1) / (a2 - a1) :=
    (continuous_id.sub continuous_const).div_const _
  have hc2 : Continuous fun r : ℝ => (b2 - r) / (b2 - b1) :=
    (continuous_const.sub continuous_id).div_const _
  exact (((continuous_sTrans'.comp hc1).div_const _).mul
      (Real.smoothTransition.continuous.comp hc2)).sub
    ((Real.smoothTransition.continuous.comp hc1).mul
      ((continuous_sTrans'.comp hc2).div_const _))

lemma plateauCut_nonneg (a1 a2 b1 b2 r : ℝ) : 0 ≤ plateauCut a1 a2 b1 b2 r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma plateauCut_le_one (a1 a2 b1 b2 r : ℝ) : plateauCut a1 a2 b1 b2 r ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma plateauCut_left_zero (a1 a2 b1 b2 : ℝ) : plateauCut a1 a2 b1 b2 a1 = 0 := by
  simp [plateauCut, Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]

lemma plateauCut_right_zero (a1 a2 b1 b2 : ℝ) : plateauCut a1 a2 b1 b2 b2 = 0 := by
  simp [plateauCut, Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]

/-- The plateau cut-off is supported in `[a₁,b₂]`. -/
lemma plateauCut_eq_zero_outside {a1 a2 b1 b2 : ℝ} (h1 : a1 < a2) (h2 : b1 < b2) {r : ℝ}
    (hr : r ≤ a1 ∨ b2 ≤ r) : plateauCut a1 a2 b1 b2 r = 0 := by
  rcases hr with hr | hr
  · have hq : (r - a1) / (a2 - a1) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    simp [plateauCut, Real.smoothTransition.zero_of_nonpos hq]
  · have hq : (b2 - r) / (b2 - b1) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    simp [plateauCut, Real.smoothTransition.zero_of_nonpos hq]

lemma plateauCut_eq_one {a1 a2 b1 b2 : ℝ} (h1 : a1 < a2) (h2 : b1 < b2) {r : ℝ}
    (hr1 : a2 ≤ r) (hr2 : r ≤ b1) : plateauCut a1 a2 b1 b2 r = 1 := by
  have e1 : (1 : ℝ) ≤ (r - a1) / (a2 - a1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have e2 : (1 : ℝ) ≤ (b2 - r) / (b2 - b1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  simp [plateauCut, Real.smoothTransition.one_of_one_le e1,
    Real.smoothTransition.one_of_one_le e2]

/-- On the plateau the derivative vanishes: the cut-off costs nothing in the
bulk. -/
lemma plateauCut'_eq_zero_middle {a1 a2 b1 b2 : ℝ} (h1 : a1 < a2) (h2 : b1 < b2) {r : ℝ}
    (hr1 : a2 ≤ r) (hr2 : r ≤ b1) : plateauCut' a1 a2 b1 b2 r = 0 := by
  have e1 : (1 : ℝ) ≤ (r - a1) / (a2 - a1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have e2 : (1 : ℝ) ≤ (b2 - r) / (b2 - b1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  simp [plateauCut', sTrans'_eq_zero_of_one_le e1, sTrans'_eq_zero_of_one_le e2]

/-- On the inner transition annulus the derivative is bounded by `K/(a₂−a₁)`. -/
lemma plateauCut'_inner_bound {a1 a2 b1 b2 K : ℝ} (h1 : a1 < a2) (h2 : b1 < b2)
    (hab : a2 ≤ b1) (hK : ∀ x, |sTrans' x| ≤ K) {r : ℝ} (hr2 : r ≤ a2) :
    |plateauCut' a1 a2 b1 b2 r| ≤ K / (a2 - a1) := by
  have e2 : (1 : ℝ) ≤ (b2 - r) / (b2 - b1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hz : sTrans' ((b2 - r) / (b2 - b1)) = 0 := sTrans'_eq_zero_of_one_le e2
  have hone : Real.smoothTransition ((b2 - r) / (b2 - b1)) = 1 :=
    Real.smoothTransition.one_of_one_le e2
  have hd : (0 : ℝ) < a2 - a1 := by linarith
  simp only [plateauCut', hz, hone, mul_one, zero_div, mul_zero, sub_zero]
  rw [abs_div, abs_of_pos hd]
  gcongr
  exact hK _

/-- On the outer transition annulus the derivative is bounded by `K/(b₂−b₁)`. -/
lemma plateauCut'_outer_bound {a1 a2 b1 b2 K : ℝ} (h1 : a1 < a2) (h2 : b1 < b2)
    (hab : a2 ≤ b1) (hK : ∀ x, |sTrans' x| ≤ K) {r : ℝ} (hr1 : b1 ≤ r) :
    |plateauCut' a1 a2 b1 b2 r| ≤ K / (b2 - b1) := by
  have e1 : (1 : ℝ) ≤ (r - a1) / (a2 - a1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hz : sTrans' ((r - a1) / (a2 - a1)) = 0 := sTrans'_eq_zero_of_one_le e1
  have hone : Real.smoothTransition ((r - a1) / (a2 - a1)) = 1 :=
    Real.smoothTransition.one_of_one_le e1
  have hd : (0 : ℝ) < b2 - b1 := by linarith
  simp only [plateauCut', hz, hone, one_mul, zero_div, zero_mul, zero_sub, abs_neg]
  rw [abs_div, abs_of_pos hd]
  gcongr
  exact hK _

/-! ## The dyadic pigeonhole -/

/-- **Pigeonhole.**  Among `N` consecutive dyadic annuli starting at `c`, some
annulus carries at most `T/N` of the profile's mass.  This is where the positive
scaling dimension of the residual is cashed in: the annulus width equals the
radius, so the transition cost carries no net power of `r`, and the *total* cost
of the `N` disjoint transitions is bounded by the total mass. -/
theorem exists_good_dyadic_annulus {V : ℝ → ℝ} {c T : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N)
    (hVc : ContinuousOn V (Icc c (c * 2 ^ N)))
    (hmass : (∫ r in c..(c * 2 ^ N), V r) ≤ T) :
    ∃ i < N, (∫ r in (c * 2 ^ i)..(c * 2 ^ (i + 1)), V r) ≤ T / N := by
  set a : ℕ → ℝ := fun k => c * 2 ^ k with ha
  have hmono : Monotone a := by
    intro k l hkl
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkl)
      hc.le
  have hsub : ∀ k, k < N → Icc (a k) (a (k + 1)) ⊆ Icc c (c * 2 ^ N) := by
    intro k hk x hx
    exact ⟨le_trans (by simpa [ha] using hmono (Nat.zero_le k)) hx.1,
      le_trans hx.2 (hmono hk)⟩
  have hint : ∀ k < N, IntervalIntegrable V volume (a k) (a (k + 1)) := by
    intro k hk
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (hmono (Nat.le_succ k))]
    exact hVc.mono (hsub k hk)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = c := by simp [ha]
  have hle : ∑ k ∈ Finset.range N, (∫ r in a k..a (k + 1), V r) ≤ T := by
    rw [hsum, h0]
    exact hmass
  have hconst : ∑ _k ∈ Finset.range N, (T / N) = T := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  obtain ⟨i, hi, hle'⟩ := Finset.exists_le_of_sum_le
    (f := fun k => ∫ r in a k..a (k + 1), V r) (g := fun _ => T / N)
    (Finset.nonempty_range_iff.2 hN.ne') (by rw [hconst]; exact hle)
  exact ⟨i, Finset.mem_range.1 hi, hle'⟩

/-! ## The transition cost and the bulk -/

/-- **The transition cost of a dyadic plateau cut-off.**  If both transition
annuli are dyadic (`a₂ = 2a₁`, `b₂ = 2b₁`) and each carries at most `M` of the
profile's mass, then the whole transition cost is at most `4KM`.  The point is
that no power of `r` survives: the annulus width equals the radius, so
`r·|χ'| ≤ 2K` on each transition and `0` in between. -/
theorem plateau_transition_cost_le {V : ℝ → ℝ} {a1 a2 b1 b2 K M : ℝ}
    (h1 : a1 < a2) (h2 : b1 < b2) (hab : a2 ≤ b1) (ha1 : 0 < a1)
    (hK : ∀ x, |sTrans' x| ≤ K) (hKpos : 0 ≤ K)
    (hdya : a2 = 2 * a1) (hdyb : b2 = 2 * b1)
    (hVnn : ∀ r ∈ Icc a1 b2, 0 ≤ V r)
    (hVc : ContinuousOn V (Icc a1 b2))
    (hin : (∫ r in a1..a2, V r) ≤ M) (hout : (∫ r in b1..b2, V r) ≤ M) :
    (∫ r in a1..b2, |plateauCut' a1 a2 b1 b2 r| * r * |V r|) ≤ 4 * K * M := by
  have hb1 : 0 < b1 := lt_of_lt_of_le (lt_of_lt_of_le ha1 h1.le) hab
  have ha1b2 : a1 ≤ b2 := by linarith
  set g : ℝ → ℝ := fun r => |plateauCut' a1 a2 b1 b2 r| * r * |V r| with hg
  have hgc : ContinuousOn g (Icc a1 b2) :=
    (((continuous_plateauCut' a1 a2 b1 b2).abs.continuousOn).mul continuousOn_id).mul hVc.abs
  have hgi : ∀ x y : ℝ, a1 ≤ x → x ≤ y → y ≤ b2 → IntervalIntegrable g volume x y := by
    intro x y hx hxy hy
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hxy]
    exact hgc.mono fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hgi a1 a2 le_rfl h1.le (by linarith)) (hgi a2 b1 h1.le hab (by linarith))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hgi a1 b1 le_rfl (by linarith) (by linarith)) (hgi b1 b2 (by linarith) h2.le le_rfl)
  have hmid : (∫ r in a2..b1, g r) = 0 := by
    rw [show (0 : ℝ) = ∫ _r in a2..b1, (0 : ℝ) by simp]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hab] at hr
    simp [hg, plateauCut'_eq_zero_middle h1 h2 hr.1 hr.2]
  have heqa : a2 - a1 = a1 := by rw [hdya]; ring
  have heqb : b2 - b1 = b1 := by rw [hdyb]; ring
  have hinner : (∫ r in a1..a2, g r) ≤ 2 * K * M := by
    have hmono : ∀ r ∈ Icc a1 a2, g r ≤ (2 * K) * V r := by
      intro r hr
      have hrpos : 0 < r := lt_of_lt_of_le ha1 hr.1
      have hVr : 0 ≤ V r := hVnn r ⟨hr.1, by linarith [hr.2]⟩
      have hb := plateauCut'_inner_bound h1 h2 hab hK hr.2
      rw [heqa] at hb
      have hrle : r ≤ 2 * a1 := by rw [← hdya]; exact hr.2
      have habsV : |V r| = V r := abs_of_nonneg hVr
      calc g r = |plateauCut' a1 a2 b1 b2 r| * r * V r := by simp only [hg, habsV]
        _ ≤ (K / a1) * (2 * a1) * V r := by
            have hmm := mul_le_mul hb hrle hrpos.le (by positivity)
            exact mul_le_mul_of_nonneg_right hmm hVr
        _ = (2 * K) * V r := by field_simp
    have hVi : IntervalIntegrable V volume a1 a2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h1.le]
      exact hVc.mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩
    have hcmp := intervalIntegral.integral_mono_on h1.le (hgi a1 a2 le_rfl h1.le (by linarith))
      (hVi.const_mul (2 * K)) hmono
    rw [intervalIntegral.integral_const_mul] at hcmp
    refine hcmp.trans ?_
    nlinarith [hin]
  have houter : (∫ r in b1..b2, g r) ≤ 2 * K * M := by
    have hmono : ∀ r ∈ Icc b1 b2, g r ≤ (2 * K) * V r := by
      intro r hr
      have hrpos : 0 < r := lt_of_lt_of_le hb1 hr.1
      have hVr : 0 ≤ V r := hVnn r ⟨by linarith [hr.1], hr.2⟩
      have hb := plateauCut'_outer_bound h1 h2 hab hK hr.1
      rw [heqb] at hb
      have hrle : r ≤ 2 * b1 := by rw [← hdyb]; exact hr.2
      have habsV : |V r| = V r := abs_of_nonneg hVr
      calc g r = |plateauCut' a1 a2 b1 b2 r| * r * V r := by simp only [hg, habsV]
        _ ≤ (K / b1) * (2 * b1) * V r := by
            have hmm := mul_le_mul hb hrle hrpos.le (by positivity)
            exact mul_le_mul_of_nonneg_right hmm hVr
        _ = (2 * K) * V r := by field_simp
    have hVi : IntervalIntegrable V volume b1 b2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h2.le]
      exact hVc.mono fun z hz => ⟨by linarith [hz.1], hz.2⟩
    have hcmp := intervalIntegral.integral_mono_on h2.le (hgi b1 b2 (by linarith) h2.le le_rfl)
      (hVi.const_mul (2 * K)) hmono
    rw [intervalIntegral.integral_const_mul] at hcmp
    refine hcmp.trans ?_
    nlinarith [hout]
  linarith [hsplit1, hsplit2, hmid, hinner, houter]

/-- **The bulk of a plateau cut-off dominates the core mass.**  Since the cut-off
equals `1` across `[a₂,b₁] ⊇ [c₁,c₂]` and the profile is nonnegative, the bulk is
at least the core mass. -/
theorem plateau_bulk_ge_core {V : ℝ → ℝ} {a1 a2 b1 b2 c1 c2 : ℝ}
    (h1 : a1 < a2) (h2 : b1 < b2)
    (hac : a2 ≤ c1) (hc : c1 ≤ c2) (hcb : c2 ≤ b1)
    (hVnn : ∀ r ∈ Icc a1 b2, 0 ≤ V r) (hVc : ContinuousOn V (Icc a1 b2)) :
    (∫ r in c1..c2, V r) ≤ ∫ r in a1..b2, plateauCut a1 a2 b1 b2 r * V r := by
  have hab : a2 ≤ b1 := le_trans hac (le_trans hc hcb)
  have ha1b2 : a1 ≤ b2 := by linarith
  set f : ℝ → ℝ := fun r => plateauCut a1 a2 b1 b2 r * V r with hf
  have hfc : ContinuousOn f (Icc a1 b2) :=
    (continuous_plateauCut a1 a2 b1 b2).continuousOn.mul hVc
  have hfi : ∀ x y : ℝ, a1 ≤ x → x ≤ y → y ≤ b2 → IntervalIntegrable f volume x y := by
    intro x y hx hxy hy
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hxy]
    exact hfc.mono fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩
  have hVi : ∀ x y : ℝ, a1 ≤ x → x ≤ y → y ≤ b2 → IntervalIntegrable V volume x y := by
    intro x y hx hxy hy
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hxy]
    exact hVc.mono fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩
  have hfnn : ∀ x y : ℝ, a1 ≤ x → x ≤ y → y ≤ b2 → 0 ≤ ∫ r in x..y, f r := by
    intro x y hx hxy hy
    refine intervalIntegral.integral_nonneg hxy fun r hr => ?_
    exact mul_nonneg (plateauCut_nonneg _ _ _ _ _)
      (hVnn r ⟨le_trans hx hr.1, le_trans hr.2 hy⟩)
  have hVnn' : ∀ x y : ℝ, a1 ≤ x → x ≤ y → y ≤ b2 → 0 ≤ ∫ r in x..y, V r := by
    intro x y hx hxy hy
    exact intervalIntegral.integral_nonneg hxy fun r hr =>
      hVnn r ⟨le_trans hx hr.1, le_trans hr.2 hy⟩
  -- the middle piece equals the unweighted integral
  have hmid : (∫ r in a2..b1, f r) = ∫ r in a2..b1, V r := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hab] at hr
    simp [hf, plateauCut_eq_one h1 h2 hr.1 hr.2]
  -- and the middle integral dominates the core
  have hcore : (∫ r in c1..c2, V r) ≤ ∫ r in a2..b1, V r := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (hVi a2 c1 h1.le hac (by linarith)) (hVi c1 c2 (by linarith) hc (by linarith))
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hVi a2 c2 h1.le (by linarith) (by linarith)) (hVi c2 b1 (by linarith) hcb (by linarith))
    have p1 : 0 ≤ ∫ r in a2..c1, V r := hVnn' a2 c1 h1.le hac (by linarith)
    have p2 : 0 ≤ ∫ r in c2..b1, V r := hVnn' c2 b1 (by linarith) hcb (by linarith)
    linarith [e1, e2, p1, p2]
  have s1 := intervalIntegral.integral_add_adjacent_intervals
    (hfi a1 a2 le_rfl h1.le (by linarith)) (hfi a2 b1 h1.le hab (by linarith))
  have s2 := intervalIntegral.integral_add_adjacent_intervals
    (hfi a1 b1 le_rfl (by linarith) (by linarith)) (hfi b1 b2 (by linarith) h2.le le_rfl)
  have p1 : 0 ≤ ∫ r in a1..a2, f r := hfnn a1 a2 le_rfl h1.le (by linarith)
  have p2 : 0 ≤ ∫ r in b1..b2, f r := hfnn b1 b2 (by linarith) h2.le le_rfl
  linarith [s1, s2, hmid, hcore, p1, p2]


/-! ## Existence of a probe with arbitrarily small residual -/

/-- **A scale probe with arbitrarily small residual exists.**  Let `V` be a
nonnegative `C¹` profile on `(0,∞)` whose mass on every interval is at most `T`,
and fix a core `[c₁,c₂]` and a tolerance `ε > 0`.  Then there is a plateau
cut-off `χ` — vanishing at the two ends of its range, `[0,1]`-valued, equal to
`1` across the core — for which the cut-off homogeneous probe

  `L(W) = ∫(χ(r)/r²)·W(r)·r²dr`

is blind to the scaling direction up to `ε`,

  `|L(ΛV)| ≤ ε`,

while still seeing the profile with at least the core mass,

  `∫_{c₁}^{c₂} V ≤ L(V)`.

This is the `δ` of `ClayNS.gram_anchor_lower_bound_approx`, produced without any
spectral theory of the linearised operator: the residual can be pushed below any
tolerance by lengthening the logarithmic search range, while the anchor strength
stays fixed at the core mass. -/
theorem exists_small_residual_radial_probe
    {V V' : ℝ → ℝ} {c1 c2 T eps : ℝ} (hc1 : 0 < c1) (hc12 : c1 < c2) (heps : 0 < eps)
    (hV : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt V (V' r) r)
    (hV'c : ContinuousOn V' (Ioi 0))
    (hVnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ V r)
    (hmass : ∀ x y : ℝ, 0 < x → x ≤ y → (∫ r in x..y, V r) ≤ T) :
    ∃ (chi chi' : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a < b ∧
      (∀ r, HasDerivAt chi (chi' r) r) ∧ Continuous chi' ∧
      chi a = 0 ∧ chi b = 0 ∧ (∀ r, 0 ≤ chi r) ∧ (∀ r, chi r ≤ 1) ∧
      (∀ r ∈ Icc c1 c2, chi r = 1) ∧ (∀ r, r ≤ a ∨ b ≤ r → chi r = 0) ∧
      |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b| ≤ eps ∧
      (∫ r in c1..c2, V r) ≤ radProbe (fun r => chi r / r ^ 2) V a b := by
  obtain ⟨K, hKpos, hK⟩ := exists_smoothTransition_deriv_bound
  have hVcont : ContinuousOn V (Ioi 0) := fun r hr => (hV r hr).continuousAt.continuousWithinAt
  have hT0 : 0 ≤ T := by simpa using hmass c1 c1 hc1 le_rfl
  -- choose the number of dyadic scales: the residual will be at most `4KT/N`
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max 1 (4 * K * T / eps))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hNgt
  have hNR : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNR
  have hgapN : 4 * K * T / N < eps := by
    have hlt : 4 * K * T / eps < N := lt_of_le_of_lt (le_max_right _ _) hNgt
    rw [div_lt_iff₀ heps] at hlt
    rw [div_lt_iff₀ hNR]
    linarith
  have hpow : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ k := fun k => one_le_pow₀ (by norm_num)
  have hsubIoi : ∀ x y : ℝ, 0 < x → Icc x y ⊆ Ioi (0 : ℝ) := by
    intro x y hx z hz
    exact lt_of_lt_of_le hx hz.1
  -- the inner dyadic search range, of `N` scales below `c₁`
  set cin : ℝ := c1 / 2 ^ N with hcin
  have hcinpos : 0 < cin := by positivity
  have hcinN : cin * 2 ^ N = c1 :=
    div_mul_cancel₀ c1 (by positivity : ((2 : ℝ) ^ N) ≠ 0)
  have hcinle : cin ≤ c1 := by nlinarith [hpow N, hcinpos, hcinN]
  obtain ⟨i, hi, hinner⟩ := exists_good_dyadic_annulus (V := V) (T := T) hcinpos hNpos
    (hVcont.mono (by rw [hcinN]; exact hsubIoi _ _ hcinpos))
    (by rw [hcinN]; exact hmass cin c1 hcinpos hcinle)
  -- the outer dyadic search range, of `N` scales above `c₂`
  have hc2pos : 0 < c2 := lt_trans hc1 hc12
  obtain ⟨j, hj, houter⟩ := exists_good_dyadic_annulus (V := V) (T := T) hc2pos hNpos
    (hVcont.mono (hsubIoi _ _ hc2pos))
    (hmass c2 (c2 * 2 ^ N) hc2pos (by nlinarith [hpow N, hc2pos]))
  set a1 : ℝ := cin * 2 ^ i with ha1def
  set a2 : ℝ := cin * 2 ^ (i + 1) with ha2def
  set b1 : ℝ := c2 * 2 ^ j with hb1def
  set b2 : ℝ := c2 * 2 ^ (j + 1) with hb2def
  have ha1pos : 0 < a1 := by positivity
  have hdya : a2 = 2 * a1 := by rw [ha1def, ha2def, pow_succ]; ring
  have hdyb : b2 = 2 * b1 := by rw [hb1def, hb2def, pow_succ]; ring
  have h1 : a1 < a2 := by rw [hdya]; linarith
  have hb1pos : 0 < b1 := by positivity
  have h2 : b1 < b2 := by rw [hdyb]; linarith
  have ha2c1 : a2 ≤ c1 := by
    rw [ha2def, ← hcinN]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hi) hcinpos.le
  have hc2b1 : c2 ≤ b1 := by
    rw [hb1def]
    nlinarith [hpow j, hc2pos]
  have hab : a2 ≤ b1 := le_trans ha2c1 (le_trans hc12.le hc2b1)
  have ha1b2 : a1 < b2 := by linarith
  have hIcc : Icc a1 b2 ⊆ Ioi (0 : ℝ) := hsubIoi _ _ ha1pos
  have hVnnI : ∀ r ∈ Icc a1 b2, 0 ≤ V r := fun r hr => hVnn r (hIcc hr)
  have hVcI : ContinuousOn V (Icc a1 b2) := hVcont.mono hIcc
  -- the transition cost is at most `4KT/N < ε`
  have hcost := plateau_transition_cost_le (V := V) h1 h2 hab ha1pos hK hKpos.le hdya hdyb
    hVnnI hVcI hinner houter
  have hbulk := plateau_bulk_ge_core (V := V) h1 h2 ha2c1 hc12.le hc2b1 hVnnI hVcI
  have huIcc : uIcc a1 b2 = Icc a1 b2 := uIcc_of_le ha1b2.le
  have hresid : |radProbe (fun r => plateauCut a1 a2 b1 b2 r / r ^ 2) (radGen V V') a1 b2|
      ≤ ∫ r in a1..b2, |plateauCut' a1 a2 b1 b2 r| * r * |V r| :=
    radial_cutoff_probe_abs_le ha1pos ha1b2.le
      (fun r _ => hasDerivAt_plateauCut h1 h2 r)
      (fun r hr => hV r (hIcc (by rwa [huIcc] at hr)))
      (continuous_plateauCut' _ _ _ _).continuousOn
      (hV'c.mono (by rw [huIcc]; exact hIcc))
      (plateauCut_left_zero _ _ _ _) (plateauCut_right_zero _ _ _ _)
  refine ⟨plateauCut a1 a2 b1 b2, plateauCut' a1 a2 b1 b2, a1, b2, ha1pos, ha1b2,
    fun r => hasDerivAt_plateauCut h1 h2 r, continuous_plateauCut' _ _ _ _,
    plateauCut_left_zero _ _ _ _, plateauCut_right_zero _ _ _ _,
    plateauCut_nonneg _ _ _ _, plateauCut_le_one _ _ _ _,
    fun r hr => plateauCut_eq_one h1 h2 (le_trans ha2c1 hr.1) (le_trans hr.2 hc2b1),
    fun r hr => plateauCut_eq_zero_outside h1 h2 hr, ?_, ?_⟩
  · have hrw : 4 * K * (T / (N : ℝ)) = 4 * K * T / N := by ring
    rw [hrw] at hcost
    linarith [hresid, hcost, hgapN]
  · rw [radial_probe_bulk_eq (chi := plateauCut a1 a2 b1 b2) (V := V) ha1pos ha1b2.le]
    exact hbulk

/-! ## The separation criterion, discharged -/

/-- **A separating scale probe exists.**  If in addition the core mass is
strictly positive, the probe of the previous theorem — taken with tolerance
`ε = ½·(core mass)` — actually *separates*: it sees the profile strictly more
than it sees the scaling derivative,

  `|L(ΛV)| < L(V)`.

This discharges the hypothesis `hgap` of
`ClayNS.radial_probe_separates_sharp`. -/
theorem exists_separating_radial_probe
    {V V' : ℝ → ℝ} {c1 c2 T : ℝ} (hc1 : 0 < c1) (hc12 : c1 < c2)
    (hV : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt V (V' r) r)
    (hV'c : ContinuousOn V' (Ioi 0))
    (hVnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ V r)
    (hmass : ∀ x y : ℝ, 0 < x → x ≤ y → (∫ r in x..y, V r) ≤ T)
    (hcore : 0 < ∫ r in c1..c2, V r) :
    ∃ (chi chi' : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a < b ∧
      (∀ r, HasDerivAt chi (chi' r) r) ∧ Continuous chi' ∧
      chi a = 0 ∧ chi b = 0 ∧ (∀ r, 0 ≤ chi r) ∧ (∀ r, chi r ≤ 1) ∧
      (∀ r ∈ Icc c1 c2, chi r = 1) ∧ (∀ r, r ≤ a ∨ b ≤ r → chi r = 0) ∧
      |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
        < radProbe (fun r => chi r / r ^ 2) V a b := by
  obtain ⟨chi, chi', a, b, ha, hab, hd, hc', h0a, h0b, hnn, hle1, hone, hsupp, hres, hbulk⟩ :=
    exists_small_residual_radial_probe (V := V) (V' := V') (T := T)
      (eps := (∫ r in c1..c2, V r) / 2) hc1 hc12 (by linarith) hV hV'c hVnn hmass
  exact ⟨chi, chi', a, b, ha, hab, hd, hc', h0a, h0b, hnn, hle1, hone, hsupp, by linarith⟩

/-- **The anchor bracket is achievable.**  Whatever the a priori bound `Mc` on the
collinearity coefficient of the pair `(V, ΛV)`, one can choose the cut-off so
that the anchor bracket of `ClayNS.gram_anchor_lower_bound_approx` is strictly
positive:

  `Mc·δ < a₀`,  with `δ = |L(ΛV)|` and `a₀ = L(V)`.

So the hypothesis `hbracket` of the approximate anchor is not an extra
assumption on the profile: it is bought by lengthening the logarithmic search
range. -/
theorem exists_radial_probe_anchor_bracket
    {V V' : ℝ → ℝ} {c1 c2 T Mc : ℝ} (hc1 : 0 < c1) (hc12 : c1 < c2) (hMc : 0 ≤ Mc)
    (hV : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt V (V' r) r)
    (hV'c : ContinuousOn V' (Ioi 0))
    (hVnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ V r)
    (hmass : ∀ x y : ℝ, 0 < x → x ≤ y → (∫ r in x..y, V r) ≤ T)
    (hcore : 0 < ∫ r in c1..c2, V r) :
    ∃ (chi chi' : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a < b ∧
      (∀ r, HasDerivAt chi (chi' r) r) ∧ Continuous chi' ∧
      chi a = 0 ∧ chi b = 0 ∧ (∀ r, 0 ≤ chi r) ∧ (∀ r, chi r ≤ 1) ∧
      (∀ r ∈ Icc c1 c2, chi r = 1) ∧ (∀ r, r ≤ a ∨ b ≤ r → chi r = 0) ∧
      Mc * |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
        < radProbe (fun r => chi r / r ^ 2) V a b := by
  set TC : ℝ := ∫ r in c1..c2, V r with hTCdef
  have hden : 0 < 2 * (Mc + 1) := by linarith
  obtain ⟨chi, chi', a, b, ha, hab, hd, hc', h0a, h0b, hnn, hle1, hone, hsupp, hres, hbulk⟩ :=
    exists_small_residual_radial_probe (V := V) (V' := V') (T := T)
      (eps := TC / (2 * (Mc + 1))) hc1 hc12 (by positivity) hV hV'c hVnn hmass
  refine ⟨chi, chi', a, b, ha, hab, hd, hc', h0a, h0b, hnn, hle1, hone, hsupp, ?_⟩
  have hmul : Mc * |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      ≤ Mc * (TC / (2 * (Mc + 1))) := mul_le_mul_of_nonneg_left hres hMc
  have hd0 : 0 < TC / (2 * (Mc + 1)) := by positivity
  have hcancel : TC / (2 * (Mc + 1)) * (2 * (Mc + 1)) = TC := div_mul_cancel₀ _ hden.ne'
  have hlt : Mc * (TC / (2 * (Mc + 1))) < TC := by nlinarith [hd0, hcancel, hMc]
  linarith [hmul, hlt, hbulk]

end ClayNS
