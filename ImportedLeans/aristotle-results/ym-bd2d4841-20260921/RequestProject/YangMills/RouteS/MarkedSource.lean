/-
# `S₁`: the exact marked-source identity

Route `S` uses the source estimate through the identity

    ∂_{J_A} ∂_{J_B} log Z |_{J = 0} = Cov_μ(A, B),

i.e. the mixed second derivative of the log generating functional of a state is
the connected covariance of the two marked observables.  This file proves that
identity, for bounded observables of an arbitrary probability state, by
differentiating under the integral sign:

* `hasDerivAt_integral_mul_exp` — the analytic core: for bounded measurable `f`
  and `A`, `s ↦ ∫ f e^{sA}` is differentiable with derivative `∫ f A e^{sA}`;
* `hasDerivAt_log_source` — hence `u ↦ log ∫ e^{sA + uB}` is differentiable at
  `u = 0` with derivative the tilted mean `(∫ B e^{sA}) / (∫ e^{sA})`;
* `markedSource_mixed_deriv` — and the `s`-derivative of that tilted mean at
  `s = 0` is exactly `∫AB − ∫A·∫B`.  So the marked-source coordinate really is
  the connected covariance, not an unrelated quantity carrying the same name.

The literal corollary `wilson_markedSource_mixed_deriv` states it for the
Wilson–Gibbs state and *any* pair of continuous observables of the literal
lattice configuration space — in particular the Wilson loops of
`Lattice/WilsonLoop.lean`, which are continuous on a compact space and hence
automatically bounded.
-/
import Mathlib
import RequestProject.YangMills.RouteS.WilsonCovariance

namespace RequestProject.YangMills.RouteS

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

/-! ## Differentiating a tilted integral -/

/-- Bounded measurable functions are integrable in a finite measure. -/
theorem integrable_of_bound {mu : Measure X} [IsFiniteMeasure mu] {g : X → ℝ}
    (hg : AEStronglyMeasurable g mu) {M : ℝ} (hb : ∀ᵐ x ∂mu, ‖g x‖ ≤ M) :
    Integrable g mu :=
  Integrable.mono' (integrable_const M) hg hb

/-- **The analytic core of the marked-source identity.**  For bounded
measurable `f` and `A`, the tilted integral `s ↦ ∫ f e^{sA}` is differentiable
with the expected derivative. -/
theorem hasDerivAt_integral_mul_exp {mu : Measure X} [IsFiniteMeasure mu] {f A : X → ℝ}
    (hf : AEStronglyMeasurable f mu) (hA : AEStronglyMeasurable A mu) {MA Mf : ℝ}
    (hMA : 0 ≤ MA) (hMf : 0 ≤ Mf)
    (hAb : ∀ᵐ x ∂mu, |A x| ≤ MA) (hfb : ∀ᵐ x ∂mu, |f x| ≤ Mf) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, f x * Real.exp (s * A x) ∂mu)
      (∫ x, f x * A x * Real.exp (s0 * A x) ∂mu) s0 := by
  set R : ℝ := |s0| + 1 with hR
  set bound : X → ℝ := fun _ => Mf * MA * Real.exp (R * MA) with hbound
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun x => f x * Real.exp (s * A x)) mu :=
    fun s => hf.mul ((Real.continuous_exp.comp_aestronglyMeasurable (hA.const_mul s)))
  have hmeas' : ∀ s : ℝ, AEStronglyMeasurable (fun x => f x * A x * Real.exp (s * A x)) mu :=
    fun s => (hf.mul hA).mul ((Real.continuous_exp.comp_aestronglyMeasurable (hA.const_mul s)))
  have hballmem : Metric.ball s0 1 ∈ nhds s0 := Metric.ball_mem_nhds _ one_pos
  have hkey : ∀ᵐ x ∂mu, ∀ s ∈ Metric.ball s0 1,
      ‖f x * A x * Real.exp (s * A x)‖ ≤ bound x := by
    filter_upwards [hAb, hfb] with x hax hfx
    intro s hs
    have hsabs : |s| ≤ R := by
      have : |s - s0| < 1 := by simpa [Real.dist_eq] using hs
      have := abs_sub_abs_le_abs_sub s s0
      simp only [hR]
      linarith [abs_nonneg s]
    have hexp : Real.exp (s * A x) ≤ Real.exp (R * MA) := by
      refine Real.exp_le_exp.mpr ?_
      calc s * A x ≤ |s * A x| := le_abs_self _
        _ = |s| * |A x| := abs_mul _ _
        _ ≤ R * MA := by
            refine mul_le_mul hsabs hax (abs_nonneg _) ?_
            exact le_trans (abs_nonneg s) hsabs
    have h1 : |f x * A x| ≤ Mf * MA :=
      le_trans (le_of_eq (abs_mul _ _)) (mul_le_mul hfx hax (abs_nonneg _) hMf)
    calc ‖f x * A x * Real.exp (s * A x)‖
        = |f x * A x| * Real.exp (s * A x) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ (Mf * MA) * Real.exp (R * MA) :=
          mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)
  have hderiv : ∀ᵐ _x ∂mu, ∀ s ∈ Metric.ball s0 1, True := by
    filter_upwards with _ _ _ using trivial
  have hint0 : Integrable (fun x => f x * Real.exp (s0 * A x)) mu := by
    refine integrable_of_bound (hmeas s0) (M := Mf * Real.exp (R * MA)) ?_
    filter_upwards [hAb, hfb] with x hax hfx
    have hexp : Real.exp (s0 * A x) ≤ Real.exp (R * MA) := by
      refine Real.exp_le_exp.mpr ?_
      calc s0 * A x ≤ |s0 * A x| := le_abs_self _
        _ = |s0| * |A x| := abs_mul _ _
        _ ≤ R * MA := by
            refine mul_le_mul (by simp [hR]) hax (abs_nonneg _) (by positivity)
    calc ‖f x * Real.exp (s0 * A x)‖
        = |f x| * Real.exp (s0 * A x) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Mf * Real.exp (R * MA) := mul_le_mul hfx hexp (Real.exp_pos _).le hMf
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
    (F := fun s x => f x * Real.exp (s * A x))
    (F' := fun s x => f x * A x * Real.exp (s * A x))
    hballmem (Filter.Eventually.of_forall fun s => hmeas s) hint0 (hmeas' s0) hkey
    (integrable_const _) ?_
  · exact this.2
  · filter_upwards with x s _
    have h1 : HasDerivAt (fun s : ℝ => s * A x) (A x) s := by
      simpa using (hasDerivAt_id s).mul_const (A x)
    have := (Real.hasDerivAt_exp (s * A x)).comp s h1
    simpa [mul_comm, mul_assoc, mul_left_comm] using this.const_mul (f x)

/-! ## The marked-source identity -/

variable {mu : Measure X} [IsProbabilityMeasure mu] {A B : X → ℝ}

/-- The tilted partition function of the marked source `A`. -/
noncomputable def srcZ (mu : Measure X) (A : X → ℝ) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (s * A x) ∂mu

/-- The mean of `B` in the state tilted by `s·A`. -/
noncomputable def tiltedMean (mu : Measure X) (A B : X → ℝ) (s : ℝ) : ℝ :=
  (∫ x, B x * Real.exp (s * A x) ∂mu) / srcZ mu A s

theorem srcZ_pos (hA : AEStronglyMeasurable A mu) {MA : ℝ} (hAb : ∀ᵐ x ∂mu, |A x| ≤ MA)
    (s : ℝ) : 0 < srcZ mu A s := by
  have hint : Integrable (fun x => Real.exp (s * A x)) mu := by
    exact integrable_of_bound
      ((Real.continuous_exp.comp_aestronglyMeasurable (hA.const_mul s)))
      (M := Real.exp (|s| * MA)) (by
        filter_upwards [hAb] with x hax
        have hMA : 0 ≤ MA := le_trans (abs_nonneg _) hax
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        calc s * A x ≤ |s * A x| := le_abs_self _
          _ = |s| * |A x| := abs_mul _ _
          _ ≤ |s| * MA := by exact mul_le_mul_of_nonneg_left hax (abs_nonneg s))
  have hlow : ∀ᵐ x ∂mu, Real.exp (-(|s| * MA)) ≤ Real.exp (s * A x) := by
    filter_upwards [hAb] with x hax
    refine Real.exp_le_exp.mpr ?_
    have : -(|s| * |A x|) ≤ s * A x := by
      have := neg_abs_le (s * A x)
      rw [abs_mul] at this
      linarith
    have hmono : |s| * |A x| ≤ |s| * MA := mul_le_mul_of_nonneg_left hax (abs_nonneg s)
    linarith
  have hmono := integral_mono_ae (integrable_const _) hint hlow
  simp only [integral_const, smul_eq_mul] at hmono
  have hone : mu.real Set.univ = 1 := by simp
  rw [hone, one_mul] at hmono
  exact lt_of_lt_of_le (Real.exp_pos _) hmono

/-- **The `u`-derivative of the log generating functional** at `u = 0` is the
tilted mean of the second marked observable. -/
theorem hasDerivAt_log_source (hA : AEStronglyMeasurable A mu) (hB : AEStronglyMeasurable B mu)
    {MA MB : ℝ} (hMB : 0 ≤ MB) (hAb : ∀ᵐ x ∂mu, |A x| ≤ MA) (hBb : ∀ᵐ x ∂mu, |B x| ≤ MB)
    (s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log (∫ x, Real.exp (s * A x + u * B x) ∂mu))
      (tiltedMean mu A B s) 0 := by
  have hfmeas : AEStronglyMeasurable (fun x => Real.exp (s * A x)) mu :=
    Real.continuous_exp.comp_aestronglyMeasurable (hA.const_mul s)
  have hfb : ∀ᵐ x ∂mu, |Real.exp (s * A x)| ≤ Real.exp (|s| * MA) := by
    filter_upwards [hAb] with x hax
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * A x ≤ |s * A x| := le_abs_self _
      _ = |s| * |A x| := abs_mul _ _
      _ ≤ |s| * MA := mul_le_mul_of_nonneg_left hax (abs_nonneg s)
  have hd := hasDerivAt_integral_mul_exp (mu := mu) (f := fun x => Real.exp (s * A x))
    (A := B) hfmeas hB hMB (Real.exp_pos (|s| * MA)).le hBb hfb 0
  have hfun : (fun u : ℝ => ∫ x, Real.exp (s * A x + u * B x) ∂mu)
      = fun u : ℝ => ∫ x, Real.exp (s * A x) * Real.exp (u * B x) ∂mu := by
    funext u
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Real.exp_add])
  have hd0 : HasDerivAt (fun u : ℝ => ∫ x, Real.exp (s * A x + u * B x) ∂mu)
      (∫ x, B x * Real.exp (s * A x) ∂mu) 0 := by
    rw [hfun]
    have : (∫ x, Real.exp (s * A x) * B x * Real.exp (0 * B x) ∂mu)
        = ∫ x, B x * Real.exp (s * A x) ∂mu := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_comm]
    rwa [this] at hd
  have hZ : (∫ x, Real.exp (s * A x + 0 * B x) ∂mu) = srcZ mu A s := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [srcZ]
  have hpos : 0 < srcZ mu A s := srcZ_pos hA hAb s
  have := hd0.log (by rw [hZ]; exact ne_of_gt hpos)
  rw [hZ] at this
  exact this

/-- **The marked-source identity.**  The mixed second derivative of the log
generating functional at zero source is the connected covariance of the two
marked observables. -/
theorem markedSource_mixed_deriv (hA : AEStronglyMeasurable A mu)
    (hB : AEStronglyMeasurable B mu) {MA MB : ℝ} (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hAb : ∀ᵐ x ∂mu, |A x| ≤ MA) (hBb : ∀ᵐ x ∂mu, |B x| ≤ MB) :
    HasDerivAt
      (fun s : ℝ => deriv (fun u : ℝ => Real.log (∫ x, Real.exp (s * A x + u * B x) ∂mu)) 0)
      ((∫ x, A x * B x ∂mu) - (∫ x, A x ∂mu) * ∫ x, B x ∂mu) 0 := by
  have hinner : (fun s : ℝ =>
      deriv (fun u : ℝ => Real.log (∫ x, Real.exp (s * A x + u * B x) ∂mu)) 0)
      = tiltedMean mu A B := by
    funext s
    exact (hasDerivAt_log_source hA hB hMB hAb hBb s).deriv
  rw [hinner]
  -- numerator and denominator derivatives at `s = 0`
  have hnum := hasDerivAt_integral_mul_exp (mu := mu) (f := B) (A := A) hB hA hMA hMB hAb hBb 0
  have hden := hasDerivAt_integral_mul_exp (mu := mu) (f := fun _ => (1 : ℝ)) (A := A)
    aestronglyMeasurable_const hA hMA zero_le_one hAb
    (Filter.Eventually.of_forall fun x => by simp) 0
  have hnum' : HasDerivAt (fun s : ℝ => ∫ x, B x * Real.exp (s * A x) ∂mu)
      (∫ x, A x * B x ∂mu) 0 := by
    have heq : (∫ x, B x * A x * Real.exp (0 * A x) ∂mu) = ∫ x, A x * B x ∂mu := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_comm]
    rwa [heq] at hnum
  have hden' : HasDerivAt (fun s : ℝ => srcZ mu A s) (∫ x, A x ∂mu) 0 := by
    have heq : (∫ x, (1 : ℝ) * A x * Real.exp (0 * A x) ∂mu) = ∫ x, A x ∂mu := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hfun : (fun s : ℝ => ∫ x, (1 : ℝ) * Real.exp (s * A x) ∂mu) = srcZ mu A := by
      funext s
      simp [srcZ]
    rw [heq, hfun] at hden
    exact hden
  have hZ0 : srcZ mu A 0 = 1 := by
    simp only [srcZ, zero_mul, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
    simp
  have hne : srcZ mu A 0 ≠ 0 := by rw [hZ0]; norm_num
  have := hnum'.div hden' hne
  rw [hZ0] at this
  have hnum0 : (∫ x, B x * Real.exp (0 * A x) ∂mu) = ∫ x, B x ∂mu := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [hnum0] at this
  have hsimp : ((∫ x, A x * B x ∂mu) * 1 - (∫ x, B x ∂mu) * ∫ x, A x ∂mu) / 1 ^ 2
      = (∫ x, A x * B x ∂mu) - (∫ x, A x ∂mu) * ∫ x, B x ∂mu := by
    ring
  rw [hsimp] at this
  exact this

/-- The marked-source second derivative is literally the connected covariance
`cov` used by the `S₄` limit compiler, for real observables. -/
theorem cov_ofReal (nu : Measure X) {A B : X → ℝ} :
    cov nu (fun x => (A x : ℂ)) (fun x => (B x : ℂ))
      = (((∫ x, A x * B x ∂nu) - (∫ x, A x ∂nu) * ∫ x, B x ∂nu : ℝ) : ℂ) := by
  have h1 : (∫ x, (starRingEnd ℂ) ((A x : ℂ)) * ((B x : ℂ)) ∂nu)
      = ((∫ x, A x * B x ∂nu : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have h2 : (∫ x, ((A x : ℝ) : ℂ) ∂nu) = ((∫ x, A x ∂nu : ℝ) : ℂ) := integral_complex_ofReal
  have h3 : (∫ x, ((B x : ℝ) : ℂ) ∂nu) = ((∫ x, B x ∂nu : ℝ) : ℂ) := integral_complex_ofReal
  rw [cov, h1, h2, h3, Complex.conj_ofReal]
  push_cast
  ring

/-! ## The literal Wilson corollary -/

open RequestProject.YangMills.Lattice

/-- **`S₁` on the literal state.**  For the literal Wilson–Gibbs measure and any
two continuous observables of the lattice configuration space — in particular
the literal Wilson loops — the mixed second derivative of the log generating
functional is the connected covariance. -/
theorem wilson_markedSource_mixed_deriv {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    {A B : Conf n G → ℝ} (hA : Continuous A) (hB : Continuous B) :
    HasDerivAt
      (fun s : ℝ => deriv (fun u : ℝ =>
        Real.log (∫ U, Real.exp (s * A U + u * B U) ∂(gibbs n G beta chi))) 0)
      ((∫ U, A U * B U ∂(gibbs n G beta chi))
        - (∫ U, A U ∂(gibbs n G beta chi)) * ∫ U, B U ∂(gibbs n G beta chi)) 0 := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  obtain ⟨MA, hMA⟩ := isCompact_univ.exists_bound_of_continuousOn (f := A) hA.continuousOn
  obtain ⟨MB, hMB⟩ := isCompact_univ.exists_bound_of_continuousOn (f := B) hB.continuousOn
  have hMA0 : 0 ≤ MA := le_trans (norm_nonneg _) (hMA (Classical.arbitrary _) (Set.mem_univ _))
  have hMB0 : 0 ≤ MB := le_trans (norm_nonneg _) (hMB (Classical.arbitrary _) (Set.mem_univ _))
  refine markedSource_mixed_deriv hA.aestronglyMeasurable hB.aestronglyMeasurable
    (MA := MA) (MB := MB) hMA0 hMB0 ?_ ?_
  · exact Filter.Eventually.of_forall fun U => by
      simpa [Real.norm_eq_abs] using hMA U (Set.mem_univ U)
  · exact Filter.Eventually.of_forall fun U => by
      simpa [Real.norm_eq_abs] using hMB U (Set.mem_univ U)

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms hasDerivAt_integral_mul_exp
#print axioms hasDerivAt_log_source
#print axioms markedSource_mixed_deriv
#print axioms cov_ofReal
#print axioms wilson_markedSource_mixed_deriv

end Audit

end RequestProject.YangMills.RouteS
