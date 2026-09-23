/-
# Gauge-invariant observables are dense in the physical vacuum complement

`Lattice/DenseCorrelationExtension.lean` reduces the finite side of the mass gap
to a two-slice correlation estimate on a dense space of continuous observables.
The estimate demanded there is an estimate for *all* continuous observables,
gauge invariant or not.  But the physical Hilbert space of the lattice theory is
the gauge-invariant subspace, and the estimates constructive field theory
produces are estimates for gauge-invariant (Wilson-loop-type) observables.

This file closes that gap by averaging over the lattice gauge group:

* `gaugeAvg f` — the Haar average of a continuous observable over the lattice
  gauge group, again a continuous observable, and pointwise gauge invariant;
* `inner_obsToL2_gaugeAvg` — the inner product of any state with the averaged
  observable is the Haar average of its inner products with the gauge-rotated
  observable (Fubini on the literal measures);
* `norm_obsToL2_gaugeAvg_sub_le` — hence averaging does not increase the
  distance to a gauge-invariant state;
* `meanZero_invariant_obs_mem_closure` — so the mean-zero *gauge-invariant*
  continuous observables are dense in the vacuum complement of the physical
  (gauge-invariant) Hilbert space;
* `decorrelation_of_gauge_invariant_correlation`,
  `ym_uniform_gap_of_gauge_invariant_mixing` — the resulting weakening of the
  `F1` input: only the connected two-slice correlations of mean-zero
  gauge-invariant continuous observables need to be estimated.

As everywhere in this lane, no correlation estimate is proved here: the
interacting input is a displayed hypothesis in every statement.
-/
import Mathlib
import RequestProject.YangMills.Lattice.DenseCorrelationExtension
import RequestProject.YangMills.Lattice.GaugeInvariantSlice

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.GaugeInvariantL2Carrier
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## The gauge action -/

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The gauge action on slice configurations is jointly continuous. -/
theorem continuous_sliceGauge_uncurry :
    Continuous fun p : (SliceIdx n → G) × (Site n → G) => sliceGauge p.2 p.1 := by
  refine continuous_pi fun l => ?_
  exact (((continuous_apply (A := fun _ : Site n => G) l.1.1).comp continuous_snd).mul
      ((continuous_apply (A := fun _ : SliceIdx n => G) l).comp continuous_fst)).mul
    (((continuous_apply (A := fun _ : Site n => G)
      (l.1.1 + unitVec n l.1.2)).comp continuous_snd).inv)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The gauge transformations act on slice configurations as the lattice gauge
group. -/
theorem sliceGauge_mul (g h : Site n → G) (u : SliceIdx n → G) :
    sliceGauge g (sliceGauge h u) = sliceGauge (g * h) u := by
  funext l
  simp only [sliceGauge, Pi.mul_apply, mul_inv_rev]
  group

/-! ## Haar averaging of observables -/

/-- **The Haar average of an observable over the lattice gauge group.** -/
noncomputable def gaugeAvg (f : C(SliceIdx n → G, ℂ)) : C(SliceIdx n → G, ℂ) where
  toFun u := ∫ g, f (sliceGauge g u) ∂(prodHaar (Site n) G)
  continuous_toFun := by
    have hcont : Continuous (Function.uncurry
        fun (u : SliceIdx n → G) (g : Site n → G) => f (sliceGauge g u)) :=
      f.continuous.comp continuous_sliceGauge_uncurry
    simpa using continuous_parametric_integral_of_continuous
      (μ := prodHaar (Site n) G) hcont (isCompact_univ (X := Site n → G))

theorem gaugeAvg_apply (f : C(SliceIdx n → G, ℂ)) (u : SliceIdx n → G) :
    gaugeAvg f u = ∫ g, f (sliceGauge g u) ∂(prodHaar (Site n) G) := rfl

/-- **The Haar average is gauge invariant**, by right invariance of the Haar
measure of the lattice gauge group. -/
theorem gaugeAvg_invariant (f : C(SliceIdx n → G, ℂ)) (h : Site n → G) (u : SliceIdx n → G) :
    gaugeAvg f (sliceGauge h u) = gaugeAvg f u := by
  have hmp : MeasurePreserving (fun (U : Site n → G) => fun i => (1 : G) * U i * h i)
      (prodHaar (Site n) G) (prodHaar (Site n) G) := measurePreserving_translate 1 h
  have hfun : (fun (U : Site n → G) => fun i => (1 : G) * U i * h i) = fun U => U * h := by
    funext U i; simp
  rw [hfun] at hmp
  have hF : Continuous fun g : Site n → G => f (sliceGauge g u) :=
    f.continuous.comp (continuous_sliceGauge_uncurry.comp
      (Continuous.prodMk continuous_const continuous_id))
  calc gaugeAvg f (sliceGauge h u)
      = ∫ g, f (sliceGauge (g * h) u) ∂(prodHaar (Site n) G) := by
        rw [gaugeAvg_apply]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        dsimp only
        rw [sliceGauge_mul]
    _ = ∫ g, f (sliceGauge g u) ∂(Measure.map (fun U : Site n → G => U * h)
          (prodHaar (Site n) G)) := by
        rw [integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]
    _ = gaugeAvg f u := by rw [hmp.map_eq, gaugeAvg_apply]

/-! ## The gauge action on `L²` -/

/-- The gauge action on `L²` computes pointwise on representatives. -/
theorem coeFn_gaugeCLM (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : Site n → G)
    (F : SliceL2 n G beta chi) :
    (gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g F : _ → ℂ)
      =ᵐ[sliceMeasure n G beta chi] fun u => (F : _ → ℂ) (sliceGauge g u) :=
  Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) F
    (measurePreserving_sliceGauge hchi hconj beta g)

/-- The gauge action on `L²` is isometric. -/
theorem norm_gaugeCLM (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : Site n → G)
    (F : SliceL2 n G beta chi) :
    ‖gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g F‖ = ‖F‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (sliceGauge g)
    (measurePreserving_sliceGauge hchi hconj beta g)).norm_map F

/-- A pointwise gauge-invariant continuous observable defines a gauge-invariant
element of `L²`. -/
theorem obsToL2_mem_invariantSubspace (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    {f : C(SliceIdx n → G, ℂ)} (hf : ∀ g u, f (sliceGauge g u) = f u) :
    obsToL2 hchi beta f ∈ invariantSubspace (μ := sliceMeasure n G beta chi)
      (G := Site n → G) sliceGauge (measurePreserving_sliceGauge hchi hconj beta) := by
  rw [mem_invariantSubspace_iff]
  intro g
  refine Lp.ext ?_
  have hco := coeFn_obsToL2 hchi beta f
  have hco' := (measurePreserving_sliceGauge hchi hconj beta g).quasiMeasurePreserving.ae hco
  filter_upwards [coeFn_gaugeCLM hchi hconj beta g (obsToL2 hchi beta f), hco, hco']
    with u h1 h2 h3
  rw [h1, h3, h2, hf]

/-! ## Averaging and the inner product -/

section Averaging

/-- The inner product of a state with a gauge-rotated observable, as an integral
against the literal slice measure. -/
theorem inner_gaugeCLM_obsToL2 (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    (f : C(SliceIdx n → G, ℂ)) (h : SliceL2 n G beta chi) (g : Site n → G) :
    ⟪h, gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
        (obsToL2 hchi beta f)⟫_ℂ
      = ∫ u, (starRingEnd ℂ) ((h : _ → ℂ) u) * f (sliceGauge g u)
          ∂(sliceMeasure n G beta chi) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_gaugeCLM hchi hconj beta g (obsToL2 hchi beta f),
    (measurePreserving_sliceGauge hchi hconj beta g).quasiMeasurePreserving.ae
      (coeFn_obsToL2 hchi beta f)] with u h1 h2
  rw [RCLike.inner_apply, h1, h2]
  ring

/-- The two-variable integrand of the averaging computation is integrable. -/
theorem integrable_conj_mul_gauge (hchi : Continuous chi) (beta : ℝ)
    (f : C(SliceIdx n → G, ℂ)) (h : SliceL2 n G beta chi) :
    Integrable (fun z : (SliceIdx n → G) × (Site n → G) =>
      (starRingEnd ℂ) ((h : _ → ℂ) z.1) * f (sliceGauge z.2 z.1))
      ((sliceMeasure n G beta chi).prod (prodHaar (Site n) G)) := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  have hh : Integrable (fun u => (h : _ → ℂ) u) (sliceMeasure n G beta chi) :=
    (Lp.memLp h).integrable (by norm_num)
  have h1 : Integrable (fun u => (starRingEnd ℂ) ((h : _ → ℂ) u))
      (sliceMeasure n G beta chi) :=
    ⟨Complex.continuous_conj.comp_aestronglyMeasurable hh.aestronglyMeasurable, by
      simpa [HasFiniteIntegral] using hh.2⟩
  have hprodint := h1.mul_prod (integrable_const (μ := prodHaar (Site n) G) (1 : ℂ))
  have hmeasm : AEStronglyMeasurable (fun z : (SliceIdx n → G) × (Site n → G) =>
      f (sliceGauge z.2 z.1)) ((sliceMeasure n G beta chi).prod (prodHaar (Site n) G)) :=
    (f.continuous.comp continuous_sliceGauge_uncurry).aestronglyMeasurable
  have hboundm : ∀ᵐ z ∂((sliceMeasure n G beta chi).prod (prodHaar (Site n) G)),
      ‖f (sliceGauge z.2 z.1)‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _
  simpa [mul_comm] using hprodint.bdd_mul hmeasm hboundm

/-- Pairings with the gauge-rotated observable are integrable over the gauge
group. -/
theorem integrable_inner_gaugeCLM (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    (f : C(SliceIdx n → G, ℂ)) (h : SliceL2 n G beta chi) :
    Integrable (fun g => ⟪h, gaugeCLM sliceGauge
        (measurePreserving_sliceGauge hchi hconj beta) g (obsToL2 hchi beta f)⟫_ℂ)
      (prodHaar (Site n) G) := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  have hint := (integrable_conj_mul_gauge hchi beta f h).integral_prod_right
  refine hint.congr ?_
  filter_upwards with g
  rw [← inner_gaugeCLM_obsToL2 hchi hconj beta f h g]

/-- **The inner product with the Haar average is the Haar average of the inner
products.** -/
theorem inner_obsToL2_gaugeAvg (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    (f : C(SliceIdx n → G, ℂ)) (h : SliceL2 n G beta chi) :
    ⟪h, obsToL2 hchi beta (gaugeAvg f)⟫_ℂ
      = ∫ g, ⟪h, gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
          (obsToL2 hchi beta f)⟫_ℂ ∂(prodHaar (Site n) G) := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  have hinner : ∀ F : SliceL2 n G beta chi,
      ⟪h, F⟫_ℂ = ∫ u, (starRingEnd ℂ) ((h : _ → ℂ) u) * (F : _ → ℂ) u
        ∂(sliceMeasure n G beta chi) := by
    intro F
    simp [L2.inner_def, RCLike.inner_apply, mul_comm]
  calc ⟪h, obsToL2 hchi beta (gaugeAvg f)⟫_ℂ
      = ∫ u, (starRingEnd ℂ) ((h : _ → ℂ) u) * gaugeAvg f u ∂(sliceMeasure n G beta chi) := by
        rw [hinner]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_obsToL2 hchi beta (gaugeAvg f)] with u hu
        rw [hu]
    _ = ∫ u, ∫ g, (starRingEnd ℂ) ((h : _ → ℂ) u) * f (sliceGauge g u)
          ∂(prodHaar (Site n) G) ∂(sliceMeasure n G beta chi) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [gaugeAvg_apply, ← integral_const_mul]
    _ = ∫ g, ∫ u, (starRingEnd ℂ) ((h : _ → ℂ) u) * f (sliceGauge g u)
          ∂(sliceMeasure n G beta chi) ∂(prodHaar (Site n) G) :=
        integral_integral_swap (integrable_conj_mul_gauge hchi beta f h)
    _ = ∫ g, ⟪h, gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
          (obsToL2 hchi beta f)⟫_ℂ ∂(prodHaar (Site n) G) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        dsimp only
        rw [inner_gaugeCLM_obsToL2 hchi hconj beta f h g]

/-- **Averaging is a contraction towards gauge-invariant states**: the Haar
average of an observable is at least as good an `L²` approximation of a
gauge-invariant state as the observable itself. -/
theorem norm_obsToL2_gaugeAvg_sub_le (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    (f : C(SliceIdx n → G, ℂ)) {ψ : SliceL2 n G beta chi}
    (hψ : ψ ∈ invariantSubspace (μ := sliceMeasure n G beta chi) (G := Site n → G)
      sliceGauge (measurePreserving_sliceGauge hchi hconj beta)) :
    ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ ≤ ‖obsToL2 hchi beta f - ψ‖ := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  rw [mem_invariantSubspace_iff] at hψ
  have hsplit : ∀ g : Site n → G,
      ⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
          gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
            (obsToL2 hchi beta f - ψ)⟫_ℂ
        = ⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
            gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
              (obsToL2 hchi beta f)⟫_ℂ
          - ⟪obsToL2 hchi beta (gaugeAvg f) - ψ, ψ⟫_ℂ := by
    intro g
    rw [map_sub, inner_sub_right, hψ g]
  have hpair : ∫ g, ⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
        gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
          (obsToL2 hchi beta f - ψ)⟫_ℂ ∂(prodHaar (Site n) G)
      = ⟪obsToL2 hchi beta (gaugeAvg f) - ψ, obsToL2 hchi beta (gaugeAvg f) - ψ⟫_ℂ := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_sub (integrable_inner_gaugeCLM hchi hconj beta f
        (obsToL2 hchi beta (gaugeAvg f) - ψ)) (integrable_const _),
      ← inner_obsToL2_gaugeAvg hchi hconj beta f (obsToL2 hchi beta (gaugeAvg f) - ψ),
      integral_const]
    have huniv : (prodHaar (Site n) G).real Set.univ = 1 := by
      simp [measureReal_def]
    rw [huniv, one_smul, ← inner_sub_right]
  have hbound : ‖⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
      obsToL2 hchi beta (gaugeAvg f) - ψ⟫_ℂ‖
        ≤ ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ * ‖obsToL2 hchi beta f - ψ‖ := by
    rw [← hpair]
    have hle : ∀ᵐ g ∂(prodHaar (Site n) G),
        ‖⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
            gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
              (obsToL2 hchi beta f - ψ)⟫_ℂ‖
          ≤ ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ * ‖obsToL2 hchi beta f - ψ‖ := by
      filter_upwards with g
      calc ‖⟪obsToL2 hchi beta (gaugeAvg f) - ψ,
              gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
                (obsToL2 hchi beta f - ψ)⟫_ℂ‖
          ≤ ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ *
              ‖gaugeCLM sliceGauge (measurePreserving_sliceGauge hchi hconj beta) g
                (obsToL2 hchi beta f - ψ)‖ := norm_inner_le_norm _ _
        _ = ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ * ‖obsToL2 hchi beta f - ψ‖ := by
            rw [norm_gaugeCLM hchi hconj beta g (obsToL2 hchi beta f - ψ)]
    simpa using norm_integral_le_of_norm_le
      (integrable_const (‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ * ‖obsToL2 hchi beta f - ψ‖)) hle
  have hvv : ‖⟪obsToL2 hchi beta (gaugeAvg f) - ψ, obsToL2 hchi beta (gaugeAvg f) - ψ⟫_ℂ‖
      = ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  rw [hvv] at hbound
  rcases eq_or_lt_of_le (norm_nonneg (obsToL2 hchi beta (gaugeAvg f) - ψ)) with hzero | hpos
  · rw [← hzero]
    exact norm_nonneg _
  · nlinarith [hbound, hpos]

end Averaging

/-! ## Density in the physical vacuum complement -/

/-- **Mean-zero gauge-invariant continuous observables are dense in the vacuum
complement of the physical Hilbert space.** -/
theorem meanZero_invariant_obs_mem_closure (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    (ψ : SliceL2 n G beta chi)
    (hinv : ψ ∈ invariantSubspace (μ := sliceMeasure n G beta chi) (G := Site n → G)
      sliceGauge (measurePreserving_sliceGauge hchi hconj beta))
    (hvac : ⟪vacuum hchi beta, ψ⟫_ℂ = 0) :
    ψ ∈ closure {v : SliceL2 n G beta chi | ∃ f : C(SliceIdx n → G, ℂ),
      (∀ g u, f (sliceGauge g u) = f u) ∧ (∫ u, f u ∂(sliceMeasure n G beta chi)) = 0
        ∧ obsToL2 hchi beta f = v} := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- approximate by a continuous observable
  obtain ⟨F, hF⟩ := Metric.mem_closure_iff.1
    ((dense_obsToL2_image hchi beta (S := ⊤) (by simp)) ψ) (ε / 2) (by linarith)
  obtain ⟨⟨f, -, rfl⟩, hfdist⟩ := hF
  -- average it: still continuous, now gauge invariant, and no worse
  have haverage : ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ ≤ ‖obsToL2 hchi beta f - ψ‖ :=
    norm_obsToL2_gaugeAvg_sub_le hchi hconj beta f hinv
  have hfnorm : ‖obsToL2 hchi beta f - ψ‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]
    simpa using hfdist
  -- subtract the mean: the constant is gauge invariant, so invariance survives
  set m : ℂ := ∫ u, gaugeAvg f u ∂(sliceMeasure n G beta chi) with hm
  set g0 : C(SliceIdx n → G, ℂ) := gaugeAvg f - ContinuousMap.const _ m with hg0
  have hg0inv : ∀ g u, g0 (sliceGauge g u) = g0 u := by
    intro g u
    simp [hg0, gaugeAvg_invariant f g u]
  have hmean0 : (∫ u, g0 u ∂(sliceMeasure n G beta chi)) = 0 := by
    have hint : Integrable (fun u => gaugeAvg f u) (sliceMeasure n G beta chi) :=
      (gaugeAvg f).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [show (fun u => g0 u) = fun u => gaugeAvg f u - m from rfl,
      integral_sub hint (integrable_const m)]
    simp [hm]
  have hg0L2 : obsToL2 hchi beta g0 = obsToL2 hchi beta (gaugeAvg f) - m • vacuum hchi beta := by
    rw [hg0, map_sub]
    congr 1
    rw [vacuum_eq_obsToL2_one hchi beta, ← map_smul]
    congr 1
    ext u
    simp
  have hminner : m = ⟪vacuum hchi beta, obsToL2 hchi beta (gaugeAvg f)⟫_ℂ := by
    rw [inner_vacuum_obsToL2 hchi beta (gaugeAvg f)]
  have hmle : ‖m‖ ≤ ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ := by
    have hsub : m = ⟪vacuum hchi beta, obsToL2 hchi beta (gaugeAvg f) - ψ⟫_ℂ := by
      rw [inner_sub_right, hvac, sub_zero, hminner]
    rw [hsub]
    calc ‖⟪vacuum hchi beta, obsToL2 hchi beta (gaugeAvg f) - ψ⟫_ℂ‖
        ≤ ‖vacuum hchi beta‖ * ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ := norm_inner_le_norm _ _
      _ = ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ := by rw [norm_vacuum hchi beta, one_mul]
  refine ⟨obsToL2 hchi beta g0, ⟨g0, hg0inv, hmean0, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, hg0L2]
  have hsplit : obsToL2 hchi beta (gaugeAvg f) - m • vacuum hchi beta - ψ
      = (obsToL2 hchi beta (gaugeAvg f) - ψ) - m • vacuum hchi beta := by abel
  rw [hsplit]
  calc ‖obsToL2 hchi beta (gaugeAvg f) - ψ - m • vacuum hchi beta‖
      ≤ ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ + ‖m • vacuum hchi beta‖ := norm_sub_le _ _
    _ = ‖obsToL2 hchi beta (gaugeAvg f) - ψ‖ + ‖m‖ := by
        rw [norm_smul, norm_vacuum hchi beta, mul_one]
    _ ≤ ‖obsToL2 hchi beta f - ψ‖ + ‖obsToL2 hchi beta f - ψ‖ := by
        have := hmle.trans haverage
        linarith [haverage]
    _ < ε := by linarith

/-! ## `F1` from gauge-invariant correlation estimates -/

/-- **The two-slice estimate for physical states from gauge-invariant
correlation bounds.**  If the connected two-slice correlation of the literal
Wilson–Gibbs measure is bounded by `c` times the `L²` norm squared for every
mean-zero *gauge-invariant* continuous observable, then the two-slice estimate
holds for every gauge-invariant state orthogonal to the vacuum — which is
exactly what the finite-spacing gap on the physical Hilbert space consumes. -/
theorem decorrelation_of_gauge_invariant_correlation (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) {c : ℝ}
    (hbound : ∀ f : C(SliceIdx n → G, ℂ), (∀ g u, f (sliceGauge g u) = f u) →
      (∫ u, f u ∂(sliceMeasure n G beta chi)) = 0 →
        ‖∫ U, (starRingEnd ℂ) (f (slice0 U)) * f (slice1 U) ∂(gibbs n G beta chi)‖
          ≤ c * ∫ u, ‖f u‖ ^ 2 ∂(sliceMeasure n G beta chi))
    (ψ : SliceL2 n G beta chi)
    (hinv : ψ ∈ invariantSubspace (μ := sliceMeasure n G beta chi) (G := Site n → G)
      sliceGauge (measurePreserving_sliceGauge hchi hconj beta))
    (hvac : ⟪vacuum hchi beta, ψ⟫_ℂ = 0) :
    ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2 := by
  have hD : ∀ v ∈ {v : SliceL2 n G beta chi | ∃ f : C(SliceIdx n → G, ℂ),
        (∀ g u, f (sliceGauge g u) = f u) ∧ (∫ u, f u ∂(sliceMeasure n G beta chi)) = 0
          ∧ obsToL2 hchi beta f = v},
      ‖⟪(embed0 n G beta chi).toContinuousLinearMap v,
          (embed1 hchi beta).toContinuousLinearMap v⟫_ℂ‖ ≤ c * ‖v‖ ^ 2 := by
    rintro v ⟨f, hfinv, hmean, rfl⟩
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [inner_embed_obsToL2 hchi beta f, norm_obsToL2_sq hchi beta f]
    exact hbound f hfinv hmean
  have hmem := meanZero_invariant_obs_mem_closure hchi hconj beta ψ hinv hvac
  have := decorrelation_of_mem_closure hD hmem
  simpa only [LinearIsometry.coe_toContinuousLinearMap] using this

/-- **The trajectory form**: gauge-invariant connected two-slice correlation
bounds `c_k` plus the spectral defect condition `Δ·a_k ≤ 1 − c_k` give the
uniform vacuum form gap of the literal physical Hamiltonians, which is the
finite-side input of the continuum weld. -/
theorem ym_uniform_gap_of_gauge_invariant_mixing (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {cs : ℕ → ℝ} {Δ : ℝ}
    (hbound : ∀ k, ∀ f : C(SliceIdx (vol k) → SU2, ℂ), (∀ g u, f (sliceGauge g u) = f u) →
      (∫ u, f u ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2)) = 0 →
        ‖∫ U, (starRingEnd ℂ) (f (slice0 U)) * f (slice1 U)
            ∂(gibbs (vol k) SU2 (beta k) chiSU2)‖
          ≤ cs k * ∫ u, ‖f u‖ ^ 2 ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2))
    (hdefect : ∀ k, Δ * a k ≤ 1 - cs k) :
    ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a (fun k => (hapos k).le) k)
      (ymTrajectoryVacuum vol beta k) Δ :=
  ym_uniform_gap_of_trajectory_decorrelation vol beta a (fun k => (hapos k).le)
    (fun k ψ hψ =>
      decorrelation_of_gauge_invariant_correlation (G := SU2) continuous_chiSU2 chiSU2_conj
        (beta k) (hbound k) (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2) ψ.2 hψ)
    (trajectory_gap_bound_of_defect hapos hdefect)

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms gaugeAvg_invariant
#print axioms obsToL2_mem_invariantSubspace
#print axioms inner_obsToL2_gaugeAvg
#print axioms norm_obsToL2_gaugeAvg_sub_le
#print axioms meanZero_invariant_obs_mem_closure
#print axioms decorrelation_of_gauge_invariant_correlation
#print axioms ym_uniform_gap_of_gauge_invariant_mixing

end Audit
