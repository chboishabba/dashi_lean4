/-
# Strong coupling: a proved mass gap for the literal lattice theory at small `β`

`Lattice/FreeCoupling.lean` inhabits the finite-spacing package of the literal
Wilson theory at the single point `β = 0`, where the Gibbs measure degenerates to
the product Haar measure and the two time slices are exactly independent.  This
file removes that degeneracy: it proves the coercivity estimate

`Δ ‖ψ‖² ≤ Re q(ψ,ψ)`   for `ψ ⟂ Ω`

for the literal Wilson energy form on an explicit *open* range of couplings, with
`Δ` an explicit function of a uniform bound `M` on the Wilson action.  The
mechanism is a Doeblin-type comparison of the Wilson–Gibbs measure with the
product Haar measure: the Radon–Nikodym density of the Gibbs measure with respect
to the product Haar measure lies in `[e^{-2M}, e^{2M}]`, so the two time slices
are *almost* independent, and the exact independence used at `β = 0` is replaced
by a quantitative decorrelation estimate.

The chain of the argument is:

* `gibbs_eq_withDensity` — the literal Gibbs measure is the product Haar measure
  weighted by the explicit real density `e^{-S}/Z`;
* `le_gibbsRealDensity`, `gibbsRealDensity_le` — two-sided bounds on that density
  coming from the uniform bound on the Wilson action on the compact configuration
  space;
* `prodHaar_le_smul_gibbs`, `haarSlice_le_smul_sliceMeasure` — the resulting
  comparison of measures, which transports square integrability from the Gibbs
  slice measure to the Haar slice measure;
* `norm_inner_embed_le` — the quantitative decorrelation estimate for the
  transfer term of the energy form, proved by splitting the density as
  `e^{-2M} + (density − e^{-2M})`, applying exact independence to the first piece
  and Cauchy–Schwarz to the second;
* `energyForm_coercive_of_small_action` — the coercivity estimate, and
* `ym_hasLatticeCoercivity_of_small_coupling`, `ym_massGap_small_coupling` — the
  literal `SU(2)` mass-gap conclusion for every coupling below an explicit
  threshold.

As in `FreeCoupling.lean` this is a statement at fixed lattice spacing: the
threshold shrinks as the lattice volume grows and the gap is measured in units of
`a⁻¹`, so nothing here bears on the continuum limit; see `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.FreeCoupling

namespace RequestProject.YangMills.Lattice

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## Two general measure-theoretic helpers -/

/-- Cauchy–Schwarz for the lower Lebesgue integral of a product of two norms. -/
theorem lintegral_enorm_mul_le {X : Type*} [MeasurableSpace X] (m : Measure X)
    {F H : X → ℂ} (hF : AEMeasurable F m) (hH : AEMeasurable H m) :
    ∫⁻ x, ‖F x‖ₑ * ‖H x‖ₑ ∂m
      ≤ (∫⁻ x, ‖F x‖ₑ ^ 2 ∂m) ^ ((1 : ℝ) / 2) * (∫⁻ x, ‖H x‖ₑ ^ 2 ∂m) ^ ((1 : ℝ) / 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  simpa [ENNReal.rpow_natCast] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq m hpq hF.enorm hH.enorm

/-- The square of the `L²` norm as a lower Lebesgue integral. -/
theorem lintegral_enorm_sq_eq_ofReal {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ψ : Lp ℂ 2 m) :
    ∫⁻ a, ‖(ψ : X → ℂ) a‖ₑ ^ 2 ∂m = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have h1 : eLpNorm (ψ : X → ℂ) 2 m = (∫⁻ a, ‖(ψ : X → ℂ) a‖ₑ ^ 2 ∂m) ^ ((1 : ℝ) / 2) := by
    simpa using eLpNorm_eq_lintegral_rpow_enorm_toReal (f := (ψ : X → ℂ)) (p := 2) (μ := m)
      (by norm_num) (by norm_num)
  have h2 : eLpNorm (ψ : X → ℂ) 2 m = ENNReal.ofReal ‖ψ‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ψ)]
  have h3 := h1.symm.trans h2
  have h4 : ((∫⁻ a, ‖(ψ : X → ℂ) a‖ₑ ^ 2 ∂m) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)
      = (ENNReal.ofReal ‖ψ‖) ^ (2 : ℝ) := by rw [h3]
  rw [← ENNReal.rpow_mul] at h4
  norm_num at h4
  rw [h4, h2, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-! ## Two-sided bounds on the partition function -/

theorem partition_le_ofReal_exp (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    partition n G beta chi ≤ ENNReal.ofReal (Real.exp M) := by
  have hle : ∀ U : Conf n G, gibbsDensity beta chi U ≤ ENNReal.ofReal (Real.exp M) := fun U => by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM U)).1
    linarith
  have hmono : ∫⁻ U : Conf n G, gibbsDensity beta chi U ∂(prodHaar (Link n) G)
      ≤ ∫⁻ _ : Conf n G, ENNReal.ofReal (Real.exp M) ∂(prodHaar (Link n) G) :=
    lintegral_mono hle
  simpa [partition, gibbsUnnorm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_const, measure_univ] using hmono

theorem ofReal_exp_neg_le_partition (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    ENNReal.ofReal (Real.exp (-M)) ≤ partition n G beta chi := by
  have hge : ∀ U : Conf n G, ENNReal.ofReal (Real.exp (-M)) ≤ gibbsDensity beta chi U := fun U => by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM U)).2
    linarith
  have hmono : ∫⁻ _ : Conf n G, ENNReal.ofReal (Real.exp (-M)) ∂(prodHaar (Link n) G)
      ≤ ∫⁻ U : Conf n G, gibbsDensity beta chi U ∂(prodHaar (Link n) G) :=
    lintegral_mono hge
  simpa [partition, gibbsUnnorm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_const, measure_univ] using hmono

theorem partition_toReal_pos (hchi : Continuous chi) (beta : ℝ) :
    0 < (partition n G beta chi).toReal :=
  ENNReal.toReal_pos (partition_ne_zero hchi beta) (partition_ne_top hchi beta)

theorem partition_toReal_le_exp (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    (partition n G beta chi).toReal ≤ Real.exp M := by
  have h := partition_le_ofReal_exp (n := n) beta hM
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa [ENNReal.toReal_ofReal (Real.exp_pos M).le] using this

theorem exp_neg_le_partition_toReal (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    Real.exp (-M) ≤ (partition n G beta chi).toReal := by
  have h := ofReal_exp_neg_le_partition (n := n) beta hM
  have := ENNReal.toReal_mono (partition_ne_top hchi beta) h
  simpa [ENNReal.toReal_ofReal (Real.exp_pos (-M)).le] using this

/-! ## The Gibbs measure as a weighted product Haar measure -/

/-- The literal real Radon–Nikodym density of the Wilson–Gibbs measure with
respect to the product Haar measure: `e^{-S(U)}/Z`. -/
noncomputable def gibbsRealDensity (beta : ℝ) (chi : G → ℝ) (U : Conf n G) : ℝ :=
  Real.exp (-wilsonAction beta chi U) / (partition n G beta chi).toReal

theorem gibbsRealDensity_pos (hchi : Continuous chi) (beta : ℝ) (U : Conf n G) :
    0 < gibbsRealDensity beta chi U :=
  div_pos (Real.exp_pos _) (partition_toReal_pos hchi beta)

/-- **The Wilson–Gibbs measure is the product Haar measure with the explicit
density `e^{-S}/Z`.** -/
theorem gibbs_eq_withDensity (hchi : Continuous chi) (beta : ℝ) :
    gibbs n G beta chi
      = (prodHaar (Link n) G).withDensity
          (fun U => ENNReal.ofReal (gibbsRealDensity beta chi U)) := by
  have hZt : partition n G beta chi ≠ ⊤ := partition_ne_top hchi beta
  have hZr : 0 < (partition n G beta chi).toReal := partition_toReal_pos hchi beta
  rw [gibbs, gibbsUnnorm, ← withDensity_smul _ (measurable_gibbsDensity hchi beta)]
  congr 1
  funext U
  simp only [Pi.smul_apply, smul_eq_mul, gibbsDensity, gibbsRealDensity]
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hZr)),
    ENNReal.ofReal_inv_of_pos hZr, ENNReal.ofReal_toReal hZt]

/-! ## Two-sided bounds on the density -/

theorem le_gibbsRealDensity (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) (U : Conf n G) :
    (Real.exp (2 * M))⁻¹ ≤ gibbsRealDensity beta chi U := by
  have hZr : 0 < (partition n G beta chi).toReal := partition_toReal_pos hchi beta
  rw [gibbsRealDensity, le_div_iff₀ hZr]
  have h1 : (Real.exp (2 * M))⁻¹ * (partition n G beta chi).toReal
      ≤ (Real.exp (2 * M))⁻¹ * Real.exp M :=
    mul_le_mul_of_nonneg_left (partition_toReal_le_exp beta hM) (by positivity)
  refine h1.trans ?_
  rw [← Real.exp_neg, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM U)).2])

theorem gibbsRealDensity_le (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) (U : Conf n G) :
    gibbsRealDensity beta chi U ≤ Real.exp (2 * M) := by
  have hZr : 0 < (partition n G beta chi).toReal := partition_toReal_pos hchi beta
  rw [gibbsRealDensity, div_le_iff₀ hZr]
  have h1 : Real.exp (-wilsonAction beta chi U) ≤ Real.exp M :=
    Real.exp_le_exp.2 (by linarith [(abs_le.1 (hM U)).1])
  refine h1.trans ?_
  have h2 : Real.exp M = Real.exp (2 * M) * Real.exp (-M) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_left (exp_neg_le_partition_toReal hchi beta hM)
    (Real.exp_pos _).le

/-! ## Comparison of the product Haar measure with the Gibbs measure -/

theorem prodHaar_le_smul_gibbs (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    prodHaar (Link n) G ≤ ENNReal.ofReal (Real.exp (2 * M)) • gibbs n G beta chi := by
  have hpos : (0 : ℝ) < Real.exp (2 * M) := Real.exp_pos _
  have hd : (fun _ : Conf n G => ENNReal.ofReal (Real.exp (2 * M))⁻¹)
      ≤ᵐ[prodHaar (Link n) G] fun U => ENNReal.ofReal (gibbsRealDensity beta chi U) :=
    Filter.Eventually.of_forall fun U =>
      ENNReal.ofReal_le_ofReal (le_gibbsRealDensity hchi beta hM U)
  have h1 : ENNReal.ofReal (Real.exp (2 * M))⁻¹ • prodHaar (Link n) G ≤ gibbs n G beta chi := by
    rw [gibbs_eq_withDensity hchi beta, ← withDensity_const]
    exact withDensity_mono hd
  have h2 : ENNReal.ofReal (Real.exp (2 * M)) * ENNReal.ofReal (Real.exp (2 * M))⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]
  calc prodHaar (Link n) G
      = ENNReal.ofReal (Real.exp (2 * M))
          • (ENNReal.ofReal (Real.exp (2 * M))⁻¹ • prodHaar (Link n) G) := by
        rw [smul_smul, h2, one_smul]
    _ ≤ ENNReal.ofReal (Real.exp (2 * M)) • gibbs n G beta chi := by
        refine Measure.le_iff'.2 fun s => ?_
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul' (le_refl _) (h1 s)

/-- The distribution of the time-zero slice under the product Haar measure. -/
noncomputable def haarSlice (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] : Measure (SliceIdx n → G) :=
  Measure.map slice0 (prodHaar (Link n) G)

instance isProbabilityMeasure_haarSlice : IsProbabilityMeasure (haarSlice n G) :=
  Measure.isProbabilityMeasure_map measurable_slice0.aemeasurable

theorem measurePreserving_slice0_haar :
    MeasurePreserving (slice0 (n := n) (G := G)) (prodHaar (Link n) G) (haarSlice n G) :=
  ⟨measurable_slice0, rfl⟩

theorem measurePreserving_slice1_haar :
    MeasurePreserving (slice1 (n := n) (G := G)) (prodHaar (Link n) G) (haarSlice n G) :=
  measurePreserving_slice0_haar.comp (measurePreserving_translateConf (unitVec n 0))

theorem haarSlice_le_smul_sliceMeasure (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M) :
    haarSlice n G ≤ ENNReal.ofReal (Real.exp (2 * M)) • sliceMeasure n G beta chi := by
  have h := Measure.map_mono (prodHaar_le_smul_gibbs hchi beta hM) measurable_slice0
  rwa [Measure.map_smul] at h

/-! ## Integration against the Gibbs measure -/

theorem measurable_gibbsRealDensity (hchi : Continuous chi) (beta : ℝ) :
    Measurable (gibbsRealDensity (n := n) beta chi) :=
  ((Real.measurable_exp.comp (measurable_wilsonAction hchi beta).neg)).div_const _

/-- Integration against the Wilson–Gibbs measure, rewritten as integration
against the product Haar measure with the explicit density. -/
theorem integral_gibbs_eq (hchi : Continuous chi) (beta : ℝ) (g : Conf n G → ℂ) :
    ∫ U, g U ∂(gibbs n G beta chi)
      = ∫ U, (gibbsRealDensity beta chi U : ℂ) * g U ∂(prodHaar (Link n) G) := by
  rw [gibbs_eq_withDensity hchi beta,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun U => ENNReal.ofReal (gibbsRealDensity beta chi U))
      (measurable_gibbsRealDensity hchi beta).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [ENNReal.toReal_ofReal (gibbsRealDensity_pos hchi beta U).le, Complex.real_smul]

/-- A weighted integral is controlled by the sup norm of the weight times the
`L¹` norm of the integrand. -/
theorem norm_integral_weighted_le {X : Type*} [MeasurableSpace X] (m : Measure X)
    {w : X → ℝ} {h : X → ℂ} {a : ℝ} (ha0 : 0 ≤ a) (ha : ∀ x, |w x| ≤ a)
    (hfin : ∫⁻ x, ‖h x‖ₑ ∂m ≠ ⊤) :
    ‖∫ x, ((w x : ℝ) : ℂ) * h x ∂m‖ ≤ a * (∫⁻ x, ‖h x‖ₑ ∂m).toReal := by
  have hpt : ∀ x, ‖((w x : ℝ) : ℂ) * h x‖ₑ ≤ ENNReal.ofReal a * ‖h x‖ₑ := by
    intro x
    rw [enorm_mul]
    refine mul_le_mul' ?_ (le_refl _)
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (ha x)
  calc ‖∫ x, ((w x : ℝ) : ℂ) * h x ∂m‖
      ≤ (∫⁻ x, ‖((w x : ℝ) : ℂ) * h x‖ₑ ∂m).toReal := by
        simpa only [ofReal_norm_eq_enorm] using
          norm_integral_le_lintegral_norm (μ := m) (fun x => ((w x : ℝ) : ℂ) * h x)
    _ ≤ (ENNReal.ofReal a * ∫⁻ x, ‖h x‖ₑ ∂m).toReal := by
        refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ?_
        exact (lintegral_mono hpt).trans_eq
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = a * (∫⁻ x, ‖h x‖ₑ ∂m).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0]

/-! ## The quantitative decorrelation estimate -/

/-- **The transfer term of the literal Wilson energy form is small on the vacuum
complement when the Wilson action is uniformly small.**  The proof splits the
Radon–Nikodym density of the Gibbs measure with respect to the product Haar
measure into its infimum plus a remainder: the infimum part factorises exactly by
independence of the two time slices and is killed by the vacuum orthogonality up
to the density oscillation, and the remainder is estimated by Cauchy–Schwarz. -/
theorem norm_inner_embed_le (h01 : (0 : ZMod (n + 1)) ≠ 1) (hchi : Continuous chi)
    (beta : ℝ) {M : ℝ} (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M)
    (ψ : SliceL2 n G beta chi) (hψ : ⟪ vacuum hchi beta, ψ ⟫_ℂ = 0) :
    ‖⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ‖
      ≤ ((Real.exp (2 * M) - 1) ^ 2 + (Real.exp (2 * M)) ^ 2 - 1) * ‖ψ‖ ^ 2 := by
  haveI := isProbabilityMeasure_gibbs (n := n) hchi beta
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  have hM0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hM fun _ => 1)
  have hCpos : (0 : ℝ) < Real.exp (2 * M) := Real.exp_pos _
  have hC1 : (1 : ℝ) ≤ Real.exp (2 * M) := Real.one_le_exp (by linarith)
  have hdlo := le_gibbsRealDensity hchi beta hM
  have hdhi := gibbsRealDensity_le hchi beta hM
  -- square integrability against the product Haar measure
  have hmem_s : MemLp (ψ : _ → ℂ) 2 (sliceMeasure n G beta chi) := Lp.memLp ψ
  have hmem_h : MemLp (ψ : _ → ℂ) 2 (haarSlice n G) :=
    MemLp.of_measure_le_smul ENNReal.ofReal_ne_top
      (haarSlice_le_smul_sliceMeasure hchi beta hM) hmem_s
  have hF : MemLp (fun U => (ψ : _ → ℂ) (slice0 U)) 2 (prodHaar (Link n) G) :=
    hmem_h.comp_measurePreserving measurePreserving_slice0_haar
  have hG : MemLp (fun U => (ψ : _ → ℂ) (slice1 U)) 2 (prodHaar (Link n) G) :=
    hmem_h.comp_measurePreserving measurePreserving_slice1_haar
  have hFc : MemLp (fun U => (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U))) 2
      (prodHaar (Link n) G) := by simpa [Complex.star_def] using hF.star
  have hGint : Integrable (fun U => (ψ : _ → ℂ) (slice1 U)) (prodHaar (Link n) G) :=
    hG.integrable (by norm_num)
  have hgint : Integrable (fun U => (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U))
      * (ψ : _ → ℂ) (slice1 U)) (prodHaar (Link n) G) := by
    simpa using hFc.integrable_mul hG
  -- transport of lower Lebesgue integrals along the slice maps
  have hcomp : ∀ (p : Conf n G → (SliceIdx n → G)),
      MeasurePreserving p (prodHaar (Link n) G) (haarSlice n G) →
      ∀ (Φ : (SliceIdx n → G) → ℝ≥0∞), AEMeasurable Φ (haarSlice n G) →
      ∫⁻ U, Φ (p U) ∂(prodHaar (Link n) G) = ∫⁻ u, Φ u ∂(haarSlice n G) := by
    intro p hp Φ hΦ
    rw [← hp.map_eq] at hΦ ⊢
    exact (lintegral_map' hΦ hp.measurable.aemeasurable).symm
  have hae : AEMeasurable (fun u => ‖(ψ : _ → ℂ) u‖ₑ) (haarSlice n G) :=
    hmem_h.1.aemeasurable.enorm
  have hae2 : AEMeasurable (fun u => ‖(ψ : _ → ℂ) u‖ₑ ^ 2) (haarSlice n G) := hae.pow_const 2
  set T1 : ℝ≥0∞ := ∫⁻ u, ‖(ψ : _ → ℂ) u‖ₑ ∂(haarSlice n G) with hT1def
  set T2 : ℝ≥0∞ := ∫⁻ u, ‖(ψ : _ → ℂ) u‖ₑ ^ 2 ∂(haarSlice n G) with hT2def
  have hT2le : T2 ≤ ENNReal.ofReal (Real.exp (2 * M) * ‖ψ‖ ^ 2) := by
    have h1 : T2 ≤ ∫⁻ u, ‖(ψ : _ → ℂ) u‖ₑ ^ 2
        ∂(ENNReal.ofReal (Real.exp (2 * M)) • sliceMeasure n G beta chi) :=
      lintegral_mono' (haarSlice_le_smul_sliceMeasure hchi beta hM) (le_refl _)
    rwa [lintegral_smul_measure, lintegral_enorm_sq_eq_ofReal ψ, smul_eq_mul,
      ← ENNReal.ofReal_mul hCpos.le] at h1
  have hT2top : T2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT2le
  have hT1le : T1 ≤ T2 ^ ((1 : ℝ) / 2) := by
    have h := lintegral_enorm_mul_le (haarSlice n G) (F := fun u => (ψ : _ → ℂ) u)
      (H := fun _ => (1 : ℂ)) hmem_h.1.aemeasurable aemeasurable_const
    simpa [hT1def, hT2def, measure_univ] using h
  have hT1top : T1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT2top) hT1le
  have ht1nonneg : (0 : ℝ) ≤ T1.toReal := ENNReal.toReal_nonneg
  have ht2nonneg : (0 : ℝ) ≤ T2.toReal := ENNReal.toReal_nonneg
  have ht2 : T2.toReal ≤ Real.exp (2 * M) * ‖ψ‖ ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT2le
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have ht1sq : T1.toReal ^ 2 ≤ T2.toReal := by
    have h1 : T1.toReal ≤ T2.toReal ^ ((1 : ℝ) / 2) := by
      have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT2top) hT1le
      rwa [← ENNReal.toReal_rpow] at h
    rw [← Real.sqrt_eq_rpow] at h1
    nlinarith [Real.sq_sqrt ht2nonneg, Real.sqrt_nonneg T2.toReal]
  -- the Cauchy–Schwarz bound for the joint integral
  have he0 : ∫⁻ U, ‖(ψ : _ → ℂ) (slice0 U)‖ₑ ^ 2 ∂(prodHaar (Link n) G) = T2 :=
    hcomp slice0 measurePreserving_slice0_haar _ hae2
  have he1 : ∫⁻ U, ‖(ψ : _ → ℂ) (slice1 U)‖ₑ ^ 2 ∂(prodHaar (Link n) G) = T2 :=
    hcomp slice1 measurePreserving_slice1_haar _ hae2
  have hf1 : ∫⁻ U, ‖(ψ : _ → ℂ) (slice1 U)‖ₑ ∂(prodHaar (Link n) G) = T1 :=
    hcomp slice1 measurePreserving_slice1_haar _ hae
  have hf0 : ∫⁻ U, ‖(starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U))‖ₑ ∂(prodHaar (Link n) G) = T1 := by
    simp only [RCLike.enorm_conj]
    exact hcomp slice0 measurePreserving_slice0_haar _ hae
  have hsq : T2 ^ ((1 : ℝ) / 2) * T2 ^ ((1 : ℝ) / 2) = T2 := by
    rw [← pow_two, ← ENNReal.rpow_natCast (T2 ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have hCS : ∫⁻ U, ‖(starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)‖ₑ
      ∂(prodHaar (Link n) G) ≤ T2 := by
    have h := lintegral_enorm_mul_le (prodHaar (Link n) G)
      (F := fun U => (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)))
      (H := fun U => (ψ : _ → ℂ) (slice1 U)) hFc.1.aemeasurable hG.1.aemeasurable
    simp only [enorm_mul, RCLike.enorm_conj] at h ⊢
    rw [he0, he1, hsq] at h
    exact h
  have hCStop : ∫⁻ U, ‖(starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)‖ₑ
      ∂(prodHaar (Link n) G) ≠ ⊤ := ne_top_of_le_ne_top hT2top hCS
  -- the splitting of the density
  have hmeasw : ∀ c : ℝ, AEStronglyMeasurable
      (fun U => ((gibbsRealDensity beta chi U - c : ℝ) : ℂ)) (prodHaar (Link n) G) := fun c =>
    (Complex.measurable_ofReal.comp
      ((measurable_gibbsRealDensity hchi beta).sub_const c)).aestronglyMeasurable
  have hbdd2 : ∀ U : Conf n G,
      |gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹|
        ≤ Real.exp (2 * M) - (Real.exp (2 * M))⁻¹ := by
    intro U
    rw [abs_of_nonneg (by linarith [hdlo U])]
    linarith [hdhi U]
  have hint2 : Integrable (fun U =>
      ((gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
        * ((starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)))
      (prodHaar (Link n) G) :=
    hgint.bdd_mul (hmeasw _) (Filter.Eventually.of_forall fun U => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hbdd2 U)
  have hsplit : ∫ U, (gibbsRealDensity beta chi U : ℂ)
        * ((starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U))
        ∂(prodHaar (Link n) G)
      = (((Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
          * (∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)
              ∂(prodHaar (Link n) G))
        + ∫ U, ((gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
            * ((starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U))
            ∂(prodHaar (Link n) G) := by
    rw [← integral_const_mul, ← integral_add (hgint.const_mul _) hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    push_cast
    ring
  -- the factorisation of the leading term
  have hfac : ∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)
      ∂(prodHaar (Link n) G)
      = (∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(prodHaar (Link n) G))
        * (∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G)) := by
    have hind := indepFun_slice (n := n) (G := G) h01
    have hf' : AEStronglyMeasurable (fun u => (starRingEnd ℂ) ((ψ : _ → ℂ) u))
        (Measure.map slice0 (prodHaar (Link n) G)) :=
      Complex.continuous_conj.comp_aestronglyMeasurable hmem_h.1
    have hg' : AEStronglyMeasurable (fun u => (ψ : _ → ℂ) u)
        (Measure.map slice1 (prodHaar (Link n) G)) := by
      rw [measurePreserving_slice1_haar.map_eq]; exact hmem_h.1
    exact hind.integral_comp_mul_comp measurable_slice0.aemeasurable
      measurePreserving_slice1_haar.measurable.aemeasurable hf' hg'
  -- the two averages vanish against the Gibbs measure
  have hzero1 : ∫ U, (ψ : _ → ℂ) (slice1 U) ∂(gibbs n G beta chi) = 0 := by
    have hmap : Measure.map (slice1 (n := n) (G := G)) (gibbs n G beta chi)
        = sliceMeasure n G beta chi := (measurePreserving_slice1 hchi beta).map_eq
    have h := integral_map (φ := slice1 (n := n) (G := G)) (μ := gibbs n G beta chi)
      (f := fun u => (ψ : _ → ℂ) u)
      (measurePreserving_slice1 hchi beta).measurable.aemeasurable
      (by rw [hmap]; exact hmem_s.1)
    rw [hmap] at h
    rw [← h, ← inner_vacuum_eq_integral hchi beta ψ, hψ]
  have hzero0 : ∫ U, (ψ : _ → ℂ) (slice0 U) ∂(gibbs n G beta chi) = 0 := by
    have hmap : Measure.map (slice0 (n := n) (G := G)) (gibbs n G beta chi)
        = sliceMeasure n G beta chi := (measurePreserving_slice0 (n := n) beta chi).map_eq
    have h := integral_map (φ := slice0 (n := n) (G := G)) (μ := gibbs n G beta chi)
      (f := fun u => (ψ : _ → ℂ) u) measurable_slice0.aemeasurable
      (by rw [hmap]; exact hmem_s.1)
    rw [hmap] at h
    rw [← h, ← inner_vacuum_eq_integral hchi beta ψ, hψ]
  -- hence the two Haar averages are controlled by the density oscillation
  have hbdd1 : ∀ U : Conf n G, |1 - gibbsRealDensity beta chi U| ≤ Real.exp (2 * M) - 1 := by
    intro U
    rw [abs_le]
    constructor
    · linarith [hdhi U]
    · have h2 : (2 - Real.exp (2 * M)) * Real.exp (2 * M) ≤ 1 := by
        nlinarith [sq_nonneg (Real.exp (2 * M) - 1)]
      have hinv : 2 - Real.exp (2 * M) ≤ (Real.exp (2 * M))⁻¹ := by
        calc 2 - Real.exp (2 * M)
            = ((2 - Real.exp (2 * M)) * Real.exp (2 * M)) * (Real.exp (2 * M))⁻¹ := by
              field_simp
          _ ≤ 1 * (Real.exp (2 * M))⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (Real.exp (2 * M))⁻¹ := one_mul _
      linarith [hdlo U]
  have hmeasd : AEStronglyMeasurable (fun U => ((gibbsRealDensity beta chi U : ℝ) : ℂ))
      (prodHaar (Link n) G) :=
    (Complex.measurable_ofReal.comp (measurable_gibbsRealDensity hchi beta)).aestronglyMeasurable
  have hintd1 : Integrable (fun U => ((gibbsRealDensity beta chi U : ℝ) : ℂ)
      * (ψ : _ → ℂ) (slice1 U)) (prodHaar (Link n) G) :=
    hGint.bdd_mul hmeasd
      (Filter.Eventually.of_forall fun U => by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (gibbsRealDensity_pos hchi beta U).le]
        exact hdhi U)
  have hE1 : ∫ U, ((1 - gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice1 U)
      ∂(prodHaar (Link n) G)
      = ∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G) := by
    have hfun : (fun U => ((1 - gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice1 U))
        = fun U => (ψ : _ → ℂ) (slice1 U)
            - ((gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice1 U) := by
      funext U; push_cast; ring
    have hg1 : ∫ U, ((gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice1 U)
        ∂(prodHaar (Link n) G) = 0 := by
      rw [← integral_gibbs_eq hchi beta]; exact hzero1
    rw [hfun, integral_sub hGint hintd1, hg1, sub_zero]
  have hbE1 : ‖∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G)‖
      ≤ (Real.exp (2 * M) - 1) * T1.toReal := by
    rw [← hE1, ← hf1]
    exact norm_integral_weighted_le _ (by linarith) hbdd1 (hf1 ▸ hT1top)
  have hbE0 : ‖∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(prodHaar (Link n) G)‖
      ≤ (Real.exp (2 * M) - 1) * T1.toReal := by
    have hFint : Integrable (fun U => (ψ : _ → ℂ) (slice0 U)) (prodHaar (Link n) G) :=
      hF.integrable (by norm_num)
    have hintd0 : Integrable (fun U => ((gibbsRealDensity beta chi U : ℝ) : ℂ)
        * (ψ : _ → ℂ) (slice0 U)) (prodHaar (Link n) G) :=
      hFint.bdd_mul hmeasd
        (Filter.Eventually.of_forall fun U => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gibbsRealDensity_pos hchi beta U).le]
          exact hdhi U)
    have hE0 : ∫ U, ((1 - gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice0 U)
        ∂(prodHaar (Link n) G)
        = ∫ U, (ψ : _ → ℂ) (slice0 U) ∂(prodHaar (Link n) G) := by
      have hfun : (fun U => ((1 - gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice0 U))
          = fun U => (ψ : _ → ℂ) (slice0 U)
              - ((gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice0 U) := by
        funext U; push_cast; ring
      have hg0 : ∫ U, ((gibbsRealDensity beta chi U : ℝ) : ℂ) * (ψ : _ → ℂ) (slice0 U)
          ∂(prodHaar (Link n) G) = 0 := by
        rw [← integral_gibbs_eq hchi beta]; exact hzero0
      rw [hfun, integral_sub hFint hintd0, hg0, sub_zero]
    have hT1' : ∫⁻ U, ‖(ψ : _ → ℂ) (slice0 U)‖ₑ ∂(prodHaar (Link n) G) = T1 :=
      hcomp slice0 measurePreserving_slice0_haar _ hae
    have hb : ‖∫ U, (ψ : _ → ℂ) (slice0 U) ∂(prodHaar (Link n) G)‖
        ≤ (Real.exp (2 * M) - 1) * T1.toReal := by
      rw [← hE0, ← hT1']
      exact norm_integral_weighted_le _ (by linarith) hbdd1 (hT1' ▸ hT1top)
    rw [integral_conj]
    rwa [RCLike.norm_conj]
  -- the remainder term
  have hbS : ‖∫ U, ((gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
        * ((starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U))
        ∂(prodHaar (Link n) G)‖
      ≤ (Real.exp (2 * M) - (Real.exp (2 * M))⁻¹) * T2.toReal := by
    have h := norm_integral_weighted_le (prodHaar (Link n) G)
      (w := fun U => gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹)
      (h := fun U => (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U))
      (by nlinarith [hdlo (fun _ => 1), hdhi (fun _ => 1)]) hbdd2 hCStop
    refine h.trans ?_
    have hco : (0 : ℝ) ≤ Real.exp (2 * M) - (Real.exp (2 * M))⁻¹ := by
      nlinarith [hdlo (fun _ => 1), hdhi (fun _ => 1)]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hT2top hCS) hco
  -- assembling
  have hmain : ⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ
      = (((Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
          * ((∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(prodHaar (Link n) G))
            * (∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G)))
        + ∫ U, ((gibbsRealDensity beta chi U - (Real.exp (2 * M))⁻¹ : ℝ) : ℂ)
            * ((starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U))
            ∂(prodHaar (Link n) G) := by
    rw [inner_embed_eq_integral hchi beta ψ ψ, integral_gibbs_eq hchi beta, hsplit, hfac]
  rw [hmain]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.exp (2 * M))⁻¹)]
  have hkey : (Real.exp (2 * M))⁻¹
      * (‖∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(prodHaar (Link n) G)‖
        * ‖∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G)‖)
      ≤ (Real.exp (2 * M) - 1) ^ 2 * ‖ψ‖ ^ 2 := by
    have hprod : ‖∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(prodHaar (Link n) G)‖
        * ‖∫ U, (ψ : _ → ℂ) (slice1 U) ∂(prodHaar (Link n) G)‖
        ≤ ((Real.exp (2 * M) - 1) * T1.toReal) * ((Real.exp (2 * M) - 1) * T1.toReal) :=
      mul_le_mul hbE0 hbE1 (norm_nonneg _) (by nlinarith)
    have hstep : (Real.exp (2 * M))⁻¹
        * (((Real.exp (2 * M) - 1) * T1.toReal) * ((Real.exp (2 * M) - 1) * T1.toReal))
        ≤ (Real.exp (2 * M) - 1) ^ 2 * ‖ψ‖ ^ 2 := by
      have h1 : ((Real.exp (2 * M) - 1) * T1.toReal) * ((Real.exp (2 * M) - 1) * T1.toReal)
          ≤ (Real.exp (2 * M) - 1) ^ 2 * (Real.exp (2 * M) * ‖ψ‖ ^ 2) := by
        nlinarith [ht1sq, ht2, sq_nonneg (Real.exp (2 * M) - 1)]
      have h2 : (Real.exp (2 * M))⁻¹ * ((Real.exp (2 * M) - 1) ^ 2
          * (Real.exp (2 * M) * ‖ψ‖ ^ 2)) = (Real.exp (2 * M) - 1) ^ 2 * ‖ψ‖ ^ 2 := by
        field_simp
      calc (Real.exp (2 * M))⁻¹
            * (((Real.exp (2 * M) - 1) * T1.toReal) * ((Real.exp (2 * M) - 1) * T1.toReal))
          ≤ (Real.exp (2 * M))⁻¹ * ((Real.exp (2 * M) - 1) ^ 2
              * (Real.exp (2 * M) * ‖ψ‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (Real.exp (2 * M) - 1) ^ 2 * ‖ψ‖ ^ 2 := h2
    exact le_trans (mul_le_mul_of_nonneg_left hprod (by positivity)) hstep
  have hrem : (Real.exp (2 * M) - (Real.exp (2 * M))⁻¹) * T2.toReal
      ≤ ((Real.exp (2 * M)) ^ 2 - 1) * ‖ψ‖ ^ 2 := by
    have hco : (0 : ℝ) ≤ Real.exp (2 * M) - (Real.exp (2 * M))⁻¹ := by
      nlinarith [hdlo (fun _ => 1), hdhi (fun _ => 1)]
    have h1 : (Real.exp (2 * M) - (Real.exp (2 * M))⁻¹) * T2.toReal
        ≤ (Real.exp (2 * M) - (Real.exp (2 * M))⁻¹) * (Real.exp (2 * M) * ‖ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht2 hco
    refine h1.trans (le_of_eq ?_)
    field_simp
  linarith [hbS, hkey, hrem]

/-! ## Coercivity of the literal energy form -/

/-- **The literal Wilson energy form is coercive on the vacuum complement**
whenever the Wilson action is uniformly bounded by `M` with
`(e^{2M} - 1)^2 + e^{4M} < 2`.  At `M = 0` the constant is `1`, recovering the
zero-coupling estimate of `FreeCoupling.lean`. -/
theorem energyForm_coercive_of_small_action (h01 : (0 : ZMod (n + 1)) ≠ 1)
    (hchi : Continuous chi) (beta : ℝ) {M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M)
    (ψ : SliceL2 n G beta chi) (hψ : ⟪ vacuum hchi beta, ψ ⟫_ℂ = 0) :
    (2 - (Real.exp (2 * M) - 1) ^ 2 - (Real.exp (2 * M)) ^ 2) * ‖ψ‖ ^ 2
      ≤ ((energyForm hchi beta).form ψ ψ).re := by
  have h := norm_inner_embed_le h01 hchi beta hM ψ hψ
  have hre : (⟪ ψ, ψ ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hBA : ⟪ embed1 hchi beta ψ, embed0 n G beta chi ψ ⟫_ℂ
      = (starRingEnd ℂ) ⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [energyForm_apply, hBA]
  have hhalf : (1 / 2 : ℂ) * (⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ
      + (starRingEnd ℂ) ⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ)
      = ((⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ).re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  rw [hhalf, Complex.sub_re, Complex.ofReal_re, hre]
  nlinarith [Complex.re_le_norm ⟪ embed0 n G beta chi ψ, embed1 hchi beta ψ ⟫_ℂ, h]

/-! ## The literal `SU(2)` theory at small coupling -/

/-- The real part of a quaternion is bounded by its norm. -/
theorem abs_quaternion_re_le_norm (q : Quaternion ℝ) : |q.re| ≤ ‖q‖ := by
  have h : ‖q‖ ^ 2 = Quaternion.normSq q := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self]
  have h2 : q.re ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [h, Quaternion.normSq_def']
    nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
  nlinarith [abs_nonneg q.re, norm_nonneg q, sq_abs q.re]

/-- The Wilson character of `SU(2)` is bounded by `2`. -/
theorem abs_chiSU2_le (g : SU2) : |chiSU2 g| ≤ 2 := by
  have hg : ‖(g : Quaternion ℝ)‖ = 1 := by
    have := g.2
    rwa [mem_sphere_iff_norm, sub_zero] at this
  have h := abs_quaternion_re_le_norm (g : Quaternion ℝ)
  rw [hg] at h
  rw [chiSU2_eq, abs_mul]
  simp only [abs_two]
  linarith

theorem card_site (n : ℕ) : Fintype.card (Site n) = (n + 1) ^ 4 := by
  simp [Site, ZMod.card]

/-- **An explicit bound on the literal `SU(2)` Wilson action**: `32|β|(n+1)^4`. -/
theorem abs_wilsonAction_SU2_le (beta : ℝ) (U : Conf n SU2) :
    |wilsonAction beta chiSU2 U| ≤ 32 * |beta| * ((n : ℝ) + 1) ^ 4 := by
  have hcard : (Fintype.card (Site n) : ℝ) = ((n : ℝ) + 1) ^ 4 := by
    rw [card_site]; push_cast; ring
  have h3 : ∀ (x : Site n) (mu : Fin 4),
      |∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)| ≤ 8 := by
    intro x mu
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ nu : Fin 4, |chiSU2 (plaqHol U x mu nu)|
        ≤ ∑ _nu : Fin 4, (2 : ℝ) := Finset.sum_le_sum fun nu _ => abs_chiSU2_le _
      _ = 8 := by norm_num
  have h2 : ∀ x : Site n, |∑ mu : Fin 4, ∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)| ≤ 32 := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ mu : Fin 4, |∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)|
        ≤ ∑ _mu : Fin 4, (8 : ℝ) := Finset.sum_le_sum fun mu _ => h3 x mu
      _ = 32 := by norm_num
  have hsum : |∑ x : Site n, ∑ mu : Fin 4, ∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)|
      ≤ 32 * ((n : ℝ) + 1) ^ 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x : Site n, |∑ mu : Fin 4, ∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)|
        ≤ ∑ _x : Site n, (32 : ℝ) := Finset.sum_le_sum fun x _ => h2 x
      _ = (Fintype.card (Site n) : ℝ) * 32 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 32 * ((n : ℝ) + 1) ^ 4 := by rw [hcard]; ring
  rw [wilsonAction, abs_mul, abs_neg]
  calc |beta| * |∑ x : Site n, ∑ mu : Fin 4, ∑ nu : Fin 4, chiSU2 (plaqHol U x mu nu)|
      ≤ |beta| * (32 * ((n : ℝ) + 1) ^ 4) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 32 * |beta| * ((n : ℝ) + 1) ^ 4 := by ring

/-- **The coercivity estimate for the literal `SU(2)` Wilson energy form** at any
coupling for which the Wilson action is uniformly bounded by `M`. -/
theorem ym_hasLatticeCoercivity_of_small_action {n : ℕ} (hn : 1 ≤ n) {beta a M : ℝ}
    (hM : ∀ U : Conf n SU2, |wilsonAction beta chiSU2 U| ≤ M) (ha : 0 < a) :
    HasLatticeCoercivity n beta a
      (a⁻¹ * (2 - (Real.exp (2 * M) - 1) ^ 2 - (Real.exp (2 * M)) ^ 2)) ha.le := by
  intro ψ hψ
  have hq := energyForm_coercive_of_small_action (zero_ne_one_zmod hn) continuous_chiSU2
    beta hM ψ hψ
  rw [ymEnergyForm, scaleForm_apply, Complex.re_ofReal_mul]
  have hnn : (0 : ℝ) ≤ a⁻¹ := (inv_pos.2 ha).le
  nlinarith [hq]

/-- **The literal four-dimensional `SU(2)` lattice Yang–Mills theory has a mass
gap at every coupling whose Wilson action is uniformly small.**  The conclusion is
the full vacuum-sector statement: the form gap, absence of an eigenvalue below the
gap, unique solvability of `Hψ − λψ = y` on the vacuum sector for every `λ < Δ`,
and the resolvent bound.  This is a fixed-lattice-spacing theorem; the gap is
measured in units of `a⁻¹`. -/
theorem ym_massGap_of_small_action {n : ℕ} (hn : 1 ≤ n) {beta a M : ℝ}
    (hM : ∀ U : Conf n SU2, |wilsonAction beta chiSU2 U| ≤ M)
    (hMsmall : (Real.exp (2 * M) - 1) ^ 2 + (Real.exp (2 * M)) ^ 2 < 2) (ha : 0 < a) :
    Clay.MassGapConclusion (ymHamiltonian n beta a ha.le) (ymVacuum n beta)
      (a⁻¹ * (2 - (Real.exp (2 * M) - 1) ^ 2 - (Real.exp (2 * M)) ^ 2)) :=
  lattice_massGap_of_coercivity n beta a (mul_pos (inv_pos.2 ha) (by linarith)) ha.le
    (ym_hasLatticeCoercivity_of_small_action hn hM ha)

/-- **The same conclusion with an explicit threshold on the inverse coupling**: the
literal `SU(2)` lattice theory on the periodic lattice with `n+1` sites per
direction has a positive mass gap at lattice spacing `a` whenever
`(e^{64|β|(n+1)^4} - 1)^2 + e^{128|β|(n+1)^4} < 2`, which holds for all
sufficiently small `|β|`. -/
theorem ym_massGap_of_small_coupling {n : ℕ} (hn : 1 ≤ n) {beta a : ℝ} (ha : 0 < a)
    (hbeta : (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4)) - 1) ^ 2
        + (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4))) ^ 2 < 2) :
    Clay.MassGapConclusion (ymHamiltonian n beta a ha.le) (ymVacuum n beta)
      (a⁻¹ * (2 - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4)) - 1) ^ 2
        - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4))) ^ 2)) :=
  ym_massGap_of_small_action hn (abs_wilsonAction_SU2_le beta) hbeta ha

/-- The smallness condition is satisfied whenever `t ≤ 1/10`; in particular the
coupling range of `ym_massGap_of_small_coupling` is a genuine neighbourhood of
zero, not the single point `β = 0`. -/
theorem exp_smallness {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10) :
    (Real.exp t - 1) ^ 2 + (Real.exp t) ^ 2 < 2 := by
  have hpos : 0 < Real.exp t := Real.exp_pos _
  have hinv : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h9 : (9 : ℝ) / 10 ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  have h2 : Real.exp t ≤ 10 / 9 := by nlinarith
  have h3 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht0
  nlinarith

/-- **A completely explicit small-coupling mass gap for the literal `SU(2)`
lattice theory**: if `64|β|(n+1)^4 ≤ 1/10` then the finite-spacing Hamiltonian of
the literal four-dimensional `SU(2)` Wilson theory has a positive vacuum-sector
mass gap at lattice spacing `a`. -/
theorem ym_massGap_of_coupling_le {n : ℕ} (hn : 1 ≤ n) {beta a : ℝ} (ha : 0 < a)
    (hbeta : 64 * |beta| * ((n : ℝ) + 1) ^ 4 ≤ 1 / 10) :
    Clay.MassGapConclusion (ymHamiltonian n beta a ha.le) (ymVacuum n beta)
      (a⁻¹ * (2 - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4)) - 1) ^ 2
        - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4))) ^ 2)) := by
  refine ym_massGap_of_small_coupling hn ha (exp_smallness ?_ ?_)
  · positivity
  · linarith

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms gibbs_eq_withDensity
#print axioms norm_inner_embed_le
#print axioms energyForm_coercive_of_small_action
#print axioms abs_wilsonAction_SU2_le
#print axioms ym_hasLatticeCoercivity_of_small_action
#print axioms ym_massGap_of_small_action
#print axioms ym_massGap_of_small_coupling
#print axioms ym_massGap_of_coupling_le

end Audit
