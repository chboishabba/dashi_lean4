import Mathlib
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.FiniteFeaturePowerIntegralRP
import YangMills.FiniteCrossPlaneExponentialRP

/-!
# Integral positivity for exponentials of finite positive-feature kernels

This is the continuous-measure analogue of `FiniteCrossPlaneExponentialRP`,
under the concrete hypotheses used by the literal Wilson crossing plane:
finite measurable features bounded by one, nonnegative feature weights,
beta >= 0, and an L1 test function.

Taylor truncations are positive because every Hadamard power has already been
expanded into a finite positive-feature family.  The limit is taken on the
single product measure mu x mu, dominated by

  exp(beta * sum_i w_i) * |f(x)| * |f(y)|.

Thus no theorem asserting that an arbitrary finite-sample PSD kernel is
integrally PSD is used.
-/

namespace RequestProject.YangMills

/-- Total nonnegative feature weight controlling the kernel uniformly. -/
def finiteFeatureWeightBudget
    {I : Type*} (terms : Finset I) (weight : I → ℝ) : ℝ :=
  ∑ i ∈ terms, weight i

lemma finite_feature_weight_budget_nonnegative
    {I : Type*} (terms : Finset I) (weight : I → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i) :
    0 ≤ finiteFeatureWeightBudget terms weight := by
  unfold finiteFeatureWeightBudget
  exact Finset.sum_nonneg fun i hi => hweight i hi

/-- Unit-bounded features give a uniform absolute bound on the base kernel. -/
theorem finite_cross_plane_features_abs_le_budget
    {X I : Type*}
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    (x y : X) :
    |finiteCrossPlaneFeatures terms weight feature x y| ≤
      finiteFeatureWeightBudget terms weight := by
  classical
  unfold finiteCrossPlaneFeatures finiteFeatureWeightBudget
  calc
    |∑ i ∈ terms, weight i * feature i x * feature i y|
      ≤ ∑ i ∈ terms, |weight i * feature i x * feature i y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ terms, weight i := by
      gcongr with i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hweight i hi)]
      have hx := hFeatureBound i hi x
      have hy := hFeatureBound i hi y
      nlinarith [abs_nonneg (feature i x), abs_nonneg (feature i y)]

/-- Power features remain measurable. -/
theorem finite_feature_power_feature_measurable
    {X I : Type*} [MeasurableSpace X]
    {terms : Finset I} (feature : I → X → ℝ)
    (hFeatureMeas : ∀ i ∈ terms, Measurable (feature i))
    {n : ℕ} (choice : Fin n → ActiveFiniteFeature terms) :
    Measurable (finiteFeaturePowerFeature feature choice) := by
  unfold finiteFeaturePowerFeature
  fun_prop

/-- Products of unit-bounded source features remain unit bounded. -/
theorem finite_feature_power_feature_abs_le_one
    {X I : Type*}
    {terms : Finset I} (feature : I → X → ℝ)
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    {n : ℕ} (choice : Fin n → ActiveFiniteFeature terms)
    (x : X) :
    |finiteFeaturePowerFeature feature choice x| ≤ 1 := by
  unfold finiteFeaturePowerFeature
  rw [abs_prod]
  exact Finset.prod_le_one₀
    (fun k hk => abs_nonneg _)
    (fun k hk => hFeatureBound (choice k).1 (choice k).2 x)

/-- L1 tests remain integrable after multiplication by every power feature. -/
theorem integrable_mul_finite_feature_power_feature
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    {terms : Finset I} (feature : I → X → ℝ)
    (hFeatureMeas : ∀ i ∈ terms, Measurable (feature i))
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    {n : ℕ} (choice : Fin n → ActiveFiniteFeature terms)
    (f : X → ℝ) (hfInt : MeasureTheory.Integrable f μ) :
    MeasureTheory.Integrable
      (fun x => f x * finiteFeaturePowerFeature feature choice x) μ := by
  have hm := finite_feature_power_feature_measurable feature hFeatureMeas choice
  have hb : ∀ᵐ x ∂μ,
      ‖finiteFeaturePowerFeature feature choice x‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using
        finite_feature_power_feature_abs_le_one feature hFeatureBound choice x
  have h := hfInt.bdd_mul hm.aestronglyMeasurable hb
  simpa [mul_comm] using h

/-- Each Hadamard-power OS pair integrand is integrable on the product measure. -/
theorem finite_cross_plane_feature_pow_pair_integrable
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → X → ℝ)
    (n : ℕ) (f : X → ℝ)
    (hInt : ∀ choice : Fin n → ActiveFiniteFeature terms,
      MeasureTheory.Integrable
        (fun x => f x * finiteFeaturePowerFeature feature choice x) μ) :
    MeasureTheory.Integrable
      (fun z : X × X =>
        f z.1 * (finiteCrossPlaneFeatures terms weight feature z.1 z.2) ^ n * f z.2)
      (μ.prod μ) := by
  classical
  rw [show
    (fun z : X × X =>
      f z.1 * (finiteCrossPlaneFeatures terms weight feature z.1 z.2) ^ n * f z.2) =
    (fun z : X × X =>
      ∑ choice : Fin n → ActiveFiniteFeature terms,
        finiteFeaturePowerWeight weight choice *
          ((f z.1 * finiteFeaturePowerFeature feature choice z.1) *
           (f z.2 * finiteFeaturePowerFeature feature choice z.2))) by
      funext z
      rw [finite_cross_plane_feature_pow_eq_power_features
        terms weight feature n z.1 z.2]
      unfold finiteCrossPlaneFeatures
      simp only [Finset.mem_univ, true_and]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro choice hchoice
      ring]
  apply MeasureTheory.integrable_finsetSum
  intro choice hchoice
  exact ((hInt choice).mul_prod (hInt choice)).const_mul _

/-- Every power has a nonnegative product-space quadratic integral. -/
theorem finite_cross_plane_feature_pow_product_integral_rp
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (n : ℕ) (f : X → ℝ)
    (hInt : ∀ choice : Fin n → ActiveFiniteFeature terms,
      MeasureTheory.Integrable
        (fun x => f x * finiteFeaturePowerFeature feature choice x) μ) :
    0 ≤ ∫ z : X × X,
      f z.1 * (finiteCrossPlaneFeatures terms weight feature z.1 z.2) ^ n * f z.2
      ∂(μ.prod μ) := by
  have hpair := finite_cross_plane_feature_pow_pair_integrable
    μ terms weight feature n f hInt
  rw [MeasureTheory.integral_prod _ hpair]
  exact finite_cross_plane_feature_pow_integral_rp
    μ terms weight feature hweight n f hInt

/-- The finite Taylor quadratic integral is nonnegative term by term. -/
theorem finite_feature_exponential_taylor_product_integral_rp
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hFeatureMeas : ∀ i ∈ terms, Measurable (feature i))
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (N : ℕ) (f : X → ℝ)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ z : X × X,
      f z.1 *
        finiteFeatureExponentialTaylorKernel terms weight feature β N z.1 z.2 *
        f z.2 ∂(μ.prod μ) := by
  classical
  unfold finiteFeatureExponentialTaylorKernel
  rw [show
    (fun z : X × X =>
      f z.1 *
        (∑ n ∈ Finset.range N,
          β ^ n / (n.factorial : ℝ) *
            (finiteCrossPlaneFeatures terms weight feature z.1 z.2) ^ n) *
        f z.2) =
      (fun z : X × X =>
        ∑ n ∈ Finset.range N,
          (β ^ n / (n.factorial : ℝ)) *
            (f z.1 *
              (finiteCrossPlaneFeatures terms weight feature z.1 z.2) ^ n *
              f z.2)) by
      funext z
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_nonneg fun n hn =>
      mul_nonneg
        (div_nonneg (pow_nonneg hβ n) (by positivity))
        (finite_cross_plane_feature_pow_product_integral_rp
          μ terms weight feature hweight n f
          (fun choice =>
            integrable_mul_finite_feature_power_feature
              μ feature hFeatureMeas hFeatureBound choice f hfInt))
  · intro n hn
    exact (finite_cross_plane_feature_pow_pair_integrable
      μ terms weight feature n f
      (fun choice =>
        integrable_mul_finite_feature_power_feature
          μ feature hFeatureMeas hFeatureBound choice f hfInt)).const_mul _

/-- Uniform absolute bound on every exponential Taylor truncation. -/
theorem finite_feature_exponential_taylor_abs_le_exp_budget
    {X I : Type*}
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (N : ℕ) (x y : X) :
    |finiteFeatureExponentialTaylorKernel terms weight feature β N x y| ≤
      Real.exp (β * finiteFeatureWeightBudget terms weight) := by
  classical
  let B := finiteFeatureWeightBudget terms weight
  have hB : 0 ≤ B := finite_feature_weight_budget_nonnegative terms weight hweight
  have hK := finite_cross_plane_features_abs_le_budget
    terms weight feature hweight hFeatureBound x y
  unfold finiteFeatureExponentialTaylorKernel
  calc
    |∑ n ∈ Finset.range N,
        β ^ n / (n.factorial : ℝ) *
          (finiteCrossPlaneFeatures terms weight feature x y) ^ n|
      ≤ ∑ n ∈ Finset.range N,
          |β ^ n / (n.factorial : ℝ) *
            (finiteCrossPlaneFeatures terms weight feature x y) ^ n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N,
          (β * B) ^ n / (n.factorial : ℝ) := by
        gcongr with n hn
        rw [abs_mul, abs_div, abs_pow, abs_pow,
          abs_of_nonneg hβ, abs_of_nonneg (Nat.cast_nonneg _)]
        have hp := pow_le_pow_left₀ (abs_nonneg _)
          hK n
        rw [mul_pow]
        gcongr
    _ ≤ Real.exp (β * B) :=
      Real.sum_le_exp_of_nonneg (mul_nonneg hβ hB) N

/--
Main continuous-measure exponential RP theorem.  This is the measure-level
bridge needed by the literal Wilson crossing kernel.
-/
theorem finite_cross_plane_feature_exponential_integral_rp
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hFeatureMeas : ∀ i ∈ terms, Measurable (feature i))
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ x, ∫ y,
      f x * Real.exp
        (β * finiteCrossPlaneFeatures terms weight feature x y) * f y ∂μ ∂μ := by
  classical
  let B := finiteFeatureWeightBudget terms weight
  let F : ℕ → X × X → ℝ := fun N z =>
    f z.1 *
      finiteFeatureExponentialTaylorKernel terms weight feature β N z.1 z.2 *
      f z.2
  let G : X × X → ℝ := fun z =>
    f z.1 * Real.exp
      (β * finiteCrossPlaneFeatures terms weight feature z.1 z.2) * f z.2
  let D : X × X → ℝ := fun z =>
    Real.exp (β * B) * |f z.1| * |f z.2|
  have hDint : MeasureTheory.Integrable D (μ.prod μ) := by
    have hp := hfInt.norm.mul_prod hfInt.norm
    simpa [D, mul_assoc] using hp.const_mul (Real.exp (β * B))
  have hFmeas : ∀ N, MeasureTheory.AEStronglyMeasurable (F N) (μ.prod μ) := by
    intro N
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hbound : ∀ N, ∀ᵐ z ∂(μ.prod μ), ‖F N z‖ ≤ D z := by
    intro N
    exact Filter.Eventually.of_forall fun z => by
      dsimp [F, D]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have ht := finite_feature_exponential_taylor_abs_le_exp_budget
        terms weight feature hweight hFeatureBound β hβ N z.1 z.2
      nlinarith [abs_nonneg (f z.1), abs_nonneg (f z.2), Real.exp_pos (β * B).le]
  have hlim : ∀ᵐ z ∂(μ.prod μ),
      Filter.Tendsto (fun N => F N z) Filter.atTop (nhds (G z)) :=
    Filter.Eventually.of_forall fun z => by
      dsimp [F, G]
      exact ((finite_feature_exponential_taylor_tendsto
        terms weight feature β z.1 z.2).const_mul (f z.1)).mul_const (f z.2)
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    D hFmeas hDint hbound hlim
  have hnonneg : ∀ N, 0 ≤ ∫ z, F N z ∂(μ.prod μ) := by
    intro N
    exact finite_feature_exponential_taylor_product_integral_rp
      μ terms weight feature hweight hFeatureMeas hFeatureBound
      β hβ N f hfInt
  have hGnonneg : 0 ≤ ∫ z, G z ∂(μ.prod μ) :=
    ge_of_tendsto hconv (Filter.Eventually.of_forall hnonneg)
  have hGmeas : Measurable G := by
    dsimp [G]
    fun_prop
  have hGint : MeasureTheory.Integrable G (μ.prod μ) := by
    apply MeasureTheory.Integrable.mono hDint hGmeas.aestronglyMeasurable
    filter_upwards with z
    dsimp [G, D]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_exp]
    have hB := finite_cross_plane_features_abs_le_budget
      terms weight feature hweight hFeatureBound z.1 z.2
    have hexp :
        Real.exp (β * finiteCrossPlaneFeatures terms weight feature z.1 z.2) ≤
          Real.exp (β * B) := by
      apply Real.exp_le_exp.mpr
      have hle : finiteCrossPlaneFeatures terms weight feature z.1 z.2 ≤ B :=
        (le_abs_self _).trans hB
      exact mul_le_mul_of_nonneg_left hle hβ
    nlinarith [abs_nonneg (f z.1), abs_nonneg (f z.2), Real.exp_pos _ .le]
  rw [← MeasureTheory.integral_prod G hGint]
  exact hGnonneg

end RequestProject.YangMills
