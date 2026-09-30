import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exponential
import YangMills.FiniteCrossPlaneFeatureRP

/-!
# Exponential closure of finite positive cross-plane feature kernels

A finite positive feature kernel
  K(x,y) = Σ_i w_i φ_i(x) φ_i(y),   w_i ≥ 0
is positive semidefinite.  More strongly, for β ≥ 0 the ENTRYWISE
exponential
  exp(β K(x,y))
is positive semidefinite.

This is the Schur-power-series theorem proved directly at the finite
reflection-Gram level:
* every Hadamard power K^n is RP;
* every exponential Taylor section is a nonnegative sum of RP kernels;
* finite Gram sums commute with the Taylor limit.

The theorem applies simultaneously to many physical crossing plaquettes:
index the features by (crossing plaquette, representation coordinate).
It therefore supplies the algebraic part of a Wilson reflection-plane
proof once the literal lattice reflection identifies the crossing action
with such a kernel.  It does NOT assert that the selected CMP119
regular/R/boundary/vacuum residual has this feature representation.
-/

namespace RequestProject.YangMills

/-- Every Hadamard power of a finite positive feature kernel is RP. -/
theorem finite_cross_plane_feature_pow_rp
    {X I : Type*}
    (sites : Finset X) (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (n : ℕ) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y =>
          (finiteCrossPlaneFeatures terms weight feature x y) ^ n)
        test := by
  induction n with
  | zero =>
      intro test
      have hkernel :
          (fun _ _ : X => (1 : ℝ)) =
            (fun x y =>
              (finiteCrossPlaneFeatures terms weight feature x y) ^ 0) := by
        funext x y
        simp
      rw [← hkernel]
      have hrank :=
        finite_reflection_gram_rank_one
          sites (fun _ : X => (1 : ℝ)) test
      rw [show
        (fun _ _ : X => (1 : ℝ)) =
          (fun x y => (1 : ℝ) * (1 : ℝ)) by
            funext x y; ring,
        finite_reflection_gram_rank_one]
      exact sq_nonneg _
  | succ n ih =>
      intro test
      have h :=
        finite_wilson_rp_mul_cross_plane_features
          sites
          (fun x y =>
            (finiteCrossPlaneFeatures terms weight feature x y) ^ n)
          (ih)
          terms weight feature hweight test
      simpa [pow_succ, mul_assoc] using h

/-- Taylor section of exp(β K) for a finite positive feature kernel. -/
def finiteFeatureExponentialTaylorKernel
    {X I : Type*}
    (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (β : ℝ) (N : ℕ) : X → X → ℝ :=
  fun x y =>
    ∑ n ∈ Finset.range N,
      (β ^ n / (n.factorial : ℝ)) *
        (finiteCrossPlaneFeatures terms weight feature x y) ^ n

theorem finite_feature_exponential_taylor_rp
    {X I : Type*}
    (sites : Finset X) (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (β : ℝ) (hβ : 0 ≤ β)
    (N : ℕ) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (finiteFeatureExponentialTaylorKernel
          terms weight feature β N) test := by
  induction N with
  | zero =>
      intro test
      simp [finiteFeatureExponentialTaylorKernel,
        finite_reflection_gram_zero_kernel]
  | succ N ih =>
      intro test
      have hcoeff :
          0 ≤ β ^ N / (N.factorial : ℝ) :=
        div_nonneg (pow_nonneg hβ N) (by positivity)
      have hsplit :
          finiteFeatureExponentialTaylorKernel
            terms weight feature β (N + 1) =
          fun x y =>
            finiteFeatureExponentialTaylorKernel
              terms weight feature β N x y +
            (β ^ N / (N.factorial : ℝ)) *
              (finiteCrossPlaneFeatures
                terms weight feature x y) ^ N := by
        funext x y
        simp [finiteFeatureExponentialTaylorKernel,
          Finset.sum_range_succ]
      rw [hsplit, finite_reflection_gram_add_kernel,
        finite_reflection_gram_scale_kernel]
      exact add_nonneg
        (ih test)
        (mul_nonneg hcoeff
          (finite_cross_plane_feature_pow_rp
            sites terms weight feature hweight N test))

theorem finite_feature_exponential_taylor_tendsto
    {X I : Type*}
    (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (β : ℝ) (x y : X) :
    Filter.Tendsto
      (fun N =>
        finiteFeatureExponentialTaylorKernel
          terms weight feature β N x y)
      Filter.atTop
      (nhds
        (Real.exp
          (β * finiteCrossPlaneFeatures
            terms weight feature x y))) := by
  have h :=
    (NormedSpace.expSeries_div_hasSum_exp
      (β * finiteCrossPlaneFeatures
        terms weight feature x y : ℝ)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ]
  convert h using 1
  ext N
  simp only [finiteFeatureExponentialTaylorKernel]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

theorem finite_feature_exponential_gram_tendsto
    {X I : Type*}
    (sites : Finset X) (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (β : ℝ) (test : X → ℝ) :
    Filter.Tendsto
      (fun N =>
        finiteReflectionGram sites
          (finiteFeatureExponentialTaylorKernel
            terms weight feature β N) test)
      Filter.atTop
      (nhds
        (finiteReflectionGram sites
          (fun x y =>
            Real.exp
              (β * finiteCrossPlaneFeatures
                terms weight feature x y))
          test)) := by
  unfold finiteReflectionGram
  apply tendsto_finsetSum sites
  intro x hx
  apply tendsto_finsetSum sites
  intro y hy
  exact (((finite_feature_exponential_taylor_tendsto
    terms weight feature β x y).const_mul
      (test x)).mul_const (test y))

/--
MAIN GENERIC RESULT:
entrywise exp(βK) is finite reflection-positive whenever K is a
nonnegative finite feature Gram kernel and β≥0.
-/
theorem finite_cross_plane_feature_exponential_rp
    {X I : Type*}
    (sites : Finset X) (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y =>
          Real.exp
            (β * finiteCrossPlaneFeatures
              terms weight feature x y))
        test := by
  intro test
  apply ge_of_tendsto
    (finite_feature_exponential_gram_tendsto
      sites terms weight feature β test)
  exact Filter.Eventually.of_forall
    (fun N =>
      finite_feature_exponential_taylor_rp
        sites terms weight feature hweight β hβ N test)

/--
Multi-crossing version: an entire finite collection of crossing
plaquettes/coordinates can be put into one feature index.
-/
def multiCrossingFeatureKernel
    {X P I : Type*}
    (plaquettes : Finset P) (coordinates : Finset I)
    (weight : P → I → ℝ)
    (feature : P → I → X → ℝ) : X → X → ℝ :=
  fun x y =>
    ∑ p ∈ plaquettes,
      ∑ i ∈ coordinates,
        weight p i * feature p i x * feature p i y

theorem multi_crossing_feature_exponential_rp
    {X P I : Type*}
    (sites : Finset X)
    (plaquettes : Finset P) (coordinates : Finset I)
    (weight : P → I → ℝ)
    (feature : P → I → X → ℝ)
    (hweight :
      ∀ p ∈ plaquettes, ∀ i ∈ coordinates, 0 ≤ weight p i)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y =>
          Real.exp
            (β * multiCrossingFeatureKernel
              plaquettes coordinates weight feature x y))
        test := by
  classical
  intro test
  let terms : Finset (P × I) :=
    plaquettes.product coordinates
  let pairWeight : P × I → ℝ :=
    fun pi => weight pi.1 pi.2
  let pairFeature : P × I → X → ℝ :=
    fun pi => feature pi.1 pi.2
  have hpw :
      ∀ pi ∈ terms, 0 ≤ pairWeight pi := by
    intro pi hpi
    rcases Finset.mem_product.mp hpi with ⟨hp, hi⟩
    exact hweight pi.1 hp pi.2 hi
  have hkernel :
      finiteCrossPlaneFeatures terms pairWeight pairFeature =
        multiCrossingFeatureKernel
          plaquettes coordinates weight feature := by
    funext x y
    simp [terms, pairWeight, pairFeature,
      finiteCrossPlaneFeatures, multiCrossingFeatureKernel,
      Finset.sum_product]
  rw [← hkernel]
  exact finite_cross_plane_feature_exponential_rp
    sites terms pairWeight pairFeature hpw β hβ test

end RequestProject.YangMills
