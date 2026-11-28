import Mathlib
import YangMills.FiniteReflectionKernelAudit

/-!
# Exact finite reflection positivity for genuine cross-plane interactions

A complete effective-action correction need not split into two half-space
actions.  Reflection positivity can also survive a nontrivial interaction
across the reflection plane, provided its Gibbs kernel admits a POSITIVE
finite feature expansion.  This construction is algebraic and applies
to the full selected E/R/boundary/vacuum interaction, if the actual
CMP119 source supplies the expansion.

Theorems:
* The Gram form is additive in its kernel and nonnegative under
  nonnegative scaling.
* Every real feature rank-one kernel is reflection-positive.
* Every nonnegative finite sum of rank-one cross-plane kernels is
  reflection-positive.
* Hadamard multiplication of an already reflection-positive Wilson
  kernel by this feature expansion preserves its positive Gram.
* Reflected-half reweighting can be combined with genuine cross-plane
  feature interactions without losing reflection positivity.

An arbitrary small residual action does NOT supply a positive feature
expansion: see FiniteReflectionKernelAudit for the counterexample.
-/

namespace RequestProject.YangMills

theorem finite_reflection_gram_add_kernel
    {X : Type*} (sites : Finset X) (K H : X → X → ℝ)
    (test : X → ℝ) :
    finiteReflectionGram sites (fun x y => K x y + H x y) test =
      finiteReflectionGram sites K test +
        finiteReflectionGram sites H test := by
  simp only [finiteReflectionGram]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem finite_reflection_gram_scale_kernel
    {X : Type*} (sites : Finset X) (K : X → X → ℝ)
    (scalar : ℝ) (test : X → ℝ) :
    finiteReflectionGram sites (fun x y => scalar * K x y) test =
      scalar * finiteReflectionGram sites K test := by
  simp only [finiteReflectionGram]
  simp_rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem finite_reflection_gram_zero_kernel
    {X : Type*} (sites : Finset X) (test : X → ℝ) :
    finiteReflectionGram sites (fun _ _ => (0 : ℝ)) test = 0 := by
  simp [finiteReflectionGram]

/--
A rank-one reflected kernel is the actual square of a finite
positive-time linear functional.
-/
theorem finite_reflection_gram_rank_one
    {X : Type*} (sites : Finset X)
    (feature test : X → ℝ) :
    finiteReflectionGram sites
        (fun x y => feature x * feature y) test =
      (∑ x ∈ sites, test x * feature x) ^ 2 := by
  unfold finiteReflectionGram
  calc
    (∑ x ∈ sites, ∑ y ∈ sites,
        test x * (feature x * feature y) * test y) =
      (∑ x ∈ sites, test x * feature x) *
        (∑ y ∈ sites, test y * feature y) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = _ := by ring

/--
A weighted rank-one perturbation preserves reflection positivity
for nonnegative weight, with an exact quantitative Gram-square formula.
-/
theorem finite_reflection_gram_weighted_rank_one
    {X : Type*} (sites : Finset X)
    (feature test : X → ℝ) (weight : ℝ) :
    finiteReflectionGram sites
        (fun x y => weight * feature x * feature y) test =
      weight * (∑ x ∈ sites, test x * feature x) ^ 2 := by
  calc
    _ = weight *
      finiteReflectionGram sites
        (fun x y => feature x * feature y) test := by
          simpa only [mul_assoc] using
            (finite_reflection_gram_scale_kernel sites
              (fun x y => feature x * feature y) weight test)
    _ = _ := by rw [finite_reflection_gram_rank_one]

/-- Genuine cross-plane feature interaction, not an additive half-action. -/
def finiteCrossPlaneFeatures
    {X I : Type*} (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ) :
    X → X → ℝ :=
  fun x y => ∑ i ∈ terms, weight i * feature i x * feature i y

/-- All finite positive-feature interactions preserve real OS2. -/
theorem finite_cross_plane_features_rp
    {X I : Type*} (sites : Finset X) (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (finiteCrossPlaneFeatures terms weight feature) test := by
  classical
  intro test
  induction terms using Finset.induction_on with
  | empty =>
      simp [finiteCrossPlaneFeatures, finite_reflection_gram_zero_kernel]
  | @insert i terms hi ih =>
      have hweightTail : ∀ j ∈ terms, 0 ≤ weight j :=
        fun j hj => hweight j (Finset.mem_insert_of_mem hj)
      have hhead : 0 ≤ weight i :=
        hweight i (Finset.mem_insert_self i terms)
      have hsplit :
          finiteCrossPlaneFeatures (insert i terms) weight feature =
            fun x y =>
              (weight i * feature i x * feature i y) +
              finiteCrossPlaneFeatures terms weight feature x y := by
        funext x y
        simp [finiteCrossPlaneFeatures, Finset.sum_insert hi]
      rw [hsplit, finite_reflection_gram_add_kernel]
      exact add_nonneg
        (by
          rw [finite_reflection_gram_weighted_rank_one]
          exact mul_nonneg hhead (sq_nonneg _))
        (ih hweightTail)

/--
Hadamard product of a reflection-positive Wilson kernel with a
nonnegative finite cross-plane feature expansion is again
reflection-positive.  This is the finite feature version of the
Schur-product mechanism and preserves actual cross-plane couplings.
-/
theorem finite_wilson_rp_mul_cross_plane_features
    {X I : Type*} (sites : Finset X)
    (wilsonKernel : X → X → ℝ)
    (hWilsonRP : ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites wilsonKernel test)
    (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y =>
          wilsonKernel x y *
            finiteCrossPlaneFeatures terms weight feature x y)
        test := by
  classical
  intro test
  induction terms using Finset.induction_on with
  | empty =>
      simp [finiteCrossPlaneFeatures, finite_reflection_gram_zero_kernel]
  | @insert i terms hi ih =>
      have htail : ∀ j ∈ terms, 0 ≤ weight j :=
        fun j hj => hweight j (Finset.mem_insert_of_mem hj)
      have hhead : 0 ≤ weight i :=
        hweight i (Finset.mem_insert_self i terms)
      have hsplit :
          (fun x y =>
            wilsonKernel x y *
              finiteCrossPlaneFeatures (insert i terms) weight feature x y) =
          (fun x y =>
              weight i * (feature i x * wilsonKernel x y * feature i y) +
              wilsonKernel x y *
                finiteCrossPlaneFeatures terms weight feature x y) := by
        funext x y
        simp only [finiteCrossPlaneFeatures, Finset.sum_insert hi]
        ring
      rw [hsplit, finite_reflection_gram_add_kernel,
        finite_reflection_gram_scale_kernel]
      have hrank :
          0 ≤ finiteReflectionGram sites
            (fun x y => feature i x * wilsonKernel x y * feature i y)
            test :=
        (finite_reflection_positive_of_half_factorization sites
          wilsonKernel (feature i) hWilsonRP) test
      exact add_nonneg (mul_nonneg hhead hrank) (ih htail)

/--
The complete selected non-Wilson Gibbs factor may combine reflected
half-actions AND actual cross-plane interactions whose kernel admits
a positive feature expansion. A factorization identity with the
published CMP119 effective density remains separately required.
-/
theorem finite_full_residual_rp_of_feature_factorization
    {X I : Type*} (sites : Finset X)
    (wilsonKernel : X → X → ℝ)
    (hWilsonRP : ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites wilsonKernel test)
    (halfAction : X → ℝ)
    (terms : Finset I)
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y =>
          Real.exp (-halfAction x) *
            (wilsonKernel x y *
              finiteCrossPlaneFeatures terms weight feature x y) *
            Real.exp (-halfAction y)) test := by
  intro test
  exact finite_reflection_positive_of_half_factorization
    sites
    (fun x y =>
      wilsonKernel x y *
        finiteCrossPlaneFeatures terms weight feature x y)
    (fun x => Real.exp (-halfAction x))
    (finite_wilson_rp_mul_cross_plane_features
      sites wilsonKernel hWilsonRP terms weight feature hweight)
    test

end RequestProject.YangMills
