import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exponential
import YangMills.LiteralSU2BoundaryWilsonRP

/-!
# Full exponential SU(2) crossing-Wilson reflection positivity

The actual crossing-plaquette scalar
  q(U,V) = ReTr(U V^{-1})/2
is the Euclidean dot product of the two unit-quaternion halves.

For β ≥ 0, the full Wilson crossing factor is
  exp(-β) * exp(β q(U,V)).
The harmless scalar exp(-β) is positive.  This file proves the
nontrivial part exp(β q) is a positive finite Gram kernel by:

1. q is a four-feature positive Gram kernel.
2. Every Hadamard power q^n remains reflection-positive.
3. Every Taylor partial sum with coefficient β^n/n! is RP.
4. The finite Gram of those partial sums converges to the finite Gram
   of exp(βq); the closed nonnegative cone therefore contains the limit.

This is a real finite reflection-plane theorem for the FULL exponential
crossing plaquette.  It does not yet identify the selected complete
CMP119 E/R/boundary/vacuum effective factor with a positive cross-plane
kernel, nor does it prove continuum OS positivity.
-/

namespace RequestProject.YangMills

/-- q itself, expressed exactly as the four quaternion coordinate features. -/
theorem su2_relative_trace_eq_positive_features :
    su2RelativeFundamentalTrace =
      finiteCrossPlaneFeatures (Finset.univ : Finset (Fin 4))
        (fun _ => (1 : ℝ)) su2QuaternionCoordinate := by
  funext U V
  rw [su2_relative_trace_eq_quaternion_dot]
  simp [finiteCrossPlaneFeatures]

/--
Every Hadamard power of the actual SU(2) crossing trace is RP.
This is the tensor-power Gram argument expressed through repeated
positive-feature multiplication.
-/
theorem su2_relative_trace_pow_rp
    (n : ℕ)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun U V => (su2RelativeFundamentalTrace U V) ^ n) test := by
  induction n with
  | zero =>
      simpa using su2_constant_crossing_kernel_rp sites test
  | succ n ih =>
      have hprod :=
        finite_wilson_rp_mul_cross_plane_features
          sites
          (fun U V => (su2RelativeFundamentalTrace U V) ^ n)
          (fun f => su2_relative_trace_pow_rp n sites f)
          (Finset.univ : Finset (Fin 4))
          (fun _ => (1 : ℝ))
          su2QuaternionCoordinate
          (by intro i hi; norm_num)
          test
      rw [← su2_relative_trace_eq_positive_features] at hprod
      simpa [pow_succ] using hprod

/-- Taylor partial kernel for exp(β q). -/
def su2ExponentialTaylorKernel
    (β : ℝ) (N : ℕ)
    (U V : SU2PlaquetteHolonomy) : ℝ :=
  ∑ n ∈ Finset.range N,
    (β ^ n / (n.factorial : ℝ)) *
      (su2RelativeFundamentalTrace U V) ^ n

/-- Every finite Taylor section is RP for β ≥ 0. -/
theorem su2_exponential_taylor_kernel_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (N : ℕ)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (su2ExponentialTaylorKernel β N) test := by
  induction N with
  | zero =>
      simp [su2ExponentialTaylorKernel,
        finite_reflection_gram_zero_kernel]
  | succ N ih =>
      have hcoeff :
          0 ≤ β ^ N / (N.factorial : ℝ) :=
        div_nonneg (pow_nonneg hβ N) (by positivity)
      have hsplit :
          su2ExponentialTaylorKernel β (N + 1) =
            fun U V =>
              su2ExponentialTaylorKernel β N U V +
              (β ^ N / (N.factorial : ℝ)) *
                (su2RelativeFundamentalTrace U V) ^ N := by
        funext U V
        simp [su2ExponentialTaylorKernel, Finset.sum_range_succ]
      rw [hsplit, finite_reflection_gram_add_kernel,
        finite_reflection_gram_scale_kernel]
      exact add_nonneg ih
        (mul_nonneg hcoeff
          (su2_relative_trace_pow_rp N sites test))

/-- Pointwise convergence of the positive Taylor kernels to exp(βq). -/
theorem su2_exponential_taylor_kernel_tendsto
    (β : ℝ) (U V : SU2PlaquetteHolonomy) :
    Filter.Tendsto
      (fun N => su2ExponentialTaylorKernel β N U V)
      Filter.atTop
      (nhds (Real.exp
        (β * su2RelativeFundamentalTrace U V))) := by
  have h :=
    (NormedSpace.expSeries_div_hasSum_exp
      (β * su2RelativeFundamentalTrace U V : ℝ)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ]
  convert h using 1
  ext N
  simp only [su2ExponentialTaylorKernel]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

/--
Finite Gram convergence follows because both reflected half spaces are
finite sums.  No dominated-convergence theorem is needed at this stage.
-/
theorem su2_exponential_taylor_gram_tendsto
    (β : ℝ)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    Filter.Tendsto
      (fun N =>
        finiteReflectionGram sites
          (su2ExponentialTaylorKernel β N) test)
      Filter.atTop
      (nhds
        (finiteReflectionGram sites
          (fun U V =>
            Real.exp (β * su2RelativeFundamentalTrace U V))
          test)) := by
  unfold finiteReflectionGram
  apply tendsto_finsetSum sites
  intro U hU
  apply tendsto_finsetSum sites
  intro V hV
  exact (((su2_exponential_taylor_kernel_tendsto β U V).const_mul
    (test U)).mul_const (test V))

/--
FULL exponential crossing-Wilson reflection positivity:
  exp(β q(U,V))
is positive semidefinite on every finite family for β ≥ 0.
-/
theorem su2_full_exponential_crossing_kernel_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun U V =>
        Real.exp (β * su2RelativeFundamentalTrace U V)) test := by
  apply ge_of_tendsto
    (su2_exponential_taylor_gram_tendsto β sites test)
  exact Filter.Eventually.of_forall
    (fun N => su2_exponential_taylor_kernel_rp
      β hβ N sites test)

/--
The exact one-plaquette Wilson Boltzmann crossing kernel includes the
positive scalar exp(-β); it is therefore RP as well.
-/
def su2FullCrossingWilsonKernel
    (β : ℝ) (U V : SU2PlaquetteHolonomy) : ℝ :=
  Real.exp (-β) *
    Real.exp (β * su2RelativeFundamentalTrace U V)

theorem su2_full_crossing_wilson_kernel_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (su2FullCrossingWilsonKernel β) test := by
  rw [show
    su2FullCrossingWilsonKernel β =
      fun U V =>
        Real.exp (-β) *
          Real.exp (β * su2RelativeFundamentalTrace U V) by rfl]
  rw [finite_reflection_gram_scale_kernel]
  exact mul_nonneg (Real.exp_pos _).le
    (su2_full_exponential_crossing_kernel_rp
      β hβ sites test)

/--
The full exponential crossing-Wilson factor survives arbitrary
reflection-compatible half-action reweighting.
-/
theorem su2_full_crossing_wilson_with_half_action_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset SU2PlaquetteHolonomy)
    (halfAction : SU2PlaquetteHolonomy → ℝ)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun U V =>
        Real.exp (-halfAction U) *
          su2FullCrossingWilsonKernel β U V *
          Real.exp (-halfAction V)) test := by
  exact finite_reflection_positive_of_half_factorization
    sites (su2FullCrossingWilsonKernel β)
    (fun U => Real.exp (-halfAction U))
    (fun f =>
      su2_full_crossing_wilson_kernel_rp β hβ sites f)
    test

end RequestProject.YangMills
