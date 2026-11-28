import Mathlib
import YangMills.FiniteCrossPlaneExponentialRP
import YangMills.LiteralSU2FullExponentialBoundaryRP

/-!
# Full finite SU(2) Wilson crossing-plane kernel

A finite reflection plane cuts finitely many Wilson plaquettes.
For each crossing plaquette p, its two reflected half-holonomies are
represented by unit quaternions U_p and V_p.  The normalized
fundamental trace of U_p V_p^{-1} is the four-coordinate dot product.

For a crossing set C, the full Wilson crossing factor is

  ∏_{p∈C} exp(-β(1-q_p))
    = exp(-β |C|) exp(β Σ_{p∈C} q_p).

The second factor is the exponential of one finite positive feature
kernel indexed by (p, quaternion-coordinate).  Hence the ENTIRE
finite crossing-plane Wilson kernel is reflection-positive for β≥0.

This closes the algebraic multi-plaquette crossing part of Wilson RP
inside Lean.  Remaining physical geometry:
* identify the actual time-reflection cut of the 4D link lattice with
  these half-holonomy boundary variables;
* split non-crossing Wilson plaquettes into reflected half-actions;
* prove the selected CMP119 E/R/boundary/vacuum factor has a
  reflection-compatible positive kernel/pullback structure.

No continuum claim is made here.
-/

namespace RequestProject.YangMills

abbrev SU2CrossingBoundary (P : Type*) :=
  P → SU2PlaquetteHolonomy

def su2CrossingTraceSum
    {P : Type*} (crossings : Finset P)
    (left right : SU2CrossingBoundary P) : ℝ :=
  ∑ p ∈ crossings,
    su2RelativeFundamentalTrace (left p) (right p)

/-- Feature presentation of the entire finite crossing plane. -/
theorem su2_crossing_trace_sum_eq_features
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) :
    su2CrossingTraceSum crossings =
      multiCrossingFeatureKernel
        crossings (Finset.univ : Finset (Fin 4))
        (fun _ _ => (1 : ℝ))
        (fun p i boundary =>
          su2QuaternionCoordinate i (boundary p)) := by
  funext left right
  unfold su2CrossingTraceSum multiCrossingFeatureKernel
  apply Finset.sum_congr rfl
  intro p hp
  rw [su2_relative_trace_eq_quaternion_dot]
  simp

theorem su2_crossing_trace_sum_symmetric
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (left right : SU2CrossingBoundary P) :
    su2CrossingTraceSum crossings left right =
      su2CrossingTraceSum crossings right left := by
  unfold su2CrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [su2_relative_trace_eq_quaternion_dot,
    su2_relative_trace_eq_quaternion_dot]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
The complete Wilson crossing-plane factor, including the constant
positive plaquette cost e^{-β} for every crossed plaquette.
-/
def su2WilsonCrossingPlaneKernel
    {P : Type*} (crossings : Finset P)
    (β : ℝ)
    (left right : SU2CrossingBoundary P) : ℝ :=
  Real.exp (-(β * (crossings.card : ℝ))) *
    Real.exp (β * su2CrossingTraceSum crossings left right)

theorem su2_wilson_crossing_plane_kernel_symmetric
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) (β : ℝ)
    (left right : SU2CrossingBoundary P) :
    su2WilsonCrossingPlaneKernel crossings β left right =
      su2WilsonCrossingPlaneKernel crossings β right left := by
  unfold su2WilsonCrossingPlaneKernel
  rw [su2_crossing_trace_sum_symmetric crossings left right]

/-- Exact factorization into one-plaquette crossing Wilson kernels. -/
theorem su2_wilson_crossing_plane_kernel_eq_product
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ)
    (left right : SU2CrossingBoundary P) :
    su2WilsonCrossingPlaneKernel crossings β left right =
      ∏ p ∈ crossings,
        su2FullCrossingWilsonKernel β (left p) (right p) := by
  unfold su2WilsonCrossingPlaneKernel
    su2FullCrossingWilsonKernel
    su2CrossingTraceSum
  rw [Finset.prod_mul_distrib]
  have hconst :
      (∏ _p ∈ crossings, Real.exp (-β)) =
        Real.exp (-(β * (crossings.card : ℝ))) := by
    rw [Finset.prod_const]
    simp only [nsmul_eq_mul, Real.exp_nat_mul]
    congr 1
    ring
  rw [hconst]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  ring

/--
MAIN PHYSICAL FINITE WILSON RESULT:
the whole SU(2) crossing-plane Wilson Boltzmann kernel is PSD.
-/
theorem su2_wilson_crossing_plane_rp
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset (SU2CrossingBoundary P))
    (test : SU2CrossingBoundary P → ℝ) :
    0 ≤ finiteReflectionGram sites
      (su2WilsonCrossingPlaneKernel crossings β) test := by
  have hExp :
      0 ≤ finiteReflectionGram sites
        (fun left right =>
          Real.exp
            (β * su2CrossingTraceSum crossings left right))
        test := by
    rw [su2_crossing_trace_sum_eq_features crossings]
    exact multi_crossing_feature_exponential_rp
      sites crossings (Finset.univ : Finset (Fin 4))
      (fun _ _ => (1 : ℝ))
      (fun p i boundary =>
        su2QuaternionCoordinate i (boundary p))
      (by intro p hp i hi; norm_num)
      β hβ test
  rw [show
    su2WilsonCrossingPlaneKernel crossings β =
      fun left right =>
        Real.exp (-(β * (crossings.card : ℝ))) *
          Real.exp (β * su2CrossingTraceSum crossings left right) by
            rfl,
    finite_reflection_gram_scale_kernel]
  exact mul_nonneg (Real.exp_pos _).le hExp

/--
Adding an arbitrary reflection-compatible positive-half action to the
full crossing plane preserves positivity.  This is the Wilson-side
shape needed before asking what CMP119's extra effective sectors do.
-/
theorem su2_wilson_crossing_plane_with_half_action_rp
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset (SU2CrossingBoundary P))
    (halfAction : SU2CrossingBoundary P → ℝ)
    (test : SU2CrossingBoundary P → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun left right =>
        Real.exp (-halfAction left) *
          su2WilsonCrossingPlaneKernel crossings β left right *
          Real.exp (-halfAction right))
      test := by
  exact finite_reflection_positive_of_half_factorization
    sites
    (su2WilsonCrossingPlaneKernel crossings β)
    (fun boundary => Real.exp (-halfAction boundary))
    (fun f =>
      su2_wilson_crossing_plane_rp
        crossings β hβ sites f)
    test

end RequestProject.YangMills
