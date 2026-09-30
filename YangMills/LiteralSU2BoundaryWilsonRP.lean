import Mathlib
import YangMills.LiteralSU2FourDimensionalLattice
import YangMills.FiniteCrossPlaneFeatureRP

/-!
# A physically evaluated SU(2) crossing-plaquette reflection kernel

The time-reflection crossing geometry exposes one plaquette as the
fundamental SU(2) relative holonomy U V⁻¹.  The real normalized trace
is exactly the Euclidean dot product of the two *unit quaternion*
halves.  This is an ACTUAL holonomy calculation, not a coefficient
in the symbolic T4 plaquette basis.

The full Wilson Boltzmann factor e^(-β(1-dot)) needs an infinite
positive-feature/character expansion to prove reflection positivity;
the local first-order crossing kernel 1+β dot is treated here exactly.
The theorem is a useful physical base case and the first term in the
character expansion, not yet an OS2 theorem for the full Wilson action.

Source lineage: Osterwalder--Seiler, "Gauge field theories on a lattice"
(1978), DOI 10.1016/0003-4916(78)90039-8; the specific finite
quaternion calculation and its first-order Gram proof are DASHI
derivations, not claims copied from that article.
-/

namespace RequestProject.YangMills

def su2QuaternionCoordinate (i : Fin 4)
    (U : SU2PlaquetteHolonomy) : ℝ :=
  if i = 0 then U.a
  else if i = 1 then U.b
  else if i = 2 then U.c
  else U.d

/-- Actual real first-character kernel, computed from SU(2) holonomies. -/
def su2RelativeFundamentalTrace
    (U V : SU2PlaquetteHolonomy) : ℝ :=
  (U * V⁻¹).a

/-- Fundamental-trace cyclicity reduces to four-dimensional dot product. -/
theorem su2_relative_trace_eq_quaternion_dot
    (U V : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace U V =
      ∑ i : Fin 4, su2QuaternionCoordinate i U *
        su2QuaternionCoordinate i V := by
  unfold su2RelativeFundamentalTrace su2QuaternionCoordinate
  simp [Fin.sum_univ_four, Mul.mul, Inv.inv,
    su2Mul, su2Inv]
  ring

/--
The REAL normalized SU(2) crossing trace is a positive Gram kernel:
it is a sum of four actual physical quaternion-coordinate squares.
-/
theorem su2_fundamental_crossing_trace_real_rp
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      su2RelativeFundamentalTrace test := by
  have hFeatures :
      0 ≤ finiteReflectionGram sites
        (finiteCrossPlaneFeatures (Finset.univ : Finset (Fin 4))
          (fun _ => (1 : ℝ)) su2QuaternionCoordinate) test :=
    finite_cross_plane_features_rp
      sites Finset.univ (fun _ => 1) su2QuaternionCoordinate
      (by intro i hi; norm_num) test
  convert hFeatures using 1
  congr 1
  funext U V
  rw [su2_relative_trace_eq_quaternion_dot]
  simp [finiteCrossPlaneFeatures]

/--
The constant crossing kernel is a rank-one nonnegative square.
-/
theorem su2_constant_crossing_kernel_rp
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun _ _ => (1 : ℝ)) test := by
  have h := finite_reflection_gram_rank_one sites
    (fun _ => (1 : ℝ)) test
  simpa using (show
    0 ≤ (∑ x ∈ sites, test x * (1 : ℝ)) ^ 2 from sq_nonneg _)

/--
First-order physical crossing-plaquette Wilson kernel.
This is not the full exponential Gibbs factor.
-/
def su2FirstOrderCrossingWilsonKernel
    (β : ℝ) (U V : SU2PlaquetteHolonomy) : ℝ :=
  1 + β * su2RelativeFundamentalTrace U V

theorem su2_first_order_crossing_wilson_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset SU2PlaquetteHolonomy)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (su2FirstOrderCrossingWilsonKernel β) test := by
  have hsplit :
      su2FirstOrderCrossingWilsonKernel β =
        fun U V => (1 : ℝ) +
          β * su2RelativeFundamentalTrace U V := rfl
  rw [hsplit, finite_reflection_gram_add_kernel,
    finite_reflection_gram_scale_kernel]
  exact add_nonneg
    (su2_constant_crossing_kernel_rp sites test)
    (mul_nonneg hβ
      (su2_fundamental_crossing_trace_real_rp sites test))

/--
The same explicitly computed first-character kernel remains RP
under arbitrary reflection-compatible half-space reweighting.
-/
theorem su2_first_order_crossing_with_half_action_rp
    (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset SU2PlaquetteHolonomy)
    (halfAction : SU2PlaquetteHolonomy → ℝ)
    (test : SU2PlaquetteHolonomy → ℝ) :
    0 ≤ finiteReflectionGram sites
      (fun U V =>
        Real.exp (-halfAction U) *
          su2FirstOrderCrossingWilsonKernel β U V *
          Real.exp (-halfAction V)) test := by
  exact finite_reflection_positive_of_half_factorization
    sites (su2FirstOrderCrossingWilsonKernel β)
    (fun U => Real.exp (-halfAction U))
    (fun f => su2_first_order_crossing_wilson_rp β hβ sites f)
    test

end RequestProject.YangMills
