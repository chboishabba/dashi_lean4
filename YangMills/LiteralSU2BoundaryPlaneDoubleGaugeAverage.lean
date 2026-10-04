import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.ProductPairSecondSwap
import YangMills.LiteralSU2BoundaryPlaneFeatureRP
import YangMills.LiteralSU2CrossingDoubleGaugeAverage
import YangMills.LiteralSU2BoundaryProjectedHalfWeightFactorization

/-!
# Plane double-gauge average = literal crossing average

The augmented Gram presentation gauges each upper and lower plane independently
on the two positive copies.  The literal lower crossing orientation is the
opposite one.  Swapping only the two lower Haar copies converts the augmented
plane kernel pointwise into the already-owned full-boundary double-gauge
kernel.  The swap preserves the product Haar law, and the plane-assembly map
pushes product plane Haar to the literal full temporal-boundary Haar.

This is the source-specific same-object/Fubini weld needed by the terminal
finite pure-Wilson OS2 theorem.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Augmented crossing kernel on two independently gauged boundary-plane copies. -/
def su2BoundaryPlaneDoubleGaugedCrossingKernel
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryPlaneFields n) : ℝ :=
  Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
    Real.exp (β *
      (su2UpperPlaneDoubleGaugedCrossingTraceSum n left right b.1 c.1 +
       su2LowerPlaneDoubleGaugedCrossingTraceSum n left right b.2 c.2))

/-- Pair-product Haar average of the augmented plane kernel. -/
noncomputable def literalSU2BoundaryPlaneAveragedDoubleGaugedCrossingKernel
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) : ℝ :=
  ∫ bc : SU2BoundaryPlaneFields n × SU2BoundaryPlaneFields n,
    su2BoundaryPlaneDoubleGaugedCrossingKernel n β left right bc.1 bc.2
    ∂((literalSU2BoundaryPlaneHaar n).prod (literalSU2BoundaryPlaneHaar n))

/-- Relative full-boundary gauge formation commutes with plane assembly. -/
theorem su2_relative_boundary_field_plane_assemble
    (n : ℕ) [NeZero n]
    (b c : SU2BoundaryPlaneFields n) :
    su2RelativeBoundaryField
        (su2BoundaryTemporalPlaneAssemble n b)
        (su2BoundaryTemporalPlaneAssemble n c) =
      su2BoundaryTemporalPlaneAssemble n
        (su2BoundaryRelativeGauge b.1 c.1,
         su2BoundaryRelativeGauge b.2 c.2) := by
  funext p
  unfold su2RelativeBoundaryField su2BoundaryRelativeGauge
    su2BoundaryTemporalPlaneAssemble
  split <;> rfl

/--
After swapping only the two lower boundary copies, the plane trace is exactly
the literal full-boundary double-gauged trace.
-/
theorem su2_boundary_plane_second_swap_trace_eq_full
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryPlaneFields n) :
    su2UpperPlaneDoubleGaugedCrossingTraceSum n left right b.1 c.1 +
      su2LowerPlaneDoubleGaugedCrossingTraceSum n left right c.2 b.2 =
    su2DoubleGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n b)
      (su2BoundaryTemporalPlaneAssemble n c) := by
  rw [su2_upper_plane_double_gauge_reduce,
    su2_lower_plane_double_gauge_reduce]
  rw [su2_double_gauged_crossing_trace_sum_relative,
    su2_relative_boundary_field_plane_assemble]
  rw [su2_upper_gauged_crossing_sum_plane_readback,
    su2_lower_gauged_crossing_sum_plane_readback]
  rfl

/-- Pointwise kernel version of the lower-copy swap identity. -/
theorem su2_boundary_plane_second_swap_kernel_eq_full
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (bc : SU2BoundaryPlaneFields n × SU2BoundaryPlaneFields n) :
    su2BoundaryPlaneDoubleGaugedCrossingKernel n β left right
        (productPairSecondSwap bc).1 (productPairSecondSwap bc).2 =
      su2DoubleGaugedCrossingKernel n β left right
        (su2BoundaryTemporalPlaneAssemble n bc.1)
        (su2BoundaryTemporalPlaneAssemble n bc.2) := by
  rcases bc with ⟨b, c⟩
  rcases b with ⟨bu, bl⟩
  rcases c with ⟨cu, cl⟩
  unfold su2BoundaryPlaneDoubleGaugedCrossingKernel
    su2DoubleGaugedCrossingKernel
  rw [su2_boundary_plane_second_swap_trace_eq_full]

/-- The double-gauged crossing trace is uniformly bounded on the finite crossing set. -/
theorem su2_double_gauged_crossing_trace_sum_abs_le
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    |su2DoubleGaugedCrossingTraceSum n left right b c| ≤
      ((su2UpperCrossingPlaquettes n).card +
       (su2LowerCrossingPlaquettes n).card : ℕ) := by
  classical
  unfold su2DoubleGaugedCrossingTraceSum
  rw [abs_add]
  · gcongr
    · unfold su2UpperDoubleGaugedCrossingTraceSum
      calc
        |∑ p ∈ (su2UpperCrossingPlaquettes n).attach,
            su2RelativeFundamentalTrace
              (su2BoundaryGaugeTransformEdge
                (b (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
                (b (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
                (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))
              (su2BoundaryGaugeTransformEdge
                (c (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
                (c (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
                (right (su2UpperCrossingRightPositiveIndex n p.1 p.2)))| ≤
            ∑ p ∈ (su2UpperCrossingPlaquettes n).attach, (1 : ℝ) := by
              apply Finset.abs_sum_le_sum_abs.trans
              gcongr with p hp
              simpa [su2RelativeFundamentalTrace, su2QuaternionCoordinate] using
                (su2_quaternion_coordinate_abs_le_one (0 : Fin 4)
                  ((su2BoundaryGaugeTransformEdge
                    (b (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
                    (b (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
                    (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2))) *
                   (su2BoundaryGaugeTransformEdge
                    (c (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
                    (c (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
                    (right (su2UpperCrossingRightPositiveIndex n p.1 p.2)))⁻¹))
        _ = ((su2UpperCrossingPlaquettes n).card : ℝ) := by simp
    · unfold su2LowerDoubleGaugedCrossingTraceSum
      calc
        |∑ p ∈ (su2LowerCrossingPlaquettes n).attach,
            su2RelativeFundamentalTrace
              (su2BoundaryGaugeTransformEdge
                (b (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
                (b (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
                (right (su2LowerCrossingRightPositiveIndex n p.1 p.2)))
              (su2BoundaryGaugeTransformEdge
                (c (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
                (c (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
                (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2)))| ≤
            ∑ p ∈ (su2LowerCrossingPlaquettes n).attach, (1 : ℝ) := by
              apply Finset.abs_sum_le_sum_abs.trans
              gcongr with p hp
              simpa [su2RelativeFundamentalTrace, su2QuaternionCoordinate] using
                (su2_quaternion_coordinate_abs_le_one (0 : Fin 4)
                  ((su2BoundaryGaugeTransformEdge
                    (b (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
                    (b (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
                    (right (su2LowerCrossingRightPositiveIndex n p.1 p.2))) *
                   (su2BoundaryGaugeTransformEdge
                    (c (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
                    (c (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
                    (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2)))⁻¹))
        _ = ((su2LowerCrossingPlaquettes n).card : ℝ) := by simp
  · exact abs_nonneg _
  · exact abs_nonneg _

/-- The literal full-boundary double-gauged kernel is integrable on the boundary pair. -/
theorem su2_double_gauged_crossing_kernel_boundary_pair_integrable
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    Integrable
      (fun bc : SU2BoundaryTemporalLinks n × SU2BoundaryTemporalLinks n =>
        su2DoubleGaugedCrossingKernel n β left right bc.1 bc.2)
      ((literalSU2BoundaryTemporalHaar n).prod
        (literalSU2BoundaryTemporalHaar n)) := by
  let M : ℝ :=
    ((su2UpperCrossingPlaquettes n).card +
     (su2LowerCrossingPlaquettes n).card : ℕ)
  let C : ℝ :=
    Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
      Real.exp (|β| * M)
  refine Integrable.of_bound (by fun_prop) C (Filter.Eventually.of_forall fun bc => ?_)
  unfold su2DoubleGaugedCrossingKernel
  rw [Real.norm_eq_abs, abs_mul, abs_exp, abs_exp]
  gcongr
  apply Real.exp_le_exp.mpr
  calc
    β * su2DoubleGaugedCrossingTraceSum n left right bc.1 bc.2 ≤
        |β| * |su2DoubleGaugedCrossingTraceSum n left right bc.1 bc.2| := by
      exact mul_le_mul_of_nonneg_right (le_abs_self β) (abs_nonneg _)
    _ ≤ |β| * M := by
      gcongr
      simpa [M] using
        su2_double_gauged_crossing_trace_sum_abs_le n left right bc.1 bc.2

/-- Plane assembly is measure preserving from plane Haar to full temporal-boundary Haar. -/
theorem su2_boundary_temporal_plane_assemble_measurePreserving
    (n : ℕ) [NeZero n] :
    MeasurePreserving (su2BoundaryTemporalPlaneAssemble n)
      (literalSU2BoundaryPlaneHaar n)
      (literalSU2BoundaryTemporalHaar n) :=
  ⟨su2_boundary_temporal_plane_assemble_measurable n,
    literal_su2_boundary_temporal_haar_plane_split n⟩

/--
The pair-product augmented plane average is exactly the literal one-boundary
crossing average.
-/
theorem literal_su2_boundary_plane_double_gauge_average_eq_literal
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryPlaneAveragedDoubleGaugedCrossingKernel n β left right =
      literalSU2BoundaryAveragedCrossingKernel n β left right := by
  let μP := literalSU2BoundaryPlaneHaar n
  let μB := literalSU2BoundaryTemporalHaar n
  let Kfull : SU2BoundaryTemporalLinks n × SU2BoundaryTemporalLinks n → ℝ :=
    fun bc => su2DoubleGaugedCrossingKernel n β left right bc.1 bc.2
  let Kplane : SU2BoundaryPlaneFields n × SU2BoundaryPlaneFields n → ℝ :=
    fun bc => su2BoundaryPlaneDoubleGaugedCrossingKernel n β left right bc.1 bc.2
  have hPair := MeasurePreserving.prod
    (su2_boundary_temporal_plane_assemble_measurePreserving n)
    (su2_boundary_temporal_plane_assemble_measurePreserving n)
  have hmap :
      (∫ bc, Kfull
          (Prod.map (su2BoundaryTemporalPlaneAssemble n)
            (su2BoundaryTemporalPlaneAssemble n) bc)
        ∂(μP.prod μP)) =
        ∫ bc, Kfull bc ∂(μB.prod μB) := by
    exact hPair.integral_comp'
      (f := Prod.map (su2BoundaryTemporalPlaneAssemble n)
        (su2BoundaryTemporalPlaneAssemble n)) Kfull
  have hswap :
      (∫ bc, Kplane (productPairSecondSwap bc) ∂(μP.prod μP)) =
        ∫ bc, Kplane bc ∂(μP.prod μP) := by
    exact integral_product_pair_second_swap
      (literalSU2UpperBoundaryTemporalHaar n)
      (literalSU2LowerBoundaryTemporalHaar n) Kplane
  have hpoint :
      (fun bc => Kplane (productPairSecondSwap bc)) =
      (fun bc => Kfull
        (Prod.map (su2BoundaryTemporalPlaneAssemble n)
          (su2BoundaryTemporalPlaneAssemble n) bc)) := by
    funext bc
    exact su2_boundary_plane_second_swap_kernel_eq_full n β left right bc
  have hPairToNested :
      (∫ bc, Kfull bc ∂(μB.prod μB)) =
      ∫ b, ∫ c,
        su2DoubleGaugedCrossingKernel n β left right b c ∂μB ∂μB := by
    exact integral_prod Kfull
      (su2_double_gauged_crossing_kernel_boundary_pair_integrable
        n β left right)
  unfold literalSU2BoundaryPlaneAveragedDoubleGaugedCrossingKernel
  change (∫ bc, Kplane bc ∂(μP.prod μP)) = _
  calc
    (∫ bc, Kplane bc ∂(μP.prod μP)) =
        ∫ bc, Kplane (productPairSecondSwap bc) ∂(μP.prod μP) := hswap.symm
    _ = ∫ bc, Kfull
        (Prod.map (su2BoundaryTemporalPlaneAssemble n)
          (su2BoundaryTemporalPlaneAssemble n) bc)
        ∂(μP.prod μP) := by rw [hpoint]
    _ = ∫ bc, Kfull bc ∂(μB.prod μB) := hmap
    _ = ∫ b, ∫ c,
        su2DoubleGaugedCrossingKernel n β left right b c ∂μB ∂μB := hPairToNested
    _ = literalSU2BoundaryAveragedCrossingKernel n β left right := by
      unfold literalSU2BoundaryAveragedCrossingKernel
      exact su2_double_gauged_crossing_average_eq_literal n β left right

end RequestProject.YangMills
