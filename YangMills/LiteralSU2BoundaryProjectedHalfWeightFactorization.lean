import Mathlib
import YangMills.LiteralSU2ReflectedPairOSFactorization
import YangMills.LiteralSU2ReflectedPositiveHalfReadback

/-!
# Exact half-weight factorization of the boundary-projected Wilson kernel

After the reflected positive-half right-readback, both noncrossing Wilson
factors are independent of the temporal boundary variable.  They can therefore
be pulled outside the boundary-Haar integral, leaving only the literal crossing
kernel average between a left half weight and a right half weight.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- The one-boundary Haar average of the exact literal crossing-plane kernel. -/
noncomputable def literalSU2BoundaryAveragedCrossingKernel
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) : ℝ :=
  ∫ boundary : SU2BoundaryTemporalLinks n,
    su2WilsonCrossingPlaneKernel
      (su2EvenTimeCrossingPlaquettes n) β
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right))
    ∂(literalSU2BoundaryTemporalHaar n)

/-- Pointwise reflected-pair density with both noncrossing half weights exposed. -/
theorem literal_su2_reflected_pair_density_half_weight_factorization
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    literalSU2ReflectedPairWilsonDensity n β left boundary right =
      su2PositiveInteriorWilsonHalfWeight n β left *
      su2PositiveInteriorWilsonHalfWeight n β right *
      su2WilsonCrossingPlaneKernel
        (su2EvenTimeCrossingPlaquettes n) β
        (su2LiteralCrossingFirstBoundary
          (su2AssembleReflectedPair n left boundary right))
        (su2LiteralCrossingSecondBoundary
          (su2AssembleReflectedPair n left boundary right)) := by
  rw [literal_su2_reflected_pair_os_factorization n β left right boundary]
  rw [su2_positive_half_assembled_pair_eq_left_weight n β left right boundary]
  rw [su2_reflected_positive_half_assembled_pair_eq_right_weight
    n β left right boundary]

/--
Exact projected-kernel congruence:

  K_proj(L,R) = h(L) * K_avg(L,R) * h(R).

This is the final noncrossing assembly identity needed before applying RP to the
averaged crossing kernel.
-/
theorem literal_su2_boundary_gauge_projected_kernel_half_weight_factorization
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      su2PositiveInteriorWilsonHalfWeight n β left *
      literalSU2BoundaryAveragedCrossingKernel n β left right *
      su2PositiveInteriorWilsonHalfWeight n β right := by
  unfold literalSU2BoundaryGaugeProjectedWilsonKernel
  calc
    (∫ boundary : SU2BoundaryTemporalLinks n,
      literalSU2ReflectedPairWilsonDensity n β left boundary right
      ∂(literalSU2BoundaryTemporalHaar n)) =
        ∫ boundary : SU2BoundaryTemporalLinks n,
          (su2PositiveInteriorWilsonHalfWeight n β left *
            su2PositiveInteriorWilsonHalfWeight n β right) *
          su2WilsonCrossingPlaneKernel
            (su2EvenTimeCrossingPlaquettes n) β
            (su2LiteralCrossingFirstBoundary
              (su2AssembleReflectedPair n left boundary right))
            (su2LiteralCrossingSecondBoundary
              (su2AssembleReflectedPair n left boundary right))
          ∂(literalSU2BoundaryTemporalHaar n) := by
            apply integral_congr_ae
            filter_upwards [] with boundary
            rw [literal_su2_reflected_pair_density_half_weight_factorization
              n β left right boundary]
    _ = (su2PositiveInteriorWilsonHalfWeight n β left *
          su2PositiveInteriorWilsonHalfWeight n β right) *
        literalSU2BoundaryAveragedCrossingKernel n β left right := by
          rw [MeasureTheory.integral_const_mul]
          rfl
    _ = su2PositiveInteriorWilsonHalfWeight n β left *
        literalSU2BoundaryAveragedCrossingKernel n β left right *
        su2PositiveInteriorWilsonHalfWeight n β right := by
          ring

end RequestProject.YangMills
