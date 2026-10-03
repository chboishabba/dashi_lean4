import Mathlib
import YangMills.LiteralSU2FullBoundaryHaarDoubleAverage
import YangMills.LiteralSU2CrossingGaugeSumReadback

/-!
# Double-gauged augmented crossing average = literal crossing average

This is the crossing-only same-object/Fubini weld.  The augmented RP picture has
an independently gauged copy on each positive half.  The local SU(2) algebra
reduces those gauges to `u = b * c⁻¹`; full boundary Haar then collapses the two
independent copies to one Haar field; finally the existing literal crossing
readback identifies the resulting exponential with the exact crossing factor of
the reflected Wilson configuration.

No positivity assumption is introduced here.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Crossing exponential on two independently gauged positive copies. -/
def su2DoubleGaugedCrossingKernel
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) : ℝ :=
  Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
    Real.exp (β * su2DoubleGaugedCrossingTraceSum n left right b c)

/-- Pointwise, the double-gauged exponential is the literal gauged crossing expression at `b*c⁻¹`. -/
theorem su2_double_gauged_crossing_kernel_relative
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2DoubleGaugedCrossingKernel n β left right b c =
      Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
        Real.exp (β *
          (su2UpperGaugedCrossingTraceSum n left right
              (su2RelativeBoundaryField b c) +
           su2LowerGaugedCrossingTraceSum n left right
              (su2RelativeBoundaryField b c))) := by
  unfold su2DoubleGaugedCrossingKernel
  rw [su2_double_gauged_crossing_trace_sum_relative]

/--
Exact crossing-average weld from two independent augmented boundary copies to
the one-boundary literal Wilson crossing kernel.
-/
theorem su2_double_gauged_crossing_average_eq_literal
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    (∫ b, ∫ c,
      su2DoubleGaugedCrossingKernel n β left right b c
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u,
        su2WilsonCrossingPlaneKernel
          (su2EvenTimeCrossingPlaquettes n) β
          (su2LiteralCrossingFirstBoundary
            (su2AssembleReflectedPair n left u right))
          (su2LiteralCrossingSecondBoundary
            (su2AssembleReflectedPair n left u right))
        ∂(literalSU2BoundaryTemporalHaar n) := by
  let k : SU2BoundaryTemporalLinks n → ℝ := fun u =>
    Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
      Real.exp (β *
        (su2UpperGaugedCrossingTraceSum n left right u +
         su2LowerGaugedCrossingTraceSum n left right u))
  calc
    (∫ b, ∫ c,
      su2DoubleGaugedCrossingKernel n β left right b c
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
        ∫ b, ∫ c, k (su2RelativeBoundaryField b c)
          ∂(literalSU2BoundaryTemporalHaar n)
          ∂(literalSU2BoundaryTemporalHaar n) := by
            apply integral_congr_ae
            filter_upwards [] with b
            apply integral_congr_ae
            filter_upwards [] with c
            exact su2_double_gauged_crossing_kernel_relative
              n β left right b c
    _ = ∫ u, k u ∂(literalSU2BoundaryTemporalHaar n) :=
      literal_su2_full_boundary_haar_double_relative n k
    _ = ∫ u,
        su2WilsonCrossingPlaneKernel
          (su2EvenTimeCrossingPlaquettes n) β
          (su2LiteralCrossingFirstBoundary
            (su2AssembleReflectedPair n left u right))
          (su2LiteralCrossingSecondBoundary
            (su2AssembleReflectedPair n left u right))
        ∂(literalSU2BoundaryTemporalHaar n) := by
          apply integral_congr_ae
          filter_upwards [] with u
          symm
          exact su2_literal_crossing_kernel_gauge_sum_readback
            n β left right u

end RequestProject.YangMills
