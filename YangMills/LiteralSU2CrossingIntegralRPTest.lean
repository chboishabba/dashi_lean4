import Mathlib
import YangMills.LiteralSU2CrossingIntegralRP

namespace RequestProject.YangMills

example
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.Measure (SU2CrossingBoundary P))
    [MeasureTheory.SFinite μ]
    (f : SU2CrossingBoundary P → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ left, ∫ right,
      f left * su2WilsonCrossingPlaneKernel crossings β left right * f right ∂μ ∂μ :=
  su2_wilson_crossing_plane_integral_rp
    crossings β hβ μ f hfMeas hfInt

end RequestProject.YangMills
