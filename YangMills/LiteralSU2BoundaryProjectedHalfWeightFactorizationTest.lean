import YangMills.LiteralSU2BoundaryProjectedHalfWeightFactorization

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      su2PositiveInteriorWilsonHalfWeight n β left *
      literalSU2BoundaryAveragedCrossingKernel n β left right *
      su2PositiveInteriorWilsonHalfWeight n β right :=
  literal_su2_boundary_gauge_projected_kernel_half_weight_factorization
    n β left right

end RequestProject.YangMills
