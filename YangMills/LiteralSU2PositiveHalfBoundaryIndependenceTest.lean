import YangMills.LiteralSU2PositiveHalfBoundaryIndependence

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left : SU2PositiveInteriorLinks n)
    (boundary₁ boundary₂ : SU2BoundaryTemporalLinks n)
    (right₁ right₂ : SU2PositiveInteriorLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₁ right₁) β =
      su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₂ right₂) β :=
  su2_positive_half_assembled_pair_boundary_independent
    n β left boundary₁ boundary₂ right₁ right₂

end RequestProject.YangMills
