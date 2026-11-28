import YangMills.LiteralSU2ReflectedPositiveHalfReadback

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks
          (su2AssembleReflectedPair n left boundary right)) β =
      su2PositiveInteriorWilsonHalfWeight n β right :=
  su2_reflected_positive_half_assembled_pair_eq_right_weight
    n β left right boundary

end RequestProject.YangMills
