import Mathlib
import YangMills.LiteralSU2ReflectedPairOSFactorization

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    literalSU2ReflectedPairWilsonDensity n β left boundary right =
      su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary right) β *
      su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks
          (su2AssembleReflectedPair n left boundary right)) β *
      su2WilsonCrossingPlaneKernel
        (su2EvenTimeCrossingPlaquettes n) β
        (su2LiteralCrossingFirstBoundary
          (su2AssembleReflectedPair n left boundary right))
        (su2LiteralCrossingSecondBoundary
          (su2AssembleReflectedPair n left boundary right)) :=
  literal_su2_reflected_pair_os_factorization
    n β left boundary right

end RequestProject.YangMills
