import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionCut
import YangMills.LiteralSU2WilsonOSFactorization

/-!
# Same-object OS factorization of the reflected-pair Wilson density

The boundary-Haar projected kernel is defined by integrating the literal full
Wilson density on `su2AssembleReflectedPair`.  This file specializes the
already-proved full-lattice OS factorization to exactly that integrand.

It removes one remaining representation seam in Block A: the object under the
boundary Haar integral is now theorem-bearing as the positive half, reflected
positive half, and the SAME literal crossing-plane kernel.  The subsequent
upper/lower half-path gauge-identification and Haar projection positivity are
still the live producer obligation.
-/

namespace RequestProject.YangMills

/-- Exact OS factorization of the density appearing under boundary projection. -/
theorem literal_su2_reflected_pair_os_factorization
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
          (su2AssembleReflectedPair n left boundary right)) := by
  unfold literalSU2ReflectedPairWilsonDensity
  exact su2_literal_full_wilson_os_factorization
    n (su2AssembleReflectedPair n left boundary right) β

end RequestProject.YangMills
