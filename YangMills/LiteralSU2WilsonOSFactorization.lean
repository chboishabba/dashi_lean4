import Mathlib
import YangMills.LiteralSU2HalfIndexBijection
import YangMills.LiteralSU2PlaquetteHalfHolonomyFactorization

/-!
# Literal finite Wilson OS factorization on the even 4D SU(2) torus

This is the exact algebraic factorization needed before Haar/Fubini integration.

For the actual link-derived finite Wilson density:
  full(U) = positive(U) * negative(U) * crossing(U).

The global plaquette-index reflection theorem identifies
  negative(U) = positive(Theta U),

and the literal half-holonomy theorem identifies the crossing product with
the already-proved positive crossing kernel.

Hence the SAME literal density has the Osterwalder--Schrader shape

  full(U)
    = H(U) H(Theta U)
      K_cross(A(U),B(U)).

No independent kernel, plaquette carrier, or half action is introduced here.
The remaining integral theorem is measure-theoretic: prove the native
finite link-Haar law decomposes/preserves reflection strongly enough to
integrate this factorization against positive-time cylinder functions.
-/

namespace RequestProject.YangMills

def su2EvenTimePositiveWilsonHalf
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n)) (β : ℝ) : ℝ :=
  su2LiteralWilsonProduct
    (su2EvenTimePositivePlaquettes n) links β

theorem su2_literal_full_wilson_os_factorization
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n)) (β : ℝ) :
    su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n)) links β =
      su2EvenTimePositiveWilsonHalf n links β *
      su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks links) β *
      su2WilsonCrossingPlaneKernel
        (su2EvenTimeCrossingPlaquettes n) β
        (su2LiteralCrossingFirstBoundary links)
        (su2LiteralCrossingSecondBoundary links) := by
  rw [su2_even_time_cut_wilson_product_partition]
  rw [← su2_negative_half_eq_reflected_positive_half]
  rw [su2_even_time_crossing_product_is_positive_kernel]
  rfl

/--
The two noncrossing factors are exchanged exactly by link reflection.
-/
theorem su2_positive_half_reflection_pair
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n)) (β : ℝ) :
    su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2EvenTimeNegativePlaquettes n) links β := by
  exact su2_negative_half_eq_reflected_positive_half n links β

end RequestProject.YangMills
