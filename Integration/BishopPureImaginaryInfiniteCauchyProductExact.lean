import Integration.BishopPureImaginaryFiniteCauchyCoefficientsExact
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# K05-PRODUCT: infinite mixed signed-factorial Cauchy product on ℂ

This consumes the EXISTING all-degree factorial coefficient theorem and
constructs the infinite multiplication with genuine absolute summability,
including the rectangle -> antidiagonal/triangle exchange. No
fictitious independent "summable" source record is passed in.

This is the true mathematical series (I*x)^n/n!, the same parity-split
complex coefficient underlying original Bishop cosine/sine terms.

**Kernel/authority:** Lean/Mathlib theorem source; NOT an Agda proof
of the vendored Bishop Cauchy-limit setoid transport. The original
Bishop convergence/source identity and Agda kernel receipt remain
separate and must not be silently promoted.
-/

namespace Integration.BishopPureImaginaryInfiniteCauchyProductExact

open scoped BigOperators Topology
open Integration.BishopPureImaginaryFiniteCauchyCoefficientsExact

noncomputable section

/-- Absolute convergence of the literal complex pure imaginary
factorial coefficients, proved by the complete normed division-ring
exponential series theorem, not an added axiom or local assumption. -/
theorem imaginaryCoefficient_absSummable (x : ℝ) :
    Summable (fun n : ℕ => ‖imaginaryCoefficient x n‖) := by
  simpa only [imaginaryCoefficient] using
    (NormedSpace.norm_expSeries_div_summable (Complex.I * (x : ℂ)))

/-- Summability of actual coefficients follows from absolute
summability, with no extra infinite-series premise. -/
theorem imaginaryCoefficient_summable (x : ℝ) :
    Summable (imaginaryCoefficient x) :=
  (imaginaryCoefficient_absSummable x).of_norm

/-- The original mixed factorial Cauchy coefficients are not merely
finite: the full antidiagonal series is absolutely summable. -/
theorem imaginaryCauchyCoefficient_absSummable (x y : ℝ) :
    Summable (fun n : ℕ => ‖imaginaryCauchyCoefficient x y n‖) := by
  simpa only [imaginaryCauchyCoefficient] using
    (summable_norm_sum_mul_range_of_summable_norm
      (imaginaryCoefficient_absSummable x)
      (imaginaryCoefficient_absSummable y))

/-- Fully justified rectangle -> triangle Cauchy interchange at
the same source coefficients, for ALL real x and y. -/
theorem imaginaryInfiniteCauchyProduct (x y : ℝ) :
    (∑' n : ℕ, imaginaryCoefficient x n) *
        (∑' n : ℕ, imaginaryCoefficient y n) =
      ∑' n : ℕ, imaginaryCauchyCoefficient x y n := by
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (imaginaryCoefficient_absSummable x)
    (imaginaryCoefficient_absSummable y)

/-- ALL-n finite factorial coefficient theorem and genuine infinite
Cauchy interchange now compose into the ORIGINAL complex series
addition identity, not a second unrelated exponential model. -/
theorem imaginaryInfiniteSeriesAdd (x y : ℝ) :
    (∑' n : ℕ, imaginaryCoefficient x n) *
        (∑' n : ℕ, imaginaryCoefficient y n) =
      ∑' n : ℕ, imaginaryCoefficient (x + y) n := by
  rw [imaginaryInfiniteCauchyProduct]
  apply tsum_congr
  intro n
  exact imaginaryCauchyCoefficient_eq_add x y n

end

end Integration.BishopPureImaginaryInfiniteCauchyProductExact
