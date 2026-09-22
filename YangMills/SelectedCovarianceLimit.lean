import Mathlib.Topology.Algebra.Order
import Mathlib.Topology.Instances.Real

open Filter

namespace RequestProject.YangMills

/--
Scalar covariance assembled from the three expectation coordinates needed by
the direct source-to-OS Yang--Mills route.

Keeping this definition independent of measure theory is deliberate: once the
three finite expectations have been identified, covariance convergence is pure
topological algebra.
-/
def scalarCovariance (left right product : ℝ) : ℝ :=
  product - left * right

/--
P2 compiler: convergence of the left expectation, translated-right
expectation, and product expectation implies convergence of the connected
covariance.  No fourth convergence theorem is required.
-/
theorem tendsto_scalarCovariance_of_three_expectations
    {left right product : ℕ → ℝ}
    {left∞ right∞ product∞ : ℝ}
    (hLeft : Tendsto left atTop (𝓝 left∞))
    (hRight : Tendsto right atTop (𝓝 right∞))
    (hProduct : Tendsto product atTop (𝓝 product∞)) :
    Tendsto
      (fun n => scalarCovariance (left n) (right n) (product n))
      atTop
      (𝓝 (scalarCovariance left∞ right∞ product∞)) := by
  exact hProduct.sub (hLeft.mul hRight)

/--
A cutoff-uniform closed upper bound survives a scalar limit.

This is the generic limit step used after finite exponential clustering: for a
fixed Euclidean time, instantiate `bound` by the finite cutoff-independent
quantity `C * exp (-m * t)`.
-/
theorem le_of_tendsto_of_forall_le
    {u : ℕ → ℝ} {u∞ bound : ℝ}
    (hu : Tendsto u atTop (𝓝 u∞))
    (hbound : ∀ n, u n ≤ bound) :
    u∞ ≤ bound := by
  exact le_of_tendsto hu (Filter.Eventually.of_forall hbound)

/--
Absolute-value version of `le_of_tendsto_of_forall_le`.
-/
theorem abs_le_of_tendsto_of_forall_abs_le
    {u : ℕ → ℝ} {u∞ bound : ℝ}
    (hu : Tendsto u atTop (𝓝 u∞))
    (hbound : ∀ n, |u n| ≤ bound) :
    |u∞| ≤ bound := by
  have habs :
      Tendsto (fun n => |u n|) atTop (𝓝 |u∞|) :=
    (continuous_abs.tendsto u∞).comp hu
  exact le_of_tendsto habs (Filter.Eventually.of_forall hbound)

/--
Direct P2 -> continuum-clustering compiler.

If the three expectation coordinates converge and every finite cutoff covariance
obeys the same bound, then the continuum covariance assembled from their limits
obeys that identical bound.
-/
theorem continuum_covariance_bound_of_three_expectations
    {left right product : ℕ → ℝ}
    {left∞ right∞ product∞ bound : ℝ}
    (hLeft : Tendsto left atTop (𝓝 left∞))
    (hRight : Tendsto right atTop (𝓝 right∞))
    (hProduct : Tendsto product atTop (𝓝 product∞))
    (hFinite :
      ∀ n,
        |scalarCovariance (left n) (right n) (product n)| ≤ bound) :
    |scalarCovariance left∞ right∞ product∞| ≤ bound := by
  apply abs_le_of_tendsto_of_forall_abs_le
    (tendsto_scalarCovariance_of_three_expectations
      hLeft hRight hProduct)
  exact hFinite

end RequestProject.YangMills
