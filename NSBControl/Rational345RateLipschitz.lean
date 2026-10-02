import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# R830 selected-rate finite-ball Lipschitz compiler

O3 should not be proved by comparing the selected observable coordinate by
coordinate along a trajectory.  For any finite-dimensional real carrier, a
uniform operator-norm bound on the derivative of the selected rate over a
closed ball gives the required one-sided Lipschitz estimate by the mean-value
theorem.

The Navier--Stokes-specific residue is therefore only the finite polynomial
derivative bound for the literal R815 observable.
-/

open Set

namespace NSBControl
namespace Rational345RateLipschitz

/-- Symmetric finite-ball Lipschitz estimate from an explicit derivative
operator-norm bound. -/
theorem abs_rate_sub_le_of_fderiv_bound
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate : E → ℝ)
    (u₀ : E) (radius L : ℝ)
    (hradius : 0 ≤ radius)
    (hdiff :
      ∀ x ∈ Metric.closedBall u₀ radius,
        DifferentiableAt ℝ rate x)
    (hbound :
      ∀ x ∈ Metric.closedBall u₀ radius,
        ‖fderiv ℝ rate x‖ ≤ L)
    {x : E}
    (hx : x ∈ Metric.closedBall u₀ radius) :
    |rate x - rate u₀| ≤ L * ‖x - u₀‖ := by
  have h :=
    (convex_closedBall u₀ radius).norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound
      (Metric.mem_closedBall_self hradius)
      hx
  simpa [Real.norm_eq_abs] using h

/-- One-sided form consumed by the R828/R830 terminal theorem. -/
theorem rate_sub_le_of_fderiv_bound
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate : E → ℝ)
    (u₀ : E) (radius L : ℝ)
    (hradius : 0 ≤ radius)
    (hdiff :
      ∀ x ∈ Metric.closedBall u₀ radius,
        DifferentiableAt ℝ rate x)
    (hbound :
      ∀ x ∈ Metric.closedBall u₀ radius,
        ‖fderiv ℝ rate x‖ ≤ L)
    {x : E}
    (hx : x ∈ Metric.closedBall u₀ radius) :
    rate x - rate u₀ ≤ L * ‖x - u₀‖ := by
  exact
    (le_abs_self (rate x - rate u₀)).trans
      (abs_rate_sub_le_of_fderiv_bound
        rate u₀ radius L hradius hdiff hbound hx)

/-- The concrete R828 constant can be installed once the literal selected
rate polynomial has derivative norm bounded by this number on the bootstrap
ball. -/
def certifiedRateLipschitzBound : ℝ :=
  391309593930357307785216

theorem certifiedRateLipschitzBound_nonneg :
    0 ≤ certifiedRateLipschitzBound := by
  norm_num [certifiedRateLipschitzBound]

end Rational345RateLipschitz
end NSBControl
