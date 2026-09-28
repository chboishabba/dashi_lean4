import Mathlib
import NSBControl.AugmentedDerivativeCancellation

namespace NSBControl
namespace DyadicDifferenceResidual

/--
Abstract R748 algebra: once the exact paired three-leg powers satisfy energy
cancellation, a weighted cyclic sum has only two multiplier-difference
coordinates.
-/
theorem weighted_three_leg_eq_two_differences
    (wk wp wq pk pp pq : ℝ)
    (hEnergy : pk + pp + pq = 0) :
    wk * pk + wp * pp + wq * pq
      =
    (wk - wq) * pk + (wp - wq) * pp := by
  linarith

/-- R750 scalar core: equal selected weights kill the production correction. -/
theorem two_difference_zero_of_equal_weights
    (wk wp wq pk pp : ℝ)
    (hkq : wk = wq)
    (hpq : wp = wq) :
    (wk - wq) * pk + (wp - wq) * pp = 0 := by
  rw [hkq, hpq]
  ring

/--
Abstract global R748/R749 replacement: if the paired two-difference production
fold is exactly twice the oriented production orbit, then the new local
difference-aligned nonlinear fold is exactly the old orbit-aligned nonlinear
fold.
-/
theorem difference_aligned_replaces_oriented
    (nested pairedDiff oriented : ℝ)
    (hPair : pairedDiff = 2 * oriented) :
    3 * nested - pairedDiff = 3 * nested - 2 * oriented := by
  rw [hPair]

/--
Abstract R745-R747 residual identity. This deliberately records only the fixed
positive-factor relation; the physical carrier identities live in Agda.
-/
theorem residual_eq_three_gap
    (nonlinear coeff diss combined packet : ℝ)
    (hNonlinear : nonlinear = 3 * combined - 3 * (packet + coeff * diss)) :
    nonlinear + 3 * coeff * diss = 3 * (combined - packet) := by
  linarith

theorem residual_nonnegative_iff_gap
    (residual combined packet : ℝ)
    (hResidual : residual = 3 * (combined - packet)) :
    (0 ≤ residual) ↔ (packet ≤ combined) := by
  rw [hResidual]
  constructor
  · intro h
    linarith
  · intro h
    positivity

end DyadicDifferenceResidual
end NSBControl
