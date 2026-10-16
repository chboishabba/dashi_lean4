import Mathlib
import Synthesis.RiemannG21OddRatioGapRadiusGate

/-!
# G21 odd determinant sign and direct margin transfer

The Agda G21 audit already derives the double-radius cubic determinant as

  `D_cubic(r,2r) = -(36 r^4) * Delta_odd`.

This owner pays the remaining elementary ordered-real consequences:

* positive radius + positive odd moment margin => the cubic determinant is
  strictly negative in the historical G21 orientation;
* a direct determinant approximation with error strictly smaller than the
  cubic margin preserves that sign (and its positive-orientation analogue).

Thus after the analytic six-term remainder estimate is supplied, sign transfer
itself is no longer a separate frontier leaf.
-/

namespace Synthesis

/-- Historical G21 odd orientation at the preferred radii `r,2r`. -/
theorem oddCubicDoubleRadius_neg
    {r delta : ℝ} (hr : 0 < r) (hdelta : 0 < delta) :
    -(36 * r^4) * delta < 0 := by
  have hr4 : 0 < r^4 := by positivity
  positivity

/-- Direct negative-sign margin transfer.  No entrywise determinant estimate is
required: the determinant-level error alone suffices. -/
theorem negative_of_abs_sub_lt_abs
    {actual cubic : ℝ}
    (hcubic : cubic < 0)
    (herr : |actual - cubic| < |cubic|) :
    actual < 0 := by
  rw [abs_of_neg hcubic] at herr
  have hupper := (abs_lt.mp herr).2
  linarith

/-- Positive-orientation companion. -/
theorem positive_of_abs_sub_lt_abs
    {actual cubic : ℝ}
    (hcubic : 0 < cubic)
    (herr : |actual - cubic| < |cubic|) :
    0 < actual := by
  rw [abs_of_pos hcubic] at herr
  have hlower := (abs_lt.mp herr).1
  linarith

/-- Specialized G21 compiler: once the actual determinant lies within the
strict cubic margin, its historical odd determinant remains negative. -/
theorem g21OddFiniteMinor_neg_of_directMargin
    {r delta actual : ℝ}
    (hr : 0 < r) (hdelta : 0 < delta)
    (herr :
      |actual - (-(36 * r^4) * delta)|
        < |-(36 * r^4) * delta|) :
    actual < 0 := by
  exact negative_of_abs_sub_lt_abs (oddCubicDoubleRadius_neg hr hdelta) herr

end Synthesis
