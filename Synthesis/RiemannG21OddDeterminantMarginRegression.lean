import Synthesis.RiemannG21OddDeterminantMargin

/-! RED-first regression contract for odd determinant sign/margin transfer. -/

namespace Synthesis

example {r delta : ℝ} (hr : 0 < r) (hdelta : 0 < delta) :
    -(36 * r^4) * delta < 0 := by
  exact oddCubicDoubleRadius_neg hr hdelta

example {actual cubic : ℝ}
    (hcubic : cubic < 0)
    (herr : |actual - cubic| < |cubic|) :
    actual < 0 := by
  exact negative_of_abs_sub_lt_abs hcubic herr

example {actual cubic : ℝ}
    (hcubic : 0 < cubic)
    (herr : |actual - cubic| < |cubic|) :
    0 < actual := by
  exact positive_of_abs_sub_lt_abs hcubic herr

end Synthesis
