import Synthesis.RiemannG21SineFifthRemainder

/-! RED-first regression contract for the exact fifth-order sine remainder. -/

namespace Synthesis

example (x : ℝ) :
    |Real.sin x - (x - x^3/6)| <= |x|^5 / 120 := by
  exact sin_cubic_fifth_remainder x

example (x : ℝ) :
    |6 * (Real.sin x - (x - x^3/6))| <= |x|^5 / 20 := by
  exact six_scaled_sin_cubic_remainder x

end Synthesis
