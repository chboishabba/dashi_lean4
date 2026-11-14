import Synthesis.RiemannG21CosineFourthRemainder

namespace Synthesis

example (x : ℝ) :
    |Real.cos x - (1 - x^2/2)| <= |x|^4 / 24 := by
  exact cos_quadratic_fourth_remainder x

end Synthesis
