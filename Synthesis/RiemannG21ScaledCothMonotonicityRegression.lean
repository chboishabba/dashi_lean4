import Synthesis.RiemannG21ScaledCothMonotonicity

open Set

namespace Synthesis

example {x : ℝ} (hx : 0 < x) :
    x < Real.sinh x * Real.cosh x := by
  exact sinh_mul_cosh_gt_self hx

example : StrictMonoOn scaledCothCarrier (Ioi 0) := by
  exact scaledCothCarrier_strictMonoOn

end Synthesis
