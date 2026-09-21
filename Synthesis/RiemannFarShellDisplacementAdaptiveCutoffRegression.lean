import Synthesis.RiemannFarShellDisplacementAdaptiveCutoff

namespace Synthesis

example {A t alpha : ℝ}
    (hA : 0 ≤ A) (ht : 1 ≤ t) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    18 * A * Real.log (t + 4) / ((t / alpha) ^ 4) +
      72 * A / Real.sqrt ((t / alpha) ^ 4)
      ≤ 144 * A * alpha ^ 2 / (t ^ 2) :=
  farShell_scaledQuartic_le_displacementInverseSquare hA ht ha0 ha1

end Synthesis
