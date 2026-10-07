import Mathlib
import YangMills.YMClayMaxCut20261007FinalFrontier

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  ym20261007BCExactCompiler cut

example (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  ym20261007HalfRatePhysicalEnergyFloor a E ha hDecay

end RequestProject.YangMills
