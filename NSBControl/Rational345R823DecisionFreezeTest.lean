import NSBControl.Rational345R823DecisionFreeze

namespace NSBControl
namespace Rational345R823DecisionFreezeTest

open Rational345R823DecisionFreeze

example : ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r823UniversalReserveCounterexample

example : r823DecisionSourceClosed = true := rfl
example : r823DecisionKernelCertified = false := rfl

end Rational345R823DecisionFreezeTest
end NSBControl
