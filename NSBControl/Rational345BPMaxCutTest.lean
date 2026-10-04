import NSBControl.Rational345BPMaxCut

namespace NSBControl
namespace Rational345BPMaxCutTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPBudget
open Rational345BPMaxCut

example {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    |criticalDissipation x - criticalDissipation y| ≤
      criticalDissipationLipschitzBound * ‖x - y‖ := by
  exact criticalDissipation_diff_le hx hy

end Rational345BPMaxCutTest
end NSBControl
