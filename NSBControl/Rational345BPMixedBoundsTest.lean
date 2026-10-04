import NSBControl.Rational345BPMixedBounds

namespace NSBControl
namespace Rational345BPMixedBoundsTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPBudget
open Rational345BPMixedBounds

example {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputMixed u k‖ ≤ mixedValueBound := by
  exact fixedOutputMixed_norm_le hu k

end Rational345BPMixedBoundsTest
end NSBControl
