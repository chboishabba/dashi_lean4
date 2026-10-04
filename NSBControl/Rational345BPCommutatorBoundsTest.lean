import NSBControl.Rational345BPCommutatorBounds

namespace NSBControl
namespace Rational345BPCommutatorBoundsTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPBudget
open Rational345BPCommutatorBounds

example {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputCommutator u (projectedNonlinearity u) k‖
      ≤ commutatorValueBound := by
  exact fixedOutputCommutator_norm_le hu k

end Rational345BPCommutatorBoundsTest
end NSBControl
