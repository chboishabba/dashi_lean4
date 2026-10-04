import NSBControl.Rational345BQFieldBound
import NSBControl.Rational345ShortTime

namespace NSBControl
namespace Rational345BQFieldBoundTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQGeometry
open Rational345BQFieldBound
open Rational345ShortTime

example {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius) :
    ‖galerkinField x‖ ≤ odeComponentBound := by
  exact galerkinField_norm_le_certified hx

end Rational345BQFieldBoundTest
end NSBControl
