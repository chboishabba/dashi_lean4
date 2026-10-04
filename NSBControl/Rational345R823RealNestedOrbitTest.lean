import NSBControl.Rational345R823RealNestedOrbit

namespace NSBControl
namespace Rational345R823RealNestedOrbitTest

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823RealNestedOrbit

example (u : State) (hu : IsR823PhysicalState u) :
    realNestedOrbitCompleteFold u = 12 * globalCoherentWork u := by
  exact realNestedOrbitCompleteFold_eq_twelveCoherent u hu

end Rational345R823RealNestedOrbitTest
end NSBControl
