import NSBControl.Rational345R823RealProductionDifference

namespace NSBControl
namespace Rational345R823RealProductionDifferenceTest

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823RealProductionDifference

example (u : State) (hu : IsR823PhysicalState u) :
    pairedTwoDifferenceCompleteFold u = 3 * criticalProduction u := by
  exact pairedTwoDifferenceCompleteFold_eq_threeProduction u hu

end Rational345R823RealProductionDifferenceTest
end NSBControl
