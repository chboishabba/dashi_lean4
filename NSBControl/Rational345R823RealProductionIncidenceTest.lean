import NSBControl.Rational345R823RealProductionIncidence

namespace NSBControl
namespace Rational345R823RealProductionIncidenceTest

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealProductionIncidence

example (u : State) (p q k : Mode) : ℝ :=
  orderedPower u p q k

example (u : State) (k : Mode) :
    fixedOutputOrderedPower u k =
      (hermitianDot (u k) (projectedNonlinearity u k)).re := by
  exact fixedOutputOrderedPower_eq_pairing u k

example (u : State) :
    criticalProduction u = 2 * weightedProductionIncidenceTotal u := by
  exact criticalProduction_eq_twice_weightedIncidence u

example (u : State) (hzero : u zeroMode = 0) :
    weightedProductionIncidenceTotal u =
      physicalWeightedProductionIncidenceTotal u := by
  exact weightedIncidence_eq_physicalWeightedIncidence u hzero

end Rational345R823RealProductionIncidenceTest
end NSBControl
