import NSBControl.Rational345BPProduction

namespace NSBControl
namespace Rational345BPProductionTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPBudget
open Rational345BPMaxCut
open Rational345BPProduction

example : ProductionLeaf := by
  exact productionLeaf_closed

end Rational345BPProductionTest
end NSBControl
