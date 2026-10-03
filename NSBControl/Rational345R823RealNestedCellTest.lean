import NSBControl.Rational345R823RealNestedCell

namespace NSBControl
namespace Rational345R823RealNestedCellTest

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealNestedCell

example (u : State) (p q : Mode)
    (hp : nonzeroMode p) (hq : nonzeroMode q)
    (hzero : u zeroMode = 0)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    realNestedCell u p q =
      4 • forcingCommutatorCell u (projectedNonlinearity u) p q := by
  exact realNestedCell_eq_fourCommutator u p q hp hq hzero htrans

end Rational345R823RealNestedCellTest
end NSBControl
