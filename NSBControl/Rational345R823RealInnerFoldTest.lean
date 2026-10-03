import NSBControl.Rational345R823RealInnerFold

namespace NSBControl
namespace Rational345R823RealInnerFoldTest

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealInnerFold

example (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (hzero : u zeroMode = 0) :
    physicalOrderedFold u k = projectedNonlinearity u k := by
  exact physicalOrderedFold_eq_projectedNonlinearity u k hk hzero

example (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (hzero : u zeroMode = 0) :
    physicalPairedFold u k =
      projectedNonlinearity u k + projectedNonlinearity u k := by
  exact physicalPairedFold_eq_twiceProjectedNonlinearity u k hk hzero

example (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (hzero : u zeroMode = 0)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    physicalPairedFold u k = fourSignInnerFold u k := by
  exact physicalPairedFold_eq_fourSignInnerFold u k hk hzero htrans

end Rational345R823RealInnerFoldTest
end NSBControl
