import NSBControl.Rational345BPHelicalBounds

namespace NSBControl
namespace Rational345BPHelicalBoundsTest

open Rational345RealRadius4
open Rational345BPBudget
open Rational345BPHelicalBounds

example (k : Mode) (v : Vec3) :
    ‖helicalPlus k v‖ ≤ helicalConstant * ‖v‖ := by
  exact helicalPlus_norm_le k v

example (k : Mode) (v : Vec3) :
    ‖helicalMinus k v‖ ≤ helicalConstant * ‖v‖ := by
  exact helicalMinus_norm_le k v

end Rational345BPHelicalBoundsTest
end NSBControl
