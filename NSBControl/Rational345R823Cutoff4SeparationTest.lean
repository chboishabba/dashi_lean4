import NSBControl.Rational345R823Cutoff4Separation

namespace NSBControl
namespace Rational345R823Cutoff4SeparationTest

open Rational345RealRadius4
open Rational345R823Cutoff4Separation

example (k : Mode) : literalShellIndex4 k ≤ 2 := shellIndex4_le_two k

example (p q k : Mode) :
    classifyScale4 p q k = ScaleRegime.comparable := by
  exact classifyScale4_always_comparable p q k

example (p q k : Mode) : ccTouched4 p q k = true := by
  exact ccTouched4_always_true p q k

example (p q k : Mode) : separatedWeight4 p q k = 0 := by
  exact separatedWeight4_zero p q k

end Rational345R823Cutoff4SeparationTest
end NSBControl
