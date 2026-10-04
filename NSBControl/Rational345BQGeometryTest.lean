import NSBControl.Rational345BQGeometry

namespace NSBControl
namespace Rational345BQGeometryTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQGeometry

example : ‖u₀‖ ≤ 6 := u₀_norm_le_six
example (k : Mode) : normSq k ≤ 48 := normSq_le_48 k
example (k : Mode) (j : Fin 3) :
    2 * absCoord k j * sumAbs k ≤ 3 * normSqNat k :=
  leray_ratio_nat k j

end Rational345BQGeometryTest
end NSBControl
