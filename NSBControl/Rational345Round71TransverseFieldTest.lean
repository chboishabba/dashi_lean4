import NSBControl.Rational345Round71TransverseField

namespace NSBControl
namespace Rational345Round71TransverseFieldTest

open Rational345RealRadius4
open Rational345Round71TransverseField

example {k : Mode} (hk : ¬ isZeroMode k) (v : Vec3) :
    bilinearDot (kComplex k) (leray k v) = 0 := by
  exact leray_transverse hk v

example (u : State) (k : Mode) :
    bilinearDot (kComplex k) (projectedNonlinearity u k) = 0 := by
  exact projectedNonlinearity_transverse u k

example (u : State) (k : Mode) :
    bilinearDot (kComplex k) (galerkinField u k) =
      -(normSq k : ℂ) * bilinearDot (kComplex k) (u k) := by
  exact divergence_field_identity u k

end Rational345Round71TransverseFieldTest
end NSBControl
