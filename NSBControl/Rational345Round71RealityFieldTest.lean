import NSBControl.Rational345Round71RealityField

namespace NSBControl
namespace Rational345Round71RealityFieldTest

open Rational345RealRadius4
open Rational345Round71PhysicalCarrier
open Rational345Round71RealityField

example (k : Mode) (v : Vec3) :
    leray (negateMode k) (vecConj v) = vecConj (leray k v) := by
  exact leray_reality k v

example (a : CanonicalState) (k : Mode) :
    projectedNonlinearity (decode a) (negateMode k) =
      vecConj (projectedNonlinearity (decode a) k) := by
  exact projectedNonlinearity_decode_reality a k

example (a : CanonicalState) (k : Mode) :
    galerkinField (decode a) (negateMode k) =
      vecConj (galerkinField (decode a) k) := by
  exact galerkinField_decode_reality a k

example (u : State) : realityTransform (realityTransform u) = u := by
  exact realityTransform_involutive u

example (u : State) :
    galerkinField (realityTransform u) =
      realityTransform (galerkinField u) := by
  exact galerkinField_reality_equivariant u

end Rational345Round71RealityFieldTest
end NSBControl
