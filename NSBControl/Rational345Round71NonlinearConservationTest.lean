import NSBControl.Rational345Round71NonlinearConservation

namespace NSBControl
namespace Rational345Round71NonlinearConservationTest

open Rational345RealRadius4
open Rational345Round71PhysicalCarrier
open Rational345Round71NonlinearConservation

example
    (u : State)
    (hreality : ∀ k, u (negateMode k) = vecConj (u k))
    (hdiv : ∀ k, bilinearDot (kComplex k) (u k) = 0) :
    rawProjectedPairingReal u = 0 := by
  exact rawProjectedPairingReal_eq_zero u hreality hdiv

end Rational345Round71NonlinearConservationTest
end NSBControl
