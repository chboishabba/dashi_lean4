import NSBControl.Rational345Round71PhysicalCarrier

namespace NSBControl
namespace Rational345Round71PhysicalCarrierTest

open Rational345RealRadius4
open Rational345Round71PhysicalCarrier

example (k : Mode) : negateMode (negateMode k) = k := by
  exact negateMode_involutive k

example {k : Mode} (hk : ¬ isZeroMode k) :
    leadingPositive k ↔ ¬ leadingPositive (negateMode k) := by
  exact leadingPositive_negate_iff_not hk

example (a : CanonicalState) :
    decode a (Mode.mk 4 4 4) = 0 := by
  exact decode_zero a

example (a : CanonicalState) (k : CanonicalMode) :
    decode a k.1 = a k := by
  exact decode_positive a k

example (a : CanonicalState) (k : CanonicalMode) :
    decode a (negateMode k.1) = vecConj (a k) := by
  exact decode_negative a k

end Rational345Round71PhysicalCarrierTest
end NSBControl
