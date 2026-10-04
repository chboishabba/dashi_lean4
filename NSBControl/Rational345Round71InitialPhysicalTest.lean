import NSBControl.Rational345Round71InitialPhysical

namespace NSBControl
namespace Rational345Round71InitialPhysicalTest

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71RealityField
open Rational345Round71InitialPhysical

example : realityTransform u₀ = u₀ := by
  exact initial_reality

example (k : Mode) :
    bilinearDot (kComplex k) (u₀ k) = 0 := by
  exact initial_transverse k

end Rational345Round71InitialPhysicalTest
end NSBControl
