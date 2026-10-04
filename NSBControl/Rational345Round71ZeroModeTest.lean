import NSBControl.Rational345Round71ZeroMode

namespace NSBControl
namespace Rational345Round71ZeroModeTest

open Set
open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71ZeroMode

example : isZeroMode zeroMode := zeroMode_is_zero

example (u : State) : galerkinField u zeroMode = 0 :=
  galerkinField_zeroMode u

example : u₀ zeroMode = 0 := initial_zeroMode

example
    (u : ℝ → State) {ε : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ → u t zeroMode = 0 := by
  exact trajectory_zeroMode_radius u hε hu0 hderiv

end Rational345Round71ZeroModeTest
end NSBControl
