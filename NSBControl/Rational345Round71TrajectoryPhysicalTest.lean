import NSBControl.Rational345Round71TrajectoryPhysical

namespace NSBControl
namespace Rational345Round71TrajectoryPhysicalTest

open Set
open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71RealityField
open Rational345Round71TrajectoryPhysical

example
    (u : ℝ → State) {ε : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ → realityTransform (u t) = u t := by
  exact trajectory_reality_radius u hε hu0 hderiv

end Rational345Round71TrajectoryPhysicalTest
end NSBControl
