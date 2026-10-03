import NSBControl.Rational345R831R853PhysicalCarrierWeld

namespace NSBControl
namespace Rational345R831R853PhysicalCarrierWeldTest

open Rational345R831ReserveDecision

example (weld : R853PhysicalCarrierWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_r853Physical weld

example : r831R853ReducedToPhysicalCarrier = true := by
  rfl

example : r853PhysicalTrajectoryCarrierWeldClosed = false := by
  rfl

end Rational345R831R853PhysicalCarrierWeldTest
end NSBControl
