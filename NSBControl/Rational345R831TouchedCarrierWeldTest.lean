import NSBControl.Rational345R831TouchedCarrierWeld

namespace NSBControl
namespace Rational345R831TouchedCarrierWeldTest

open Rational345R831ReserveDecision

example (data : R823Cutoff4TouchedCarrierWeldData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_cutoff4TouchedCarrierWeld data

example (data : R823Cutoff4TouchedCarrierWeldData) :
    R823Cutoff4TouchedData := by
  exact cutoff4TouchedData_of_carrierWeld data

example : r823Cutoff4CarrierCompilerClosed = true := by
  rfl

example : r823Cutoff4LiteralCarrierSameObjectClosed = false := by
  rfl

end Rational345R831TouchedCarrierWeldTest
end NSBControl
