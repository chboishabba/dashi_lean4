import NSBControl.Rational345R823RealSemanticProvenance

namespace NSBControl
namespace Rational345R823RealSemanticProvenanceTest

open Rational345R831ReserveDecision
open Rational345R823RealSemanticProvenance

example (data : R823Cutoff4TouchedCarrierWeldData) :
    ∀ x, IsR823PhysicalState x →
      r823CompleteRate data x = r823ReserveRate data x - r823DemandRate data x := by
  exact r823_completeRate_eq_reserve_sub_demand data

example (data : R823Cutoff4TouchedCarrierWeldData) :
    ∀ x, r823DemandRate data x = 0 := by
  exact r823_cutoff4_demand_zero data

example (data : R823Cutoff4TouchedCarrierWeldData) :
    R823PhysicalReserveSemanticWeld := by
  exact realSemanticWeld_of_literalTouchedCarrier data

example : r823RealDefinitionProvenanceClosed = true := by
  rfl

example : r823RealSemanticPortReducedToLiteralTouchedCarrier = true := by
  rfl

end Rational345R823RealSemanticProvenanceTest
end NSBControl
