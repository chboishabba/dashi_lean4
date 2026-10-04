import NSBControl.Rational345R831TerminalCarrier

namespace NSBControl
namespace Rational345R831TerminalCarrierTest

open Rational345R831ReserveDecision

example (weld : R823PhysicalReserveSemanticWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_terminalSemanticWeld weld

example (data : R823Cutoff4TouchedCarrierWeldData) :
    R823PhysicalReserveSemanticWeld := by
  exact terminalSemanticWeld_of_cutoff4TouchedCarrier data

example (data : R823Cutoff4TouchedCarrierWeldData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_literalTouchedCarrier data

example : r831AfterTerminalSemanticWeldClosed = true := by
  rfl

example : r823PhysicalReserveSemanticCarrierClosed = false := by
  rfl

end Rational345R831TerminalCarrierTest
end NSBControl
