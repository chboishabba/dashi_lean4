import NSBControl.Rational345R823LiteralR760CellMaxCut

namespace NSBControl
namespace Rational345R823LiteralR760CellMaxCutTest

open Rational345R823LiteralR760CellMaxCut
open Rational345R831ReserveDecision

example (data : LiteralR760CellCarrier) :
    R823Cutoff4TouchedCarrierWeldData := by
  exact touchedCarrierWeld_of_literalR760Cell data

example (data : LiteralR760CellCarrier) :
    R823PhysicalReserveSemanticWeld := by
  exact terminalSemanticWeld_of_literalR760Cell data

example (data : LiteralR760CellCarrier) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_literalR760Cell data

example : r823DecisionReducedToLiteralR760CompleteFold = true := by
  rfl

example : r823LiteralR760CompleteFoldSameObjectClosed = false := by
  rfl

end Rational345R823LiteralR760CellMaxCutTest
end NSBControl
