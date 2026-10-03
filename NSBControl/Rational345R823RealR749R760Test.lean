import NSBControl.Rational345R823RealR749R760

namespace NSBControl
namespace Rational345R823RealR749R760Test

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823RealR749R760

example (u : State) (hu : IsR823PhysicalState u) :
    r760SwapPairedResidualCompleteFold u = selectedNonlinear u := by
  exact r760SwapPairedResidualCompleteFold_eq_selectedNonlinear u hu

example : ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_literalR760Cell literalR760CellCarrier

end Rational345R823RealR749R760Test
end NSBControl
