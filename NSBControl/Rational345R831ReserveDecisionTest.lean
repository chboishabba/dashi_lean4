import NSBControl.Rational345R831Cutoff4Touched

namespace NSBControl
namespace Rational345R831ReserveDecisionTest

open Set
open Rational345R831ReserveDecision
open Rational345RealRadius4

example {payment reserve demand : ℝ}
    (hneg : payment < 0)
    (hweld : payment = reserve - demand) :
    ¬ demand ≤ reserve := by
  exact negative_payment_refutes_reserve hneg hweld

example {payment reserve demand : ℝ}
    (hweld : payment = reserve - demand) :
    demand ≤ reserve ↔ 0 ≤ payment := by
  exact reserve_iff_nonnegative_payment hweld

example
    (weld : R823PhysicalPointwiseWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_physical_segment_refutes_r823_reserve weld

example
    (data : R823PhysicalNonlinearData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_physicalNonlinearData data

/-- At cutoff four the separated family is empty, so the live decision lane
must reduce to the touched/comparable same-object theorem alone. -/
example
    (data : R823Cutoff4TouchedData) :
    R823PhysicalNonlinearData := by
  exact physicalNonlinearData_of_cutoff4Touched data

example
    (data : R823Cutoff4TouchedData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_cutoff4Touched data

end Rational345R831ReserveDecisionTest
end NSBControl
