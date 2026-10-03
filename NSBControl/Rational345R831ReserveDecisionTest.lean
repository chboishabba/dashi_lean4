import NSBControl.Rational345R831ReserveDecision

namespace NSBControl
namespace Rational345R831ReserveDecisionTest

open Rational345R831ReserveDecision

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
    (hWeld : R823WeldForR830Witness) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve hWeld

end Rational345R831ReserveDecisionTest
end NSBControl
