import NSBControl.Rational345R831ReserveDecision

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
    (hWeld : R823WeldForR830Witness) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve hWeld

example
    (weld : R823PointwiseWeld)
    (u : ℝ → State) (terminal : ℝ)
    (hu : ContinuousOn u (uIcc (0 : ℝ) terminal)) :
    selectedPayment u terminal =
      integratedReserve weld u terminal - integratedDemand weld u terminal := by
  exact integrated_weld_of_pointwise weld hu

example
    (hPointwise : R823PointwiseWeld) :
    R823WeldForR830Witness := by
  exact r823WitnessWeld_of_pointwise hPointwise

example
    (data : R823NonlinearPointwiseData) :
    R823PointwiseWeld := by
  exact r823PointwiseWeld_of_nonlinearData data

example
    (data : R823NonlinearPointwiseData) :
    ∀ x : State,
      selectedRate x =
        (data.signedComparableCC x + 6 * criticalDissipation x) -
        (2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)) := by
  exact r823_pointwise_identity_of_nonlinearData data

end Rational345R831ReserveDecisionTest
end NSBControl
