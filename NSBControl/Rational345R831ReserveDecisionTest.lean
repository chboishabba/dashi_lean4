import NSBControl.Rational345R831PhysicalWeld

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
    (weld : R853RealCarrierWeld) :
    R823PointwiseWeld := by
  exact r823PointwiseWeld_of_r853 weld

example
    (weld : R853RealCarrierWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_refutes_r823_reserve_of_r853 weld

/-- Max-cut regression: R831 must only require the R823 identity on the
physical state domain actually traversed by the R830 witness. -/
example
    (weld : R823PhysicalPointwiseWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_physical_segment_refutes_r823_reserve weld

/-- The live R813/R815/R822 semantic residue is one nonlinear same-object
identity on physical states, not three independent downstream assumptions. -/
example
    (data : R823PhysicalNonlinearData) :
    R823PhysicalPointwiseWeld := by
  exact r823PhysicalPointwiseWeld_of_nonlinearData data

example
    (data : R823PhysicalNonlinearData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  exact r830_physical_segment_refutes_r823_reserve
    (r823PhysicalPointwiseWeld_of_nonlinearData data)

end Rational345R831ReserveDecisionTest
end NSBControl
