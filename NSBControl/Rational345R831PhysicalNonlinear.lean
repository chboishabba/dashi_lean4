import NSBControl.Rational345R831PhysicalWeld

/-!
# R831 physical nonlinear max-cut

At the decision normalization nu = delta = 1, Agda R813/R815/R822 gives

  selected nonlinear = 2 * (9 * nested - q) + touched.

R823 then defines

  reserve = touched + 6 * dissipation,
  demand  = 2 * (q - 9 * nested).

Therefore the entire remaining pointwise semantic weld can be represented by
one same-object nonlinear identity on the physical state domain, plus
continuity of the three finite rate functions.  The reserve-minus-demand
identity is algebra from that point onward.
-/

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4

/-- Minimal real physical-state mirror of the combined R813/R815/R822
nonlinear content. -/
structure R823PhysicalNonlinearData where
  nestedFourHelicityWork : State → ℝ
  qsep : State → ℝ
  signedComparableCC : State → ℝ

  nestedFourHelicityWork_continuous : Continuous nestedFourHelicityWork
  qsep_continuous : Continuous qsep
  signedComparableCC_continuous : Continuous signedComparableCC

  nonlinear_sameObject :
    ∀ x, IsR823PhysicalState x →
      selectedNonlinear x =
        2 * (9 * nestedFourHelicityWork x - qsep x) +
          signedComparableCC x

/-- The single physical nonlinear same-object identity constructs the exact
R823 reserve/demand pointwise weld. -/
def r823PhysicalPointwiseWeld_of_nonlinearData
    (data : R823PhysicalNonlinearData) : R823PhysicalPointwiseWeld where
  reserveRate := fun x =>
    data.signedComparableCC x + 6 * criticalDissipation x
  demandRate := fun x =>
    2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)
  selectedRate_eq_reserve_sub_demand := by
    intro x hx
    calc
      selectedRate x
          = selectedNonlinear x + 6 * criticalDissipation x :=
            selectedRate_eq_selectedNonlinear_add_dissipation x
      _ = (2 * (9 * data.nestedFourHelicityWork x - data.qsep x) +
            data.signedComparableCC x) + 6 * criticalDissipation x := by
            rw [data.nonlinear_sameObject x hx]
      _ = (data.signedComparableCC x + 6 * criticalDissipation x) -
            (2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)) := by
            ring
  reserveRate_continuous := by
    exact data.signedComparableCC_continuous.add
      (continuous_const.mul criticalDissipation_continuous_real)
  demandRate_continuous := by
    exact continuous_const.mul
      (data.qsep_continuous.sub
        (continuous_const.mul data.nestedFourHelicityWork_continuous))

/-- Everything after the live physical nonlinear identity is now compiled. -/
theorem r830_refutes_r823_reserve_of_physicalNonlinearData
    (data : R823PhysicalNonlinearData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_physical_segment_refutes_r823_reserve
    (r823PhysicalPointwiseWeld_of_nonlinearData data)

/-- Exact remaining semantic leaf after the physical max-cut. -/
def r823PhysicalNonlinearSameObjectClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
