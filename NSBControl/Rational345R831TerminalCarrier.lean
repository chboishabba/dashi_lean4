import NSBControl.Rational345R853PhysicalScalarCarrier
import NSBControl.Rational345R831TouchedCarrierWeld

/-!
# R831 terminal physical carrier

The decision-normalized R853 three-scalar carrier is now concrete on the real
radius-four state space.  What R831 still needs is only the R823 semantic
identity saying that the same complete physical rate is reserve minus demand
on the live physical packet.

This file makes that the single preferred terminal interface.  It also shows
that the independent cutoff-four R760/R781/R822 touched-carrier route constructs
exactly the same interface, so the preferred and fallback lanes merge before
any integration or contradiction algebra.
-/

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4
open Rational345R853PhysicalScalarCarrier
open Rational345R823TouchedNormalForm

/-- Minimal terminal semantic weld.  The complete rate is the concrete R853
rate from `Rational345R853PhysicalScalarCarrier`; only reserve/demand packet
semantics remain abstract. -/
structure R823PhysicalReserveSemanticWeld where
  reserveRate : State → ℝ
  demandRate : State → ℝ

  completeRate_eq_reserve_sub_demand :
    ∀ x, IsR823PhysicalState x →
      r853CompletePhysicalRate x = reserveRate x - demandRate x

  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

/-- The concrete R853 scalar carrier plus the terminal R823 semantic identity
constructs exactly the physical pointwise weld already consumed by R831. -/
def physicalPointwiseWeld_of_terminalSemantic
    (weld : R823PhysicalReserveSemanticWeld) :
    R823PhysicalPointwiseWeld where
  reserveRate := weld.reserveRate
  demandRate := weld.demandRate
  selectedRate_eq_reserve_sub_demand := by
    intro x hx
    exact (selectedRate_eq_r853CompletePhysicalRate x hx).trans
      (weld.completeRate_eq_reserve_sub_demand x hx)
  reserveRate_continuous := weld.reserveRate_continuous
  demandRate_continuous := weld.demandRate_continuous

/-- Preferred terminal compiler: after the one R823 semantic carrier weld,
R830 and R831 immediately refute the reserve inequality. -/
theorem r830_refutes_r823_reserve_of_terminalSemanticWeld
    (weld : R823PhysicalReserveSemanticWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_physical_segment_refutes_r823_reserve
    (physicalPointwiseWeld_of_terminalSemantic weld)

/-- The cutoff-four literal touched-carrier route supplies the same terminal
semantic interface.  Its demand vanishes because the fully-separated family is
empty; its reserve is the original touched signed fold plus viscous payment. -/
def terminalSemanticWeld_of_cutoff4TouchedCarrier
    (data : R823Cutoff4TouchedCarrierWeldData) :
    R823PhysicalReserveSemanticWeld where
  reserveRate := fun x =>
    data.touchedSignedFold x + 6 * criticalDissipation x
  demandRate := fun _ => 0
  completeRate_eq_reserve_sub_demand := by
    intro x hx
    have hTouched : selectedNonlinear x = data.touchedSignedFold x := by
      calc
        selectedNonlinear x = r760SwapPairedResidualTotal x :=
          (r760SwapPairedResidualTotal_eq_selectedNonlinear x).symm
        _ = data.r760CellwiseFold x :=
          (data.r760Cellwise_eq_totalNormalForm x hx).symm
        _ = data.touchedSignedFold x :=
          (data.touched_eq_r760Cellwise x hx).symm
    calc
      r853CompletePhysicalRate x = selectedRate x := by
        exact (selectedRate_eq_r853CompletePhysicalRate x hx).symm
      _ = selectedNonlinear x + 6 * criticalDissipation x :=
        selectedRate_eq_selectedNonlinear_add_dissipation x
      _ = data.touchedSignedFold x + 6 * criticalDissipation x := by
        rw [hTouched]
      _ = (data.touchedSignedFold x + 6 * criticalDissipation x) - 0 := by
        ring
  reserveRate_continuous := by
    exact data.touchedSignedFold_continuous.add
      (continuous_const.mul criticalDissipation_continuous_real)
  demandRate_continuous := continuous_const

/-- Independent fallback route: one literal R760/R781/R822 carrier weld is
sufficient to reach the same reserve contradiction. -/
theorem r830_refutes_r823_reserve_of_literalTouchedCarrier
    (data : R823Cutoff4TouchedCarrierWeldData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_terminalSemanticWeld
    (terminalSemanticWeld_of_cutoff4TouchedCarrier data)

/-- R831 contains no remaining mathematics after the terminal semantic weld. -/
def r831AfterTerminalSemanticWeldClosed : Bool := true

/-- Preferred final leaf: port the actual R823 reserve/demand same-packet
identity to the concrete real R853 complete-rate carrier on physical states. -/
def r823PhysicalReserveSemanticCarrierClosed : Bool := false

/-- The fallback remains independently open only at the literal R760/R781/R822
cellwise same-object carrier theorem. -/
def r823LiteralTouchedCarrierFallbackClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
