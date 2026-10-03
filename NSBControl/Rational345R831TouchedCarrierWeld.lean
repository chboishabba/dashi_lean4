import NSBControl.Rational345R831Cutoff4Touched
import NSBControl.Rational345R823TouchedNormalForm

/-!
# R831 cutoff-four touched carrier weld

The cutoff-four decision lane has already removed the fully-separated family,
so the only remaining semantic content is the literal R760/R781/R822 touched
fold.  Do not identify that fold with `selectedNonlinear` by definition: Agda
R822 retains each original R760 signed scalar and merely attaches a comparable
representative.

This owner therefore keeps three objects distinct:

* the literal real R760 cellwise fold;
* the R781/R822 touched/comparable fold built from those same original cells;
* the public R830 nonlinear selected rate.

The first two equalities are the genuine carrier weld.  Once supplied on the
physical state domain, the already-proved R745--R760 scalar normal form turns
it into the exact `R823Cutoff4TouchedData` consumed by R831.
-/

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4
open Rational345R823TouchedNormalForm

/-- Exact same-object boundary still required from the concrete real
R760/R781/R822 cell implementation.

`touchedSignedFold` must retain the original R760 signed cells with their
original multiplicity; a representative may carry localization evidence but
must not replace the scalar being summed. -/
structure R823Cutoff4TouchedCarrierWeldData where
  r760CellwiseFold : State → ℝ
  touchedSignedFold : State → ℝ

  touchedSignedFold_continuous : Continuous touchedSignedFold

  touched_eq_r760Cellwise :
    ∀ x, IsR823PhysicalState x →
      touchedSignedFold x = r760CellwiseFold x

  r760Cellwise_eq_totalNormalForm :
    ∀ x, IsR823PhysicalState x →
      r760CellwiseFold x = r760SwapPairedResidualTotal x

/-- The literal carrier weld constructs the exact cutoff-four touched datum.
No sign estimate or representative re-evaluation is introduced here. -/
def cutoff4TouchedData_of_carrierWeld
    (data : R823Cutoff4TouchedCarrierWeldData) :
    R823Cutoff4TouchedData where
  signedComparableCC := data.touchedSignedFold
  signedComparableCC_continuous := data.touchedSignedFold_continuous
  touched_sameObject := by
    intro x hx
    calc
      selectedNonlinear x = r760SwapPairedResidualTotal x := by
        exact (r760SwapPairedResidualTotal_eq_selectedNonlinear x).symm
      _ = data.r760CellwiseFold x := by
        exact (data.r760Cellwise_eq_totalNormalForm x hx).symm
      _ = data.touchedSignedFold x := by
        exact (data.touched_eq_r760Cellwise x hx).symm

/-- Terminal max-cut compiler: a concrete same-object R760/R781/R822 carrier
weld on the physical radius-four state domain is sufficient to refute the
R823 reserve inequality using the already-built negative R830 packet. -/
theorem r830_refutes_r823_reserve_of_cutoff4TouchedCarrierWeld
    (data : R823Cutoff4TouchedCarrierWeldData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_cutoff4Touched
    (cutoff4TouchedData_of_carrierWeld data)

/-- Everything after the literal cellwise carrier identity is compiled. -/
def r823Cutoff4CarrierCompilerClosed : Bool := true

/-- Honest terminal status: the concrete real R760/R781/R822 same-object
carrier identity itself is still a proof obligation until instantiated. -/
def r823Cutoff4LiteralCarrierSameObjectClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
