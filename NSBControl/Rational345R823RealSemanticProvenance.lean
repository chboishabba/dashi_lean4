import NSBControl.Rational345R831TerminalCarrier

/-!
# Real R823 reserve/demand semantic provenance at cutoff four

This file ports the *definition-level* content of Agda R823 to the genuine
real radius-four carrier used by R830.

Agda R823 defines, at the decision margin delta = nu,

  Reserve = signedComparableCC + 6 * nu * dissipation,
  Demand  = 2 * (Qsep - 9 * Nsep),

and its complete physical rate is

  2 * (9 * Nsep - Qsep) + signedComparableCC + 6 * nu * dissipation.

For the radius-four witness, the already-proved separation theorem removes the
fully-separated family, so Nsep = Qsep = 0.  Therefore the real R823 semantic
port has no additional hidden analytic content: its demand vanishes and its
reserve is exactly the original-multiplicity touched R760/R781/R822 signed
fold plus the critical viscous payment.

Crucially, `signedComparableCC` is not defined to be `selectedNonlinear`.
It comes from `R823Cutoff4TouchedCarrierWeldData.touchedSignedFold`, whose
same-object proof must retain the literal R760 cellwise scalar and original
multiplicity.  This makes the remaining semantic seam explicit rather than
circular.
-/

namespace NSBControl
namespace Rational345R823RealSemanticProvenance

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R853PhysicalScalarCarrier

/-- Real decision-margin viscosity.  The R830 normalization is nu = 1. -/
def r823Nu : ℝ := 1

/-- Cutoff-four separated nested four-helicity work.  The literal separated
family is empty on the radius-four witness. -/
def r823NestedSeparated (_data : R823Cutoff4TouchedCarrierWeldData)
    (_x : State) : ℝ := 0

/-- Cutoff-four separated cubic q-transfer.  The literal separated family is
empty on the radius-four witness. -/
def r823QSeparated (_data : R823Cutoff4TouchedCarrierWeldData)
    (_x : State) : ℝ := 0

/-- R822's original-multiplicity signed CC rows on the real carrier. -/
def r823SignedComparableCC
    (data : R823Cutoff4TouchedCarrierWeldData) (x : State) : ℝ :=
  data.touchedSignedFold x

/-- Literal real R823 viscous reserve contribution. -/
def r823ViscousReserve
    (_data : R823Cutoff4TouchedCarrierWeldData) (x : State) : ℝ :=
  6 * r823Nu * criticalDissipation x

/-- Definition-level real port of Agda R823 reserve. -/
def r823ReserveRate
    (data : R823Cutoff4TouchedCarrierWeldData) (x : State) : ℝ :=
  r823SignedComparableCC data x + r823ViscousReserve data x

/-- Definition-level real port of Agda R823 cubic/quintic demand. -/
def r823DemandRate
    (data : R823Cutoff4TouchedCarrierWeldData) (x : State) : ℝ :=
  2 * (r823QSeparated data x - 9 * r823NestedSeparated data x)

/-- Definition-level real port of Agda R823's complete payment decomposition. -/
def r823CompleteRate
    (data : R823Cutoff4TouchedCarrierWeldData) (x : State) : ℝ :=
  2 * (9 * r823NestedSeparated data x - r823QSeparated data x) +
    r823SignedComparableCC data x +
    r823ViscousReserve data x

/-- At cutoff four the exact R823 cubic/quintic demand vanishes. -/
theorem r823_cutoff4_demand_zero
    (data : R823Cutoff4TouchedCarrierWeldData) (x : State) :
    r823DemandRate data x = 0 := by
  simp [r823DemandRate, r823QSeparated, r823NestedSeparated]

/-- The source R823 algebra survives verbatim over the real carrier. -/
theorem r823_completeRate_eq_reserve_sub_demand
    (data : R823Cutoff4TouchedCarrierWeldData) :
    ∀ x, IsR823PhysicalState x →
      r823CompleteRate data x =
        r823ReserveRate data x - r823DemandRate data x := by
  intro x _hx
  unfold r823CompleteRate r823ReserveRate r823DemandRate
    r823SignedComparableCC r823ViscousReserve
    r823QSeparated r823NestedSeparated r823Nu
  ring

/-- The definition-level complete R823 rate normalizes to the public selected
rate once the literal touched carrier weld is supplied. -/
theorem r823_completeRate_eq_selectedRate
    (data : R823Cutoff4TouchedCarrierWeldData)
    (x : State) (hx : IsR823PhysicalState x) :
    r823CompleteRate data x = selectedRate x := by
  have hTouched : selectedNonlinear x = data.touchedSignedFold x := by
    calc
      selectedNonlinear x =
          Rational345R823TouchedNormalForm.r760SwapPairedResidualTotal x :=
        (Rational345R823TouchedNormalForm.r760SwapPairedResidualTotal_eq_selectedNonlinear x).symm
      _ = data.r760CellwiseFold x :=
        (data.r760Cellwise_eq_totalNormalForm x hx).symm
      _ = data.touchedSignedFold x :=
        (data.touched_eq_r760Cellwise x hx).symm
  calc
    r823CompleteRate data x =
        data.touchedSignedFold x + 6 * criticalDissipation x := by
      simp [r823CompleteRate, r823SignedComparableCC,
        r823ViscousReserve, r823QSeparated, r823NestedSeparated, r823Nu]
    _ = selectedNonlinear x + 6 * criticalDissipation x := by
      rw [hTouched]
    _ = selectedRate x :=
      (selectedRate_eq_selectedNonlinear_add_dissipation x).symm

/-- The definition-level real R823 complete rate is the concrete R853 complete
physical rate on the actual physical carrier. -/
theorem r823_completeRate_eq_r853CompletePhysicalRate
    (data : R823Cutoff4TouchedCarrierWeldData)
    (x : State) (hx : IsR823PhysicalState x) :
    r823CompleteRate data x = r853CompletePhysicalRate x := by
  exact (r823_completeRate_eq_selectedRate data x hx).trans
    (selectedRate_eq_r853CompletePhysicalRate x hx)

/-- Continuity of the source-faithful reserve definition. -/
theorem r823ReserveRate_continuous
    (data : R823Cutoff4TouchedCarrierWeldData) :
    Continuous (r823ReserveRate data) := by
  unfold r823ReserveRate r823SignedComparableCC r823ViscousReserve r823Nu
  exact data.touchedSignedFold_continuous.add
    (continuous_const.mul criticalDissipation_continuous_real)

/-- Continuity of the cutoff-four demand definition. -/
theorem r823DemandRate_continuous
    (data : R823Cutoff4TouchedCarrierWeldData) :
    Continuous (r823DemandRate data) := by
  simp only [r823DemandRate, r823QSeparated, r823NestedSeparated]
  fun_prop

/-- The literal touched carrier constructs the preferred terminal semantic
interface using the actual R823 reserve/demand definitions. -/
def realSemanticWeld_of_literalTouchedCarrier
    (data : R823Cutoff4TouchedCarrierWeldData) :
    R823PhysicalReserveSemanticWeld where
  reserveRate := r823ReserveRate data
  demandRate := r823DemandRate data
  completeRate_eq_reserve_sub_demand := by
    intro x hx
    calc
      r853CompletePhysicalRate x = r823CompleteRate data x :=
        (r823_completeRate_eq_r853CompletePhysicalRate data x hx).symm
      _ = r823ReserveRate data x - r823DemandRate data x :=
        r823_completeRate_eq_reserve_sub_demand data x hx
  reserveRate_continuous := r823ReserveRate_continuous data
  demandRate_continuous := r823DemandRate_continuous data

/-- Definition-level provenance is completely explicit over the real carrier. -/
def r823RealDefinitionProvenanceClosed : Bool := true

/-- At this cutoff, the preferred semantic port reduces to the same literal
original-multiplicity touched carrier theorem as the fallback. -/
def r823RealSemanticPortReducedToLiteralTouchedCarrier : Bool := true

/-- The remaining non-circular theorem is still the literal R760/R781/R822
same-object carrier weld. -/
def r823RealLiteralTouchedSameObjectClosed : Bool := false

end Rational345R823RealSemanticProvenance
end NSBControl
