/-
# Finite physical Yang--Mills gap instantiation weld

The abstract Hilbert/operator/spectral machinery is already present in the imported
Yang--Mills lane.  The remaining finite-spacing obstruction is physical
instantiation: the selected finite Yang--Mills Hamiltonian must inhabit that
machinery, and the already-proved Row-A1 scalar must lower-bound the vacuum-sector
quadratic form of that *same* operator.

This module makes exactly that payment boundary theorem-bearing without hiding it
behind a Boolean or provenance receipt.  A `RowA1PhysicalGapInstance` contains:

* the existing `SU(N)`/budget hypotheses that prove `0 < bMinus`;
* a genuine `VacuumGapDatum`, hence an actual self-adjoint partial-domain operator,
  normalized zero-energy vacuum, and vacuum-sector form gap;
* the live physical same-object inequality `bMinus <= datum.gap`.

Once those inputs exist, no further spectral argument is needed: the Row-A1 form
gap and zero-shift inverse budget follow from the already-existing compilers.

Crucially, constructing an inhabitant of `RowA1PhysicalGapInstance` for the
literal finite-spacing Yang--Mills action remains physical work.  This file does
not manufacture that Hamiltonian, its dense core, self-adjointness, or the
inequality relating its quadratic form to `bMinus`.
-/
import Welds.YMVacuumGapBackwardBounds

namespace Welds.YMFinitePhysicalInstantiation

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The exact finite-spacing physical payment required to turn the already-proved
Row-A1 scalar into a Hamiltonian vacuum gap.

`rowA1_le_gap` is intentionally explicit.  Positivity of `bMinus` is analytic
source mathematics; it does not by itself identify that scalar with the gap of a
particular Yang--Mills Hamiltonian. -/
structure RowA1PhysicalGapInstance (N : ℕ) (r h : ℝ) where
  hN : 2 ≤ N
  hr : r ≤ YangMills.splitCost (2 / 5)
  hh : h ≤ 1 / 2
  datum : VacuumGapDatum E
  rowA1_le_gap :
    YangMills.bMinus (YangMills.casimirAdjointSU N) r h ≤ datum.gap

/-- The Row-A1 candidate is strictly positive from the existing `LocalGap`
theorem, independently of the physical Hamiltonian weld. -/
theorem rowA1GapPositive {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    0 < YangMills.bMinus (YangMills.casimirAdjointSU N) r h :=
  YangMills.bMinus_pos_SU I.hN I.hr I.hh

/-- The physical datum weakened to the concrete Row-A1 lower-gap constant.  The
operator, domain and vacuum are definitionally the same as in `I.datum`; only
the certified gap constant is lowered. -/
noncomputable def rowA1GapDatum {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) : VacuumGapDatum E :=
  YMVacuumGapBackwardBounds.weakenGapDatum I.datum
    (rowA1GapPositive I) I.rowA1_le_gap

@[simp] theorem rowA1GapDatum_op {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    (rowA1GapDatum I).op = I.datum.op := rfl

@[simp] theorem rowA1GapDatum_vac {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    (rowA1GapDatum I).vac = I.datum.vac := rfl

@[simp] theorem rowA1GapDatum_gap {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    (rowA1GapDatum I).gap =
      YangMills.bMinus (YangMills.casimirAdjointSU N) r h := rfl

/-- **Finite-spacing Balaban/Row-A1 -> Hamiltonian form-gap weld.**

Once the live same-object inequality is supplied, the selected physical operator
obeys the Row-A1 quadratic-form gap on its vacuum complement. -/
theorem rowA1VacuumFormGap {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    HasVacuumFormGap I.datum.op I.datum.vac
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h) := by
  simpa [rowA1GapDatum] using (rowA1GapDatum I).form_gap

/-- Quantitative zero-shift consumer for the literal physical instance. -/
theorem rowA1PhysicalZeroShiftBound {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h)
    {y : E} {ψ : I.datum.op.domain}
    (hψorth : ⟪I.datum.vac, (ψ : E)⟫_ℂ = 0)
    (hψ : I.datum.op ψ = y) :
    ‖(ψ : E)‖ ≤
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h)⁻¹ * ‖y‖ :=
  YMVacuumGapBackwardBounds.rowA1CandidateZeroShiftBound
    I.hN I.hr I.hh I.datum I.rowA1_le_gap hψorth hψ

#print axioms rowA1GapPositive
#print axioms rowA1GapDatum
#print axioms rowA1VacuumFormGap
#print axioms rowA1PhysicalZeroShiftBound

end Welds.YMFinitePhysicalInstantiation
