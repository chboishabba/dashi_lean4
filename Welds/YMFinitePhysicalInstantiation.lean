/-
# Finite physical Yang--Mills gap instantiation weld

The abstract Hilbert/operator/spectral machinery is already present in the imported
Yang--Mills lane.  The remaining finite-spacing obstruction is physical
instantiation: the selected finite Yang--Mills Hamiltonian must inhabit that
machinery, and the already-proved Row-A1 scalar must lower-bound the vacuum-sector
quadratic form of that *same* operator.

This module makes exactly that payment boundary theorem-bearing without hiding it
behind a Boolean or provenance receipt.

There are now two equivalent consumer-facing entry points:

1. `RowA1PhysicalGapInstance` accepts a genuine `VacuumGapDatum` plus the visible
   inequality `bMinus <= datum.gap`;
2. the more primitive `rowA1PhysicalGapInstanceOfDirectFormBound` starts directly
   from the physical operator, normalized zero-energy vacuum, self-adjointness,
   and the Row-A1 quadratic-form inequality itself.  It constructs the gap datum
   with `gap = bMinus`, so proof search no longer needs to presuppose a separately
   named physical gap before proving the Row-A1 lower bound.

Crucially, neither route manufactures the literal finite-spacing Yang--Mills
action, its measure, domain/core, self-adjointness, or direct form estimate.
-/
import Welds.YMVacuumGapBackwardBounds

namespace Welds.YMFinitePhysicalInstantiation

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Primitive physical constructor.**  If the literal finite-spacing operator
is already self-adjoint, has a normalized zero-energy vacuum, and satisfies the
Row-A1 quadratic-form lower bound on the vacuum complement, then it is a genuine
`VacuumGapDatum` with gap exactly `bMinus`.

This is the preferred backward proof-search target because it asks for the form
inequality directly rather than assuming a pre-existing larger gap. -/
noncomputable def rowA1GapDatumOfDirectFormBound
    {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ YangMills.splitCost (2 / 5)) (hh : h ≤ 1 / 2)
    (op : E →ₗ.[ℂ] E) (vac : E)
    (hmem : vac ∈ op.domain) (hunit : ‖vac‖ = 1)
    (hground : op ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint op)
    (hform : HasVacuumFormGap op vac
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h)) :
    VacuumGapDatum E where
  op := op
  vac := vac
  gap := YangMills.bMinus (YangMills.casimirAdjointSU N) r h
  vac_mem := hmem
  vac_unit := hunit
  vac_ground := hground
  selfAdjoint := hsa
  gap_pos := YangMills.bMinus_pos_SU hN hr hh
  form_gap := hform

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

/-- **Direct-form constructor for the physical instance.**  Once the literal
operator and its Row-A1 vacuum-complement form inequality are proved, the
`rowA1_le_gap` field is definitionally reflexive because the constructed gap is
exactly `bMinus`. -/
noncomputable def rowA1PhysicalGapInstanceOfDirectFormBound
    {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ YangMills.splitCost (2 / 5)) (hh : h ≤ 1 / 2)
    (op : E →ₗ.[ℂ] E) (vac : E)
    (hmem : vac ∈ op.domain) (hunit : ‖vac‖ = 1)
    (hground : op ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint op)
    (hform : HasVacuumFormGap op vac
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h)) :
    RowA1PhysicalGapInstance (E := E) N r h where
  hN := hN
  hr := hr
  hh := hh
  datum := rowA1GapDatumOfDirectFormBound hN hr hh op vac hmem hunit hground hsa hform
  rowA1_le_gap := le_rfl

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

#print axioms rowA1GapDatumOfDirectFormBound
#print axioms rowA1PhysicalGapInstanceOfDirectFormBound
#print axioms rowA1GapPositive
#print axioms rowA1GapDatum
#print axioms rowA1VacuumFormGap
#print axioms rowA1PhysicalZeroShiftBound

end Welds.YMFinitePhysicalInstantiation
