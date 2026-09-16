import Welds.YMFinitePhysicalInstantiation

namespace Welds.YMFinitePhysicalInstantiationRegression

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

example {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    0 < YangMills.bMinus (YangMills.casimirAdjointSU N) r h :=
  rowA1GapPositive I

example {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h) :
    HasVacuumFormGap I.datum.op I.datum.vac
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h) :=
  rowA1VacuumFormGap I

example {N : ℕ} {r h : ℝ}
    (I : RowA1PhysicalGapInstance (E := E) N r h)
    {y : E} {ψ : I.datum.op.domain}
    (hψorth : ⟪I.datum.vac, (ψ : E)⟫_ℂ = 0)
    (hψ : I.datum.op ψ = y) :
    ‖(ψ : E)‖ ≤
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h)⁻¹ * ‖y‖ :=
  rowA1PhysicalZeroShiftBound I hψorth hψ

end Welds.YMFinitePhysicalInstantiationRegression
