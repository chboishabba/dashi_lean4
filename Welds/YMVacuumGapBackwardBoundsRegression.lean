import Welds.YMVacuumGapBackwardBounds

namespace Welds.YMVacuumGapBackwardBoundsRegression

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

example (D : VacuumGapDatum E) {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (hψ : D.op ψ = y) :
    ‖(ψ : E)‖ ≤ D.gap⁻¹ * ‖y‖ :=
  zeroShiftResolventBound D hψorth hψ

end Welds.YMVacuumGapBackwardBoundsRegression
