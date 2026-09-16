import Welds.YMVacuumGapBackwardBounds

namespace Welds.YMVacuumGapBackwardBoundsRegression

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

example (D : VacuumGapDatum E) {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (hψ : D.op ψ = y) :
    ‖(ψ : E)‖ ≤ D.gap⁻¹ * ‖y‖ :=
  zeroShiftResolventBound D hψorth hψ

example {U V : ℝ → E → E} {S : Submodule ℂ E} {H₁ H₂ : E →ₗ.[ℂ] E}
    (hUV : U = V) (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁)
    (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁)
    {ψ : H₂.domain} (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ D.gap⁻¹ * ‖H₂ ψ‖ :=
  sameObjectZeroShiftResolventBound hUV hc₁ hc₂ hg₁ hg₂ D hD hψorth

example {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ YangMills.splitCost (2 / 5)) (hh : h ≤ 1 / 2)
    (D : VacuumGapDatum E)
    (hphysical : YangMills.bMinus (YangMills.casimirAdjointSU N) r h ≤ D.gap)
    {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (hψ : D.op ψ = y) :
    ‖(ψ : E)‖ ≤
      (YangMills.bMinus (YangMills.casimirAdjointSU N) r h)⁻¹ * ‖y‖ :=
  rowA1CandidateZeroShiftBound hN hr hh D hphysical hψorth hψ

end Welds.YMVacuumGapBackwardBoundsRegression
