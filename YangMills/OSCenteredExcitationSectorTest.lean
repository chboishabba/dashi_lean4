import Mathlib
import YangMills.OSCenteredExcitationSector

namespace RequestProject.YangMills

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ⟪Ω, Ω⟫_ℝ = 1) :
    DenseRange (centerToVacuumOrthogonal Ω hΩ) :=
  denseRange_centerToVacuumOrthogonal Ω hΩ

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (Ω : data.Hilbert) (hΩ : ⟪Ω, Ω⟫_ℝ = 1) :
    DenseRange (data.centeredRawVector Ω hΩ) :=
  data.denseRange_centeredRawVector Ω hΩ

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω left right : H) (T : H →ₗ[ℝ] H)
    (hΩ : ⟪Ω, Ω⟫_ℝ = 1)
    (hFix : T Ω = Ω)
    (hSymm : ∀ x y, ⟪x, T y⟫_ℝ = ⟪T x, y⟫_ℝ) :
    ⟪osCenteredWilsonVector Ω left, T (osCenteredWilsonVector Ω right)⟫_ℝ =
      ⟪left, T right⟫_ℝ - ⟪Ω, left⟫_ℝ * ⟪Ω, right⟫_ℝ :=
  os_centered_mixed_semigroup_correlation Ω left right T hΩ hFix hSymm

end RequestProject.YangMills
