import Synthesis.RiemannProjectiveJointComplementQuadratic

namespace Synthesis

example :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ}, ContDiff ℝ 2 g → (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) → 0 ≤ Λ → ∀ t r : ℝ,
          |Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect g t r
            + Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect g t r|
            ≤ r ^ 2 *
              (4 * Zeta23Bridge.LiteralWeilProjectiveStripConstant.projStripCoeff g Λ t
                    * Zeta23Bridge.LiteralWeilOffOrdinateTail.offOrdWeight t
                + Zeta23Bridge.LiteralWeilProjectiveStripConstant.projStripCoeff g Λ t * CG) :=
  exists_jointProjectiveComplementQuadraticEnvelope

end Synthesis
