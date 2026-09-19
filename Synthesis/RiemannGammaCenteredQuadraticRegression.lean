import Synthesis.RiemannGammaCenteredQuadraticEnvelope
import Synthesis.RiemannFinalComplementCenteredQuadratic

namespace Synthesis

example (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 :=
  abs_cos_sub_one_le_sq_div_two x

example :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |gammaResp (gammaCenteredTaper g r) t 0|
            ≤ r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) :=
  exists_centeredGammaQuadraticEnvelope

example :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |(evenConeFunctional (offOrdVec (sampleFam g t r) t)
              - evenConeFunctional (offOrdVec (sampleFam g t 0) t))
            + ((gammaResp g t r + gammaResp g t (-r))
                - 2 * gammaResp g t 0)|
          ≤ r ^ 2 *
            (4 * gammaCenteredStripCoeff g Λ t * offOrdWeight t
              + 2 * CG * gammaCenteredStripCoeff g Λ t) :=
  exists_finalComplementCenteredQuadraticEnvelope

end Synthesis
