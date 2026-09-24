import Synthesis.RiemannFinalLiteralComplementSignedReduction

namespace Synthesis

example :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          finalLiteralComplement g t r
            ≤ finalLiteralComplement g t 0
              + r ^ 2 *
                (4 * gammaCenteredStripCoeff g Λ t * offOrdWeight t
                  + 2 * CG * gammaCenteredStripCoeff g Λ t) :=
  exists_finalLiteralComplementCenteredUpper

example {S0 Sr B0 E M : ℝ}
    (hcenter : Sr ≤ S0 + E)
    (hbaseline : S0 ≤ B0)
    (hexcess : E < M) :
    Sr < B0 + M :=
  finalLiteralComplement_lt_baseline_add_margin hcenter hbaseline hexcess

end Synthesis
