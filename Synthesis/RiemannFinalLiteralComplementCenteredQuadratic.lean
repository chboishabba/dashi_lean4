import Synthesis.RiemannFinalComplementCenteredQuadratic

/-!
# Literal final complement centered quadratic bound

The final explicit-formula complement is the actual signed sum

    S(g,t,r) := D_off(g,t,r) + Q_Gamma(g,t,r),

where Q_Gamma is the even-cone Gamma channel itself.  Since

    Q_Gamma(g,t,r) = -(Gamma_g(t,r) + Gamma_g(t,-r)),

the previously source-written centered Gamma response correction appears with
the opposite sign in the literal complement.

This file records the exact consumer-faithful statement:

    |S(g,t,r) - S(g,t,0)| <= r^2 * E_center.

No projective response/balance semantics are used.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilOffOrdinateTail

def finalLiteralComplement (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  evenConeFunctional (offOrdVec (sampleFam g t r) t)
    + evenConeFunctional (gammaVec (sampleFam g t r))

theorem gammaCone_centered_radius {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    evenConeFunctional (gammaVec (sampleFam g t r))
      - evenConeFunctional (gammaVec (sampleFam g t 0))
      = -2 * gammaResp (gammaCenteredTaper g r) t 0 := by
  have hr := gammaConeValue_exact hgs.continuous hgc heven t r
  have h0 := gammaConeValue_exact hgs.continuous hgc heven t 0
  have hc := gammaResp_centered_radius hgs hgc heven hsupp hΛ t r
  rw [hr, h0]
  simp only [neg_zero]
  linarith

theorem exists_finalLiteralComplementCenteredQuadratic :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |finalLiteralComplement g t r - finalLiteralComplement g t 0|
            ≤ r ^ 2 *
              (4 * gammaCenteredStripCoeff g Λ t * offOrdWeight t
                + 2 * CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨CG, hCG, hGamma⟩ := exists_centeredGammaQuadraticEnvelope
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  have hgc :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.hasCompactSupport_of_radius hsupp
  have hOff := abs_finalOffOrd_centered_le hgs heven hsupp hΛ t r
  have hGammaCenter :=
    gammaCone_centered_radius hgs hgc heven hsupp hΛ t r
  have hGammaBound := hGamma hgs heven hsupp hΛ t r
  have hGamma :
      |evenConeFunctional (gammaVec (sampleFam g t r))
        - evenConeFunctional (gammaVec (sampleFam g t 0))|
        ≤ 2 * r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
    rw [hGammaCenter, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    nlinarith
  unfold finalLiteralComplement
  have hsplit :
      (evenConeFunctional (offOrdVec (sampleFam g t r) t)
          + evenConeFunctional (gammaVec (sampleFam g t r)))
        - (evenConeFunctional (offOrdVec (sampleFam g t 0) t)
          + evenConeFunctional (gammaVec (sampleFam g t 0)))
      =
      (evenConeFunctional (offOrdVec (sampleFam g t r) t)
          - evenConeFunctional (offOrdVec (sampleFam g t 0) t))
        + (evenConeFunctional (gammaVec (sampleFam g t r))
          - evenConeFunctional (gammaVec (sampleFam g t 0))) := by ring
  rw [hsplit]
  have htri := abs_add_le
    (evenConeFunctional (offOrdVec (sampleFam g t r) t)
      - evenConeFunctional (offOrdVec (sampleFam g t 0) t))
    (evenConeFunctional (gammaVec (sampleFam g t r))
      - evenConeFunctional (gammaVec (sampleFam g t 0)))
  nlinarith [htri, hOff, hGamma]

end Synthesis
