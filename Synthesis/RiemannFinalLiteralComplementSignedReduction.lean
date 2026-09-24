import Synthesis.RiemannFinalLiteralComplementCenteredQuadratic
import Zeta23Bridge.PoleQuotientComplementMargin

/-!
# Signed reduction for the literal final complement

The preferred consumer is signed.  This file records two facts:

1. the centered absolute estimate gives the one-sided order estimate

     S(r) <= S(0) + r^2 E_center,

   for the literal signed complement
     S = Off + Q_Gamma;

2. radius zero is NOT automatically the pole-quotient baseline.  For a short
   taper the prime term vanishes at radius zero, but the pole term generally
   survives:

     -(Off(0)+Q_Gamma(0)) = Cluster(0) + Pole(0).

Thus complementChannels_pinned at the selected pole-killing radius cannot simply
be substituted as an S(0) <= B0 theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.PoleQuotientComplementMargin

theorem exists_finalLiteralComplementCenteredUpper :
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
                  + 2 * CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨CG, hCG, hcenter⟩ := exists_finalLiteralComplementCenteredQuadratic
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  have h := hcenter hgs heven hsupp hΛ t r
  have hdir :
      finalLiteralComplement g t r - finalLiteralComplement g t 0
        ≤ |finalLiteralComplement g t r - finalLiteralComplement g t 0| :=
    le_abs_self _
  linarith

/-- At radius zero, prime vanishing does not remove the pole channel. -/
theorem radiusZero_literal_complement_with_pole {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    (t : ℝ) :
    -(finalLiteralComplement g t 0)
      =
    evenConeFunctional (clusterVec (sampleFam g t 0) t)
      + evenConeFunctional (poleVec (sampleFam g t 0)) := by
  have hprime : primeVec (sampleFam g t 0) = 0 :=
    primeVec_eq_zero_of_short_taper hshort t 0
  have hkd := fun i => sampleFam_contDiff hgs t 0 i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t 0 i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hlin :
      evenConeFunctional (clusterVec (sampleFam g t 0) t)
        + evenConeFunctional (offOrdVec (sampleFam g t 0) t)
        + evenConeFunctional (primeVec (sampleFam g t 0))
        + evenConeFunctional (gammaVec (sampleFam g t 0))
        + evenConeFunctional (poleVec (sampleFam g t 0)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  rw [hprime, map_zero, add_zero] at hlin
  unfold finalLiteralComplement
  linarith

/--
Conditional signed-chain compiler.  If a future independent same-object theorem
supplies S(0) <= B0 and the explicit centered excess is smaller than M, then
S(r) < B0 + M.  This theorem does not manufacture the baseline hypothesis.
-/
theorem finalLiteralComplement_lt_baseline_add_margin
    {S0 Sr B0 E M : ℝ}
    (hcenter : Sr ≤ S0 + E)
    (hbaseline : S0 ≤ B0)
    (hexcess : E < M) :
    Sr < B0 + M := by
  linarith

end Synthesis
