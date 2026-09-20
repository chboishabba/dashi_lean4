import Synthesis.RiemannProjectiveRvMMuGammaSameObject
import Zeta23Bridge.LiteralWeilGammaProjectiveBound

/-!
# Named projective Gamma defect = twice the signed RvM-mu pairing

The exact projective Gamma channel is an even-cone object: it contains the
two symmetric sample contributions at +s and -s.  By contrast,
`projectiveRvMMuSignedPair` is the signed real part of one projective sample
at sampling radius zero.

Consequently the correct same-object normalization is

  gammaProjectiveDefect g t r
    = 2 * projectiveRvMMuSignedPair g t r.

The factor 2 is essential.  It matches the reflection-pair normalization on
the zero side and prevents an incorrect N-mu accounting identity.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilGammaProjectiveBound
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/--
The named literal projective Gamma defect is exactly twice the signed pairing
of the actual projective test against the theorem-bearing RvM density `mu`.
-/
theorem gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 < Λ)
    (t r : ℝ) :
    gammaProjectiveDefect g t r
      = 2 * projectiveRvMMuSignedPair g t r := by
  have hproj :=
    gammaProjectiveDefect_eq hgs heven hsupp hΛ t r
  have hpc : ContDiff ℝ 2 (projTaper g r) :=
    projTaper_contDiff hgs r
  have hpcpt : HasCompactSupport (projTaper g r) :=
    projTaper_hasCompactSupport
      (hgs.continuous.hasCompactSupport_of_isClosed ?_) r
  rw [hproj]
  unfold projectiveRvMMuSignedPair
  rw [projectiveRvMMuPair_eq_literalGammaTerm]
  have hgamma :
      reim (gammaTerm (sampleTest (projTaper g r) t 0))
        = gammaResp (projTaper g r) t 0 := by
    exact reim_gammaTerm_sampleTest
      (projTaper_continuous hgs.continuous r)
      (projTaper_hasCompactSupport
        (by
          -- compact support is inherited from g; derive it from the support
          -- hypothesis and closed bounded interval.
          apply HasCompactSupport.intro (K := Set.Icc (-Λ) Λ)
          · exact isCompact_Icc
          · intro x hx
            by_contra hgx
            have hs := hsupp x hgx
            simp only [Set.mem_Icc, not_and_or] at hx
            rcases hx with hx | hx
            · have habs : -Λ ≤ x := by
                have := neg_le_of_abs_le hs
                linarith
              exact hx habs
            · have habs : x ≤ Λ := le_of_abs_le hs
              exact hx habs) r)
      (projTaper_even heven r)
      t 0
  rw [hgamma]
  ring

end Synthesis
