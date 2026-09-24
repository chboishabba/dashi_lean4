import Synthesis.RiemannRvMMuGammaSameObject
import Synthesis.RiemannGammaConeAbsoluteMargin
import Zeta23Bridge.LiteralWeilGammaChannel

/-!
# Four-sample/even-cone weld: exact RvM mu measure = literal Gamma vector

The upstream Riemann--von Mangoldt smooth measure is `mu(tau) d tau`.
The literal Weil Gamma term is exactly pairing against that same measure.

This file pushes that scalar identity through the actual four-sample family and
the even-cone consumer used by the RH high argument.

Define the signed RvM-mu coordinate with the SAME sign as `gammaVec`:

  muCoord(k) = - reim (integral paperFT(k)(tau) * mu(tau) d tau).

Then, for every four-sample family,

  rvMMuVec(kFam) = gammaVec(kFam).

Hence for the literal canonical centered taper the already-proved fixed negative
Gamma margin is simultaneously a fixed negative margin for the exact smooth RvM
measure contribution.  There is no independent M_RvM term to estimate or add.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def rvMMuCoord (k : ℝ → ℂ) : ℝ :=
  - reim (∫ tau : ℝ, paperFT k tau * (Zeta23.mu tau : ℂ))

def rvMMuVec (kFam : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ :=
  fun i => rvMMuCoord (kFam i)

theorem rvMMuCoord_eq_gammaVecCoord (k : ℝ → ℂ) :
    rvMMuCoord k = - reim (gammaTerm k) := by
  unfold rvMMuCoord
  rw [← literalGammaTerm_eq_rvMMuPair]

theorem rvMMuVec_eq_gammaVec (kFam : Fin 4 → ℝ → ℂ) :
    rvMMuVec kFam = gammaVec kFam := by
  funext i
  exact rvMMuCoord_eq_gammaVecCoord (kFam i)

theorem evenCone_rvMMuVec_eq_gammaVec
    (kFam : Fin 4 → ℝ → ℂ) :
    evenConeFunctional (rvMMuVec kFam)
      =
    evenConeFunctional (gammaVec kFam) := by
  rw [rvMMuVec_eq_gammaVec]

/--
For the literal sample family, the smooth RvM measure has exactly the same
parity decomposition as the Gamma channel.
-/
theorem rvMMuVec_sampleFam_parity
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    rvMMuVec (sampleFam g t r)
      =
    evenPattern (-gammaEvenResp g t r)
        (-gammaEvenResp g t (2 * r))
      +
    oddPattern (-gammaOddResp g t r)
        (-gammaOddResp g t (2 * r)) := by
  rw [rvMMuVec_eq_gammaVec]
  exact gammaVec_sampleFam_parity hg hgc heven t r

/--
The exact smooth RvM measure contribution on the canonical centered taper is
uniformly negative by the same fixed constant already proved for Gamma.
-/
theorem quantitativeCanonicalRvMMuCone_uniform_deficit
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (rvMMuVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      <=
    - canonicalGammaConeAbsoluteMargin := by
  rw [rvMMuVec_eq_gammaVec]
  exact quantitativeCanonicalGammaCone_uniform_deficit ht

theorem quantitativeCanonicalRvMMuCone_uniform_neg
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (rvMMuVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      < 0 := by
  have h := quantitativeCanonicalRvMMuCone_uniform_deficit ht
  have hc := canonicalGammaConeAbsoluteMargin_pos
  linarith

end Synthesis
