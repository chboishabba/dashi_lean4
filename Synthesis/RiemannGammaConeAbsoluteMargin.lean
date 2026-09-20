import Synthesis.RiemannGammaEndpointGapAbsoluteScale
import Synthesis.RiemannGammaInnerPoleAbsoluteScale
import Synthesis.RiemannQuantitativeGammaDeficit

/-!
# Uniform absolute deficit of the literal canonical Gamma cone

The two absolute-scale inputs are now explicit:

  -P_in(t) >= pi * M0 / (4 t),

and

  canonicalGammaRatioGap(t)
    >= pi * (2636149 / 17899520000) * t.

Their t factors cancel.  Since the literal canonical Gamma theorem already gives

  Q_Gamma(t) <= -2 (-P_in(t)) canonicalGammaRatioGap(t),

we obtain a fixed positive margin

  c_Gamma
    = pi^2 * M0 * (2636149 / 35799040000)

such that

  Q_Gamma(t) <= -c_Gamma

for every t>=18.

This closes the absolute Gamma-scale producer G_abs on the literal gammaConeValue
consumer.  No asymptotic notation and no new representation bridge is used.
-/

noncomputable section

open scoped Real

namespace Synthesis

def canonicalGammaConeAbsoluteMargin : ℝ :=
  Real.pi ^ 2 * unitBumpMass0
    * (2636149 / 35799040000 : ℝ)

theorem canonicalGammaConeAbsoluteMargin_pos :
    0 < canonicalGammaConeAbsoluteMargin := by
  unfold canonicalGammaConeAbsoluteMargin
  have hm : 0 < unitBumpMass0 := unitBumpMass0_pos
  positivity

theorem canonicalGammaProduct_absolute_lower
    {t : ℝ} (ht : 18 <= t) :
    canonicalGammaConeAbsoluteMargin
      <=
    2 * ((-quantitativeInnerPole t)
      * canonicalGammaRatioGap t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hp :
      quantitativeTaperR t * unitBumpMass0
        <= -quantitativeInnerPole t :=
    quantitativeInnerPole_abs_lower ht
  have hg :
      canonicalGammaGapLinearConstant * t
        <= canonicalGammaRatioGap t :=
    canonicalGammaRatioGap_linear_lower ht
  have hp0 :
      0 <= quantitativeTaperR t * unitBumpMass0 := by
    exact mul_nonneg (quantitativeTaperR_pos ht0).le
      unitBumpMass0_nonneg
  have hg0 :
      0 <= canonicalGammaGapLinearConstant * t := by
    exact mul_nonneg canonicalGammaGapLinearConstant_pos.le ht0.le
  have hpR : 0 <= -quantitativeInnerPole t := by
    linarith [quantitativeInnerPole_neg ht]
  have hgR : 0 <= canonicalGammaRatioGap t :=
    canonicalGammaRatioGap_nonneg ht
  have hprod :
      (quantitativeTaperR t * unitBumpMass0)
          * (canonicalGammaGapLinearConstant * t)
        <=
      (-quantitativeInnerPole t)
          * canonicalGammaRatioGap t := by
    exact mul_le_mul hp hg hg0 hpR
  have hscaled :
      2 * ((quantitativeTaperR t * unitBumpMass0)
          * (canonicalGammaGapLinearConstant * t))
        <=
      2 * ((-quantitativeInnerPole t)
          * canonicalGammaRatioGap t) := by
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  have heq :
      2 * ((quantitativeTaperR t * unitBumpMass0)
          * (canonicalGammaGapLinearConstant * t))
        =
      canonicalGammaConeAbsoluteMargin := by
    unfold quantitativeTaperR canonicalGammaGapLinearConstant
      canonicalGammaConeAbsoluteMargin
    field_simp [ne_of_gt ht0]
    ring
  rw [heq] at hscaled
  exact hscaled

theorem quantitativeCanonicalGammaCone_uniform_deficit
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (gammaVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      <=
    - canonicalGammaConeAbsoluteMargin := by
  have hcone := quantitativeCanonicalGammaCone_deficit ht
  have hmargin := canonicalGammaProduct_absolute_lower ht
  linarith

theorem quantitativeCanonicalGammaCone_uniform_neg
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (gammaVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      < 0 := by
  have h := quantitativeCanonicalGammaCone_uniform_deficit ht
  have hc := canonicalGammaConeAbsoluteMargin_pos
  linarith

end Synthesis
