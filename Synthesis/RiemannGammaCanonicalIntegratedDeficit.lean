import Synthesis.RiemannGammaCanonicalRatioGap
import Synthesis.RiemannGammaPoleCancellationRatioTransfer

/-!
# Canonical integrated Gamma deficit from endpoint ratio bounds

The full matched-coordinate change of variables is not needed.

Let P_in < 0 < P_out be the selected-radius pole masses and let
lambda kill the pole:

    P_in + lambda * P_out = 0.

Suppose the corresponding Gamma kernel masses satisfy the endpoint-integrated
bounds

    R5 * P_in <= G_in,
    R7 * P_out <= G_out,

where

    R5 = R_t(5*pi/(4t)),
    R7 = R_t(7*pi/(4t)).

Because P_in is negative, the inner upper endpoint for the ratio gives a lower
bound on G_in.  Because P_out is positive, the outer lower endpoint gives a
lower bound on G_out.

Therefore

    (-P_in) * (R7-R5) <= G_in + lambda*G_out.

The parenthesized factor is exactly canonicalGammaRatioGap t.
-/

noncomputable section

open scoped Real

namespace Synthesis

def canonicalInnerRatioEndpoint (t : ℝ) : ℝ :=
  gammaToPoleRatio t (5 * Real.pi / (4*t))

def canonicalOuterRatioEndpoint (t : ℝ) : ℝ :=
  gammaToPoleRatio t (7 * Real.pi / (4*t))

theorem canonicalRatioGap_eq_endpoints (t : ℝ) :
    canonicalGammaRatioGap t
      = canonicalOuterRatioEndpoint t - canonicalInnerRatioEndpoint t := by
  rfl

theorem canonicalIntegratedGammaDeficit
    {t P_in P_out G_in G_out lam : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin :
      canonicalInnerRatioEndpoint t * P_in <= G_in)
    (hGout :
      canonicalOuterRatioEndpoint t * P_out <= G_out) :
    (-P_in) * canonicalGammaRatioGap t
      <= G_in + lam * G_out := by
  have hlam : lam * P_out = -P_in := by
    linarith
  have hlam0 : 0 < lam := by
    have : lam = -P_in / P_out := by
      apply (eq_div_iff hPout.ne').2
      linarith
    rw [this]
    positivity
  have hGoutScaled :
      lam * (canonicalOuterRatioEndpoint t * P_out)
        <= lam * G_out :=
    mul_le_mul_of_nonneg_left hGout hlam0.le
  rw [mul_assoc, hlam] at hGoutScaled
  rw [canonicalRatioGap_eq_endpoints]
  nlinarith

theorem canonicalIntegratedGammaConeUpper
    {t P_in P_out G_in G_out lam QGamma : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin :
      canonicalInnerRatioEndpoint t * P_in <= G_in)
    (hGout :
      canonicalOuterRatioEndpoint t * P_out <= G_out)
    (hQ : QGamma = -2 * (G_in + lam * G_out)) :
    QGamma
      <= -2 * ((-P_in) * canonicalGammaRatioGap t) := by
  have h :=
    canonicalIntegratedGammaDeficit
      hPin hPout hcancel hGin hGout
  rw [hQ]
  nlinarith

theorem canonicalIntegratedGammaCone_neg
    {t P_in P_out G_in G_out lam QGamma : ℝ}
    (ht : 18 <= t)
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin :
      canonicalInnerRatioEndpoint t * P_in <= G_in)
    (hGout :
      canonicalOuterRatioEndpoint t * P_out <= G_out)
    (hQ : QGamma = -2 * (G_in + lam * G_out)) :
    QGamma < 0 := by
  have hupper :=
    canonicalIntegratedGammaConeUpper
      hPin hPout hcancel hGin hGout hQ
  have hgap := canonicalGammaRatioGap_pos ht
  have hmass : 0 < (-P_in) * canonicalGammaRatioGap t := by
    exact mul_pos (by linarith) hgap
  linarith

end Synthesis
