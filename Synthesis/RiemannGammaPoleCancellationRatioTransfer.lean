import Synthesis.RiemannGammaToPoleRatioMonotonicity

/-!
# Pole-cancellation transfers ratio separation into Gamma sign

This is the scalar algebra behind the canonical paired-window argument.

Let

  P_in  < 0 < P_out

be the selected-radius pole masses of the identical inner/outer bumps, and let

  lambda = - P_in / P_out

so that

  P_in + lambda * P_out = 0.

Suppose the corresponding centered-Gamma masses factor through the same pole
masses with positive ratios

  G_in  = R_in  * P_in,
  G_out = R_out * P_out,

and the outer ratio is strictly larger:

  R_in < R_out.

Then the same pole-killing coefficient forces

  0 < G_in + lambda * G_out.

Since the literal centered Gamma cone uses the opposite sign,

  Q_Gamma = -2 * (G_in + lambda * G_out),

we obtain Q_Gamma < 0.

The theorem is deliberately algebraic: the remaining analytic task is to
instantiate the factorisations from the identical affine bump and the
source-written Gamma-to-pole ratio monotonicity.
-/

noncomputable section

namespace Synthesis

theorem poleCancellation_ratioSeparation_gamma_pos
    {P_in P_out G_in G_out R_in R_out lam : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin : G_in = R_in * P_in)
    (hGout : G_out = R_out * P_out)
    (hRatio : R_in < R_out) :
    0 < G_in + lam * G_out := by
  have hlam :
      lam * P_out = -P_in := by
    linarith
  rw [hGin, hGout]
  calc
    0 < P_in * (R_in - R_out) := by
      exact mul_pos_of_neg_of_neg hPin (sub_neg.mpr hRatio)
    _ = R_in * P_in + lam * (R_out * P_out) := by
      rw [mul_assoc, show lam * P_out = -P_in from hlam]
      ring

theorem poleCancellation_ratioSeparation_gammaCone_neg
    {P_in P_out G_in G_out R_in R_out lam QGamma : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin : G_in = R_in * P_in)
    (hGout : G_out = R_out * P_out)
    (hRatio : R_in < R_out)
    (hQ : QGamma = -2 * (G_in + lam * G_out)) :
    QGamma < 0 := by
  have hG :=
    poleCancellation_ratioSeparation_gamma_pos
      hPin hPout hcancel hGin hGout hRatio
  rw [hQ]
  nlinarith

/--
Quantitative version.  If the ratio gap is at least d>0, then the paired Gamma
response gains at least (-P_in)*d.
-/
theorem poleCancellation_ratioGap_gamma_lower
    {P_in P_out G_in G_out R_in R_out lam d : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin : G_in = R_in * P_in)
    (hGout : G_out = R_out * P_out)
    (hd : 0 <= d)
    (hGap : d <= R_out - R_in) :
    (-P_in) * d <= G_in + lam * G_out := by
  have hlam :
      lam * P_out = -P_in := by
    linarith
  rw [hGin, hGout]
  have hPinNeg : 0 <= -P_in := by linarith
  have hmul :
      (-P_in) * d <= (-P_in) * (R_out - R_in) :=
    mul_le_mul_of_nonneg_left hGap hPinNeg
  calc
    (-P_in) * d
        <= (-P_in) * (R_out - R_in) := hmul
    _ = R_in * P_in + lam * (R_out * P_out) := by
      rw [mul_assoc, show lam * P_out = -P_in from hlam]
      ring

theorem poleCancellation_ratioGap_gammaCone_upper
    {P_in P_out G_in G_out R_in R_out lam d QGamma : ℝ}
    (hPin : P_in < 0)
    (hPout : 0 < P_out)
    (hcancel : P_in + lam * P_out = 0)
    (hGin : G_in = R_in * P_in)
    (hGout : G_out = R_out * P_out)
    (hd : 0 <= d)
    (hGap : d <= R_out - R_in)
    (hQ : QGamma = -2 * (G_in + lam * G_out)) :
    QGamma <= -2 * ((-P_in) * d) := by
  have hG :=
    poleCancellation_ratioGap_gamma_lower
      hPin hPout hcancel hGin hGout hd hGap
  rw [hQ]
  nlinarith

end Synthesis
