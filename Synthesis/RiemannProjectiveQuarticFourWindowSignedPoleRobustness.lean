import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleGeometry
import Synthesis.RiemannProjectiveQuarticFourWindowAtomicCorridor

/-!
# Robust signed pole/target transversality on the four-window corridor

The exact endpoint transversality is not fragile.

Let S(lambda,mu) = -J4(lambda,mu).  On the atomic smooth-witness corridor

  |mu-mu0(lambda)| <= 1/10000,

the endpoint target strengths satisfy the deliberately coarse bounds

  S(1/2,mu) >= pi^4/40,
  S(2/3,mu) <= pi^4/200.

For t>=200 the finite atomic projective pole coordinate is positive everywhere.
At lambda=1/2 it also has the coarse upper bound 5/2, while at lambda=2/3
it has the already-proved lower bound 17/20.

Consequently the pole-cancelling signed target determinant has a uniform margin

  P_t(2/3,mu2) S(1/2,mu1)
    - P_t(1/2,mu1) S(2/3,mu2)
      >= 7*pi^4/800 > 0.

This is the quantitative margin needed to transport signed pole cancellation
from the atomic endpoints to sufficiently narrow smooth four-window witnesses.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticFourAtomicTargetStrengthAt
    (lam mu : ℝ) : ℝ :=
  - quarticFourAtomicJAt lam mu 4

theorem quarticFourAtomicTargetStrengthAt_half_ge
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    Real.pi^4 / 40
      <= quarticFourAtomicTargetStrengthAt (1/2) mu := by
  have hnull := quarticFourAtomicTargetStrength_half
  have hdiff :=
    quarticFourAtomicJ4_mu_difference (1/2) mu
  have hp : 0 < Real.pi^4 := by positivity
  have habs :
      |mu-quarticFourAtomicMu (1/2)|
        <= (1/10000 : ℝ) := by
    simpa [quarticFourAtomicMuRadius] using hmu
  unfold quarticFourAtomicTargetStrengthAt
  rw [show
      quarticFourAtomicJAt (1/2) mu 4
        =
      quarticFourAtomicJAt (1/2)
          (quarticFourAtomicMu (1/2)) 4
        + Real.pi^4 * (49/32) *
          (mu-quarticFourAtomicMu (1/2)) by
      have := hdiff
      norm_num at this ⊢
      linarith]
  have hdeltaLo :
      -(1/10000 : ℝ)
        <= mu-quarticFourAtomicMu (1/2) :=
    (abs_le.mp habs).1
  rw [show
      quarticFourAtomicJAt (1/2)
          (quarticFourAtomicMu (1/2)) 4
        = -(73*Real.pi^4/2808) by
      have hs := quarticFourAtomicTargetStrength_half
      unfold quarticFourAtomicTargetStrength at hs
      linarith]
  nlinarith

theorem quarticFourAtomicTargetStrengthAt_twoThirds_le
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicTargetStrengthAt (2/3) mu
      <= Real.pi^4 / 200 := by
  have hdiff :=
    quarticFourAtomicJ4_mu_difference (2/3) mu
  have hp : 0 < Real.pi^4 := by positivity
  have habs :
      |mu-quarticFourAtomicMu (2/3)|
        <= (1/10000 : ℝ) := by
    simpa [quarticFourAtomicMuRadius] using hmu
  have hdeltaLo :
      -(1/10000 : ℝ)
        <= mu-quarticFourAtomicMu (2/3) :=
    (abs_le.mp habs).1
  unfold quarticFourAtomicTargetStrengthAt
  rw [show
      quarticFourAtomicJAt (2/3) mu 4
        =
      quarticFourAtomicJAt (2/3)
          (quarticFourAtomicMu (2/3)) 4
        + Real.pi^4 * (11/8) *
          (mu-quarticFourAtomicMu (2/3)) by
      have := hdiff
      norm_num at this ⊢
      linarith]
  rw [show
      quarticFourAtomicJAt (2/3)
          (quarticFourAtomicMu (2/3)) 4
        = -(Real.pi^4/243) by
      have hs := quarticFourAtomicTargetStrength_twoThirds
      unfold quarticFourAtomicTargetStrength at hs
      linarith]
  nlinarith

theorem quarticFourAtomicFinitePole_half_le_five_halves
    {t mu : ℝ}
    (ht : 200 <= t)
    (hmu : |mu| <= 1/10) :
    quarticFourAtomicFinitePoleResidual t (1/2) mu <= 5/2 := by
  have htpos : 0 < t := by linarith
  have h3ex :=
    quarticFour_cosh_excess_le_one_of_twoHundred ht
  have h3lo : 1 <= Real.cosh (8*Real.pi/t) :=
    Real.one_le_cosh _
  have h3hi : Real.cosh (8*Real.pi/t) <= 2 := by linarith

  have hx1non : 0 <= 8*Real.pi/(3*t) := by positivity
  have hx2non : 0 <= 4*Real.pi/t := by positivity
  have hx3non : 0 <= 8*Real.pi/t := by positivity
  have hx1 :
      |8*Real.pi/(3*t)| <= |8*Real.pi/t| := by
    rw [abs_of_nonneg hx1non, abs_of_nonneg hx3non]
    field_simp [ne_of_gt htpos]
    nlinarith [Real.pi_pos]
  have hx2 :
      |4*Real.pi/t| <= |8*Real.pi/t| := by
    rw [abs_of_nonneg hx2non, abs_of_nonneg hx3non]
    field_simp [ne_of_gt htpos]
    nlinarith [Real.pi_pos]
  have h1hi :
      Real.cosh (8*Real.pi/(3*t)) <= 2 :=
    ((Real.cosh_le_cosh).2 hx1).trans h3hi
  have h2hi :
      Real.cosh (4*Real.pi/t) <= 2 :=
    ((Real.cosh_le_cosh).2 hx2).trans h3hi
  have h1lo : 1 <= Real.cosh (8*Real.pi/(3*t)) :=
    Real.one_le_cosh _
  have h2lo : 1 <= Real.cosh (4*Real.pi/t) :=
    Real.one_le_cosh _
  have hmuLo : -1/10 <= mu := (abs_le.mp hmu).1
  have hmuHi : mu <= 1/10 := (abs_le.mp hmu).2

  have hm2abs :
      |Real.cosh (4*Real.pi/t) * mu| <= 1/5 := by
    rw [abs_mul, abs_of_nonneg h2lo.le]
    exact mul_le_mul h2hi hmu (abs_nonneg mu) (by norm_num)
  have hm3abs :
      |Real.cosh (8*Real.pi/t) * mu| <= 1/5 := by
    rw [abs_mul, abs_of_nonneg h3lo.le]
    exact mul_le_mul h3hi hmu (abs_nonneg mu) (by norm_num)
  have hm2lo := (abs_le.mp hm2abs).1
  have hm3lo := (abs_le.mp hm3abs).1

  unfold quarticFourAtomicFinitePoleResidual
  norm_num
  nlinarith

def quarticFourAtomicFinitePoleCancelledTarget
    (t muHalf muTwoThirds : ℝ) : ℝ :=
  quarticFourAtomicFinitePoleResidual t (2/3) muTwoThirds
      * quarticFourAtomicTargetStrengthAt (1/2) muHalf
    -
  quarticFourAtomicFinitePoleResidual t (1/2) muHalf
      * quarticFourAtomicTargetStrengthAt (2/3) muTwoThirds

theorem quarticFourAtomicFinitePoleCancelledTarget_ge_margin
    {t muHalf muTwoThirds : ℝ}
    (ht : 200 <= t)
    (hmuHalf :
      |muHalf-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius)
    (hmuTwo :
      |muTwoThirds-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    7 * Real.pi^4 / 800
      <= quarticFourAtomicFinitePoleCancelledTarget
          t muHalf muTwoThirds := by
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwoThirds| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hp2 :
      17/20 <=
        quarticFourAtomicFinitePoleResidual
          t (2/3) muTwoThirds :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht ⟨by norm_num, by norm_num⟩ hmuTwoAbs.le
  have hp1 :
      quarticFourAtomicFinitePoleResidual
          t (1/2) muHalf <= 5/2 :=
    quarticFourAtomicFinitePole_half_le_five_halves
      ht hmuHalfAbs.le
  have hp1non :
      0 <= quarticFourAtomicFinitePoleResidual
          t (1/2) muHalf := by
    have h :=
      quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
        ht ⟨by norm_num, by norm_num⟩ hmuHalfAbs.le
    linarith
  have hS1 :=
    quarticFourAtomicTargetStrengthAt_half_ge hmuHalf
  have hS2 :=
    quarticFourAtomicTargetStrengthAt_twoThirds_le hmuTwo
  have hS1non : 0 <= quarticFourAtomicTargetStrengthAt (1/2) muHalf := by
    positivity
    linarith [hS1]
  have hp2S1 :
      (17/20 : ℝ) * (Real.pi^4/40)
        <=
      quarticFourAtomicFinitePoleResidual t (2/3) muTwoThirds
        * quarticFourAtomicTargetStrengthAt (1/2) muHalf := by
    exact mul_le_mul hp2 hS1
      (by positivity) (by linarith)
  have hp1S2 :
      quarticFourAtomicFinitePoleResidual t (1/2) muHalf
        * quarticFourAtomicTargetStrengthAt (2/3) muTwoThirds
        <=
      (5/2 : ℝ) * (Real.pi^4/200) := by
    exact mul_le_mul hp1 hS2
      (by positivity) hp1non
  unfold quarticFourAtomicFinitePoleCancelledTarget
  nlinarith [Real.pi_pos]

theorem quarticFourAtomicFinitePoleCancelledTarget_pos
    {t muHalf muTwoThirds : ℝ}
    (ht : 200 <= t)
    (hmuHalf :
      |muHalf-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius)
    (hmuTwo :
      |muTwoThirds-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    0 <
      quarticFourAtomicFinitePoleCancelledTarget
        t muHalf muTwoThirds := by
  have h :=
    quarticFourAtomicFinitePoleCancelledTarget_ge_margin
      ht hmuHalf hmuTwo
  have hp : 0 < Real.pi^4 := by positivity
  nlinarith

end Synthesis
