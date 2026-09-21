import Synthesis.RiemannProjectiveQuarticFourWindowAtomic

/-!
# Uniform atomic corridor around the four-window J2-null manifold

Let

  mu0(lambda) = (13 lambda - 8)/(144 - 54 lambda)

and fix the tiny radius

  d = 1/10000.

For lambda in [1/2,2/3]:

* |mu0| <= 1/50, hence mu0+-d remains inside |mu|<1/10;
* J2(lambda,mu0-d) < 0 < J2(lambda,mu0+d), uniformly;
* J4 stays strictly negative throughout |mu-mu0|<=d.

These robust atomic margins are the IVT input for the smooth four-window lift.
-/

noncomputable section

open scoped Real

namespace Synthesis

def quarticFourAtomicMuRadius : ℝ := 1/10000

theorem quarticFourAtomicMuRadius_pos :
    0 < quarticFourAtomicMuRadius := by
  norm_num [quarticFourAtomicMuRadius]

theorem quarticFourAtomicMu_corridor_abs_lt_tenth
    {lam mu : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3)
    (hmu :
      |mu - quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius) :
    |mu| < 1/10 := by
  have h0 :=
    quarticFourAtomicMu_small_on_half_twoThirds hlam1 hlam2
  have htri :
      |mu| <= |mu-quarticFourAtomicMu lam|
        + |quarticFourAtomicMu lam| := by
    have := abs_add (mu-quarticFourAtomicMu lam)
      (quarticFourAtomicMu lam)
    simpa [sub_add_cancel] using this
  have hd : quarticFourAtomicMuRadius = (1/10000 : ℝ) := rfl
  rw [hd] at hmu
  nlinarith

theorem quarticFourAtomicJ2_at_mu_add_radius_pos
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    0 <
    quarticFourAtomicJAt lam
      (quarticFourAtomicMu lam + quarticFourAtomicMuRadius) 2 := by
  rw [quarticFourAtomicJAt_two_formula]
  unfold quarticFourAtomicMu quarticFourAtomicMuRadius
  have hden : 0 < 144-54*lam :=
    quarticFourAtomicMu_den_pos hlam2
  have hden0 : 144-54*lam ≠ 0 := ne_of_gt hden
  field_simp [hden0]
  have hpi : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticFourAtomicJ2_at_mu_sub_radius_neg
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    quarticFourAtomicJAt lam
      (quarticFourAtomicMu lam - quarticFourAtomicMuRadius) 2 < 0 := by
  rw [quarticFourAtomicJAt_two_formula]
  unfold quarticFourAtomicMu quarticFourAtomicMuRadius
  have hden : 0 < 144-54*lam :=
    quarticFourAtomicMu_den_pos hlam2
  have hden0 : 144-54*lam ≠ 0 := ne_of_gt hden
  field_simp [hden0]
  have hpi : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticFourAtomicJ4_null_le_uniform
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4
      <= -(Real.pi^4/243) := by
  rw [quarticFourAtomicJ4_on_null_formula hlam2]
  have hp : 0 < Real.pi^4 := by positivity
  have hd : 3*lam-8 < 0 := by linarith
  rw [le_div_iff_of_neg (by nlinarith : 324*(3*lam-8) < 0)]
  have hfactor1 : 3*lam-2 <= 0 := by linarith
  have hfactor2 : 183*lam-368 < 0 := by nlinarith
  have hprod : 0 <= (3*lam-2)*(183*lam-368) :=
    mul_nonneg_of_nonpos_of_nonpos hfactor1 hfactor2.le
  nlinarith

theorem quarticFourAtomicJ4_mu_difference
    (lam mu : ℝ) :
    quarticFourAtomicJAt lam mu 4
      - quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4
      =
    Real.pi^4 * ((32-15*lam)/16)
      * (mu-quarticFourAtomicMu lam) := by
  rw [quarticFourAtomicJAt_four_formula,
      quarticFourAtomicJAt_four_formula]
  ring

theorem quarticFourAtomicJ4_neg_in_corridor
    {lam mu : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3)
    (hmu :
      |mu-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicJAt lam mu 4 < 0 := by
  have hnull :=
    quarticFourAtomicJ4_null_le_uniform hlam1 hlam2
  have hdiff :=
    quarticFourAtomicJ4_mu_difference lam mu
  have hcoef0 : 0 < (32-15*lam)/16 := by
    nlinarith
  have hcoefUpper : (32-15*lam)/16 <= 49/32 := by
    nlinarith
  have hp : 0 < Real.pi^4 := by positivity
  have habsDiff :
      |quarticFourAtomicJAt lam mu 4
        - quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4|
      <=
      Real.pi^4 * (49/32)
        * quarticFourAtomicMuRadius := by
    rw [hdiff, abs_mul, abs_mul,
      abs_of_pos hp, abs_of_pos hcoef0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hcoefUpper hmu (abs_nonneg _)
        hcoef0.le)
      hp.le
  have hsmall :
      Real.pi^4 * (49/32) * quarticFourAtomicMuRadius
        < Real.pi^4/243 := by
    unfold quarticFourAtomicMuRadius
    have hp0 : 0 < Real.pi^4 := by positivity
    nlinarith
  have hupper :=
    (abs_le.mp habsDiff).2
  linarith


def quarticFourAtomicJ2CorridorMargin : ℝ := 1/1000

theorem quarticFourAtomicJ2CorridorMargin_pos :
    0 < quarticFourAtomicJ2CorridorMargin := by
  norm_num [quarticFourAtomicJ2CorridorMargin]

theorem quarticFourAtomicJ2_add_radius_ge_margin
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    quarticFourAtomicJ2CorridorMargin
      <
    quarticFourAtomicJAt lam
      (quarticFourAtomicMu lam + quarticFourAtomicMuRadius) 2 := by
  rw [quarticFourAtomicJAt_two_formula]
  unfold quarticFourAtomicMu quarticFourAtomicMuRadius
    quarticFourAtomicJ2CorridorMargin
  have hden : 0 < 144-54*lam :=
    quarticFourAtomicMu_den_pos hlam2
  have hden0 : 144-54*lam ≠ 0 := ne_of_gt hden
  field_simp [hden0]
  have hpi2 : 9 < Real.pi^2 := by
    nlinarith [Real.pi_gt_three]
  nlinarith

theorem quarticFourAtomicJ2_sub_radius_le_neg_margin
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    quarticFourAtomicJAt lam
      (quarticFourAtomicMu lam - quarticFourAtomicMuRadius) 2
      <
    -quarticFourAtomicJ2CorridorMargin := by
  rw [quarticFourAtomicJAt_two_formula]
  unfold quarticFourAtomicMu quarticFourAtomicMuRadius
    quarticFourAtomicJ2CorridorMargin
  have hden : 0 < 144-54*lam :=
    quarticFourAtomicMu_den_pos hlam2
  have hden0 : 144-54*lam ≠ 0 := ne_of_gt hden
  field_simp [hden0]
  have hpi2 : 9 < Real.pi^2 := by
    nlinarith [Real.pi_gt_three]
  nlinarith

def quarticFourAtomicJ4CorridorMargin : ℝ :=
  Real.pi^4 / 300

theorem quarticFourAtomicJ4CorridorMargin_pos :
    0 < quarticFourAtomicJ4CorridorMargin := by
  unfold quarticFourAtomicJ4CorridorMargin
  positivity

theorem quarticFourAtomicJ4_le_neg_corridorMargin
    {lam mu : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3)
    (hmu :
      |mu-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicJAt lam mu 4
      <
    -quarticFourAtomicJ4CorridorMargin := by
  have hnull :=
    quarticFourAtomicJ4_null_le_uniform hlam1 hlam2
  have hdiff :=
    quarticFourAtomicJ4_mu_difference lam mu
  have hcoef0 : 0 < (32-15*lam)/16 := by
    nlinarith
  have hcoefUpper : (32-15*lam)/16 <= 49/32 := by
    nlinarith
  have hp : 0 < Real.pi^4 := by positivity
  have habsDiff :
      |quarticFourAtomicJAt lam mu 4
        - quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4|
      <=
      Real.pi^4 * (49/32)
        * quarticFourAtomicMuRadius := by
    rw [hdiff, abs_mul, abs_mul,
      abs_of_pos hp, abs_of_pos hcoef0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hcoefUpper hmu (abs_nonneg _)
        hcoef0.le)
      hp.le
  have hsmall :
      Real.pi^4 * (49/32) * quarticFourAtomicMuRadius
        < Real.pi^4 * (1/243 - 1/300) := by
    unfold quarticFourAtomicMuRadius
    have hp0 : 0 < Real.pi^4 := by positivity
    nlinarith
  have hupper := (abs_le.mp habsDiff).2
  unfold quarticFourAtomicJ4CorridorMargin
  linarith

end Synthesis
