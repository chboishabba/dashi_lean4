import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleRobustness
import Synthesis.RiemannProjectiveQuarticFourWindowPoleLocalization
import Synthesis.RiemannProjectiveQuarticFourWindowRobustness

/-!
# Smooth signed pole-cancellation transversality

The atomic/corridor endpoint determinant has the uniform positive margin

  P_{2/3} S_{1/2} - P_{1/2} S_{2/3} >= 7*pi^4/800.

Both the finite pole coordinate and J4 converge uniformly from the smooth
four-window family to their atomic counterparts as R -> 0+.  Therefore, for
each fixed t>=200, sufficiently narrow endpoint profiles retain a strictly
positive signed pole-cancelled target determinant.

This is the actual smooth transversality needed by a signed two-detector
orthogonalization lane.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticFourSmoothTargetStrength
    (R lam mu : ℝ) : ℝ :=
  - quarticFourWindowJ R lam mu 4

def quarticFourSmoothPoleCancelledTarget
    (R muHalf muTwoThirds t : ℝ) : ℝ :=
  quarticFourSmoothFinitePoleResidual R (2/3) muTwoThirds t
      * quarticFourSmoothTargetStrength R (1/2) muHalf
    -
  quarticFourSmoothFinitePoleResidual R (1/2) muHalf t
      * quarticFourSmoothTargetStrength R (2/3) muTwoThirds

theorem quarticFourAtomicTargetStrengthAt_half_le
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicTargetStrengthAt (1/2) mu
      <= Real.pi^4 / 30 := by
  have hdiff :=
    quarticFourAtomicJ4_mu_difference (1/2) mu
  have habs :
      |mu-quarticFourAtomicMu (1/2)|
        <= (1/10000 : ℝ) := by
    simpa [quarticFourAtomicMuRadius] using hmu
  have hdeltaHi :
      mu-quarticFourAtomicMu (1/2)
        <= (1/10000 : ℝ) := (abs_le.mp habs).2
  have hbase := quarticFourAtomicTargetStrength_half
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
  rw [show
      quarticFourAtomicJAt (1/2)
          (quarticFourAtomicMu (1/2)) 4
        = -(73*Real.pi^4/2808) by
      unfold quarticFourAtomicTargetStrength at hbase
      linarith]
  have hp : 0 < Real.pi^4 := by positivity
  nlinarith

theorem quarticFourAtomicTargetStrengthAt_twoThirds_pos
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    0 < quarticFourAtomicTargetStrengthAt (2/3) mu := by
  unfold quarticFourAtomicTargetStrengthAt
  exact neg_pos.mpr
    (quarticFourAtomicJ4_neg_in_corridor
      (by norm_num) (by norm_num) hmu)

theorem quarticFourAtomicFinitePole_twoThirds_le_five_halves
    {t mu : ℝ}
    (ht : 200 <= t)
    (hmu : |mu| <= 1/10) :
    quarticFourAtomicFinitePoleResidual t (2/3) mu <= 5/2 := by
  have htpos : 0 < t := by linarith
  have h3ex :=
    quarticFour_cosh_excess_le_one_of_twoHundred ht
  have h3lo : 1 <= Real.cosh (8*Real.pi/t) := Real.one_le_cosh _
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
  have h1lo : 1 <= Real.cosh (8*Real.pi/(3*t)) := Real.one_le_cosh _
  have h2lo : 1 <= Real.cosh (4*Real.pi/t) := Real.one_le_cosh _
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
  have hmuHi : mu <= 1/10 := (abs_le.mp hmu).2
  unfold quarticFourAtomicFinitePoleResidual
  norm_num
  nlinarith

theorem exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwoThirds : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwoThirds-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        7 * Real.pi^4 / 1600 <=
          quarticFourSmoothPoleCancelledTarget
            R muHalf muTwoThirds t := by
  let margin : ℝ := 7 * Real.pi^4 / 800
  let M : ℝ := 10 + Real.pi^4
  let eta : ℝ := min 1 (margin / (2*(4*M+2)))
  have hmargin : 0 < margin := by
    dsimp [margin]
    positivity
  have hM : 0 <= M := by
    dsimp [M]
    positivity
  have hden : 0 < 2*(4*M+2) := by
    dsimp [M]
    positivity
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hmargin hden)
  have heta1 : eta <= 1 := min_le_left _ _

  obtain ⟨dPole,hdPole,hPole⟩ :=
    exists_radius_quarticFourSmoothPole_close_atomic ht heta
  obtain ⟨dJ4,hdJ4,hJ4⟩ :=
    exists_radius_quarticFourWindowJ4_close_atomic heta
  let delta := min dPole dJ4
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdPole hdJ4
  refine ⟨delta,hdelta,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo

  have hRP : R < dPole := hRd.trans_le (min_le_left _ _)
  have hRJ : R < dJ4 := hRd.trans_le (min_le_right _ _)
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩

  have eP2 :=
    hPole R (2/3) muTwo hR hRP hlamTwo hmuTwoAbs.le
  have eP1 :=
    hPole R (1/2) muHalf hR hRP hlamHalf hmuHalfAbs.le
  have eJ1 :=
    hJ4 R (1/2) muHalf hR hRJ hlamHalf hmuHalfAbs.le
  have eJ2 :=
    hJ4 R (2/3) muTwo hR hRJ hlamTwo hmuTwoAbs.le

  have eS1 :
      |quarticFourSmoothTargetStrength R (1/2) muHalf
        - quarticFourAtomicTargetStrengthAt (1/2) muHalf|
        <= eta := by
    unfold quarticFourSmoothTargetStrength
      quarticFourAtomicTargetStrengthAt
    simpa [abs_neg] using eJ1
  have eS2 :
      |quarticFourSmoothTargetStrength R (2/3) muTwo
        - quarticFourAtomicTargetStrengthAt (2/3) muTwo|
        <= eta := by
    unfold quarticFourSmoothTargetStrength
      quarticFourAtomicTargetStrengthAt
    simpa [abs_neg] using eJ2

  have hP1lo :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamHalf hmuHalfAbs.le
  have hP2lo :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamTwo hmuTwoAbs.le
  have hP1hi :=
    quarticFourAtomicFinitePole_half_le_five_halves
      ht hmuHalfAbs.le
  have hP2hi :=
    quarticFourAtomicFinitePole_twoThirds_le_five_halves
      ht hmuTwoAbs.le
  have hS1lo := quarticFourAtomicTargetStrengthAt_half_ge hmuHalf
  have hS1hi := quarticFourAtomicTargetStrengthAt_half_le hmuHalf
  have hS2lo := quarticFourAtomicTargetStrengthAt_twoThirds_pos hmuTwo
  have hS2hi := quarticFourAtomicTargetStrengthAt_twoThirds_le hmuTwo

  have hp4 : 0 < Real.pi^4 := by positivity
  have a0 :
      |quarticFourAtomicFinitePoleResidual t (2/3) muTwo| <= M := by
    rw [abs_of_nonneg (by linarith : 0 <=
      quarticFourAtomicFinitePoleResidual t (2/3) muTwo)]
    dsimp [M]
    linarith
  have b0 :
      |quarticFourAtomicTargetStrengthAt (1/2) muHalf| <= M := by
    rw [abs_of_nonneg (by linarith : 0 <=
      quarticFourAtomicTargetStrengthAt (1/2) muHalf)]
    dsimp [M]
    nlinarith
  have c0 :
      |quarticFourAtomicFinitePoleResidual t (1/2) muHalf| <= M := by
    rw [abs_of_nonneg (by linarith : 0 <=
      quarticFourAtomicFinitePoleResidual t (1/2) muHalf)]
    dsimp [M]
    linarith
  have d0 :
      |quarticFourAtomicTargetStrengthAt (2/3) muTwo| <= M := by
    rw [abs_of_pos hS2lo]
    dsimp [M]
    nlinarith

  have hdetErr :=
    abs_det_sub_det_le hM heta.le heta1
      a0 b0 c0 d0 eP2 eS1 eP1 eS2
  have hatom :=
    quarticFourAtomicFinitePoleCancelledTarget_ge_margin
      ht hmuHalf hmuTwo

  have herr :
      |quarticFourSmoothPoleCancelledTarget R muHalf muTwo t
        - quarticFourAtomicFinitePoleCancelledTarget t muHalf muTwo|
        <= margin/2 := by
    unfold quarticFourSmoothPoleCancelledTarget
      quarticFourAtomicFinitePoleCancelledTarget at hdetErr ⊢
    calc
      |quarticFourSmoothFinitePoleResidual R (2/3) muTwo t
          * quarticFourSmoothTargetStrength R (1/2) muHalf
        - quarticFourSmoothFinitePoleResidual R (1/2) muHalf t
          * quarticFourSmoothTargetStrength R (2/3) muTwo
        -
        (quarticFourAtomicFinitePoleResidual t (2/3) muTwo
          * quarticFourAtomicTargetStrengthAt (1/2) muHalf
        - quarticFourAtomicFinitePoleResidual t (1/2) muHalf
          * quarticFourAtomicTargetStrengthAt (2/3) muTwo)|
        <= (4*M+2)*eta := hdetErr
      _ <= margin/2 := by
        have hetaRight :
            eta <= margin/(2*(4*M+2)) := min_le_right _ _
        have hcoef : 0 <= 4*M+2 := by positivity
        have hm := mul_le_mul_of_nonneg_left hetaRight hcoef
        field_simp [ne_of_gt (by positivity : 0 < 4*M+2)] at hm ⊢
        nlinarith

  have hlo := (abs_le.mp herr).1
  unfold margin at *
  nlinarith [Real.pi_pos]

theorem exists_radius_quarticFourSmooth_signedPoleTarget_pos
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwoThirds : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwoThirds-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        0 < quarticFourSmoothPoleCancelledTarget
          R muHalf muTwoThirds t := by
  obtain ⟨delta,hdelta,hmargin⟩ :=
    exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin ht
  refine ⟨delta,hdelta,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo
  have h :=
    hmargin R muHalf muTwo hR hRd hmuHalf hmuTwo
  have hp : 0 < Real.pi^4 := by positivity
  nlinarith

end Synthesis
