import Synthesis.RiemannProjectiveQuarticAtomicFamily

/-!
# Four-window atomic quartic family with one free parameter after J2 cancellation

Use the four normalized atomic radii

  0, pi/3, pi/2, pi

with signed weights

  1, -1, lambda, mu.

The projective moments are

  J2(lambda,mu)
    = -pi^2 (54 lambda mu + 13 lambda - 144 mu - 8) / 72,

  J4(lambda,mu)
    = -pi^4 (2430 lambda mu + 97 lambda - 5184 mu - 32) / 2592.

Hence J2=0 is solved explicitly by

  mu(lambda) = (13 lambda - 8)/(144 - 54 lambda).

Along this exact J2-null curve,

  J4
    = pi^4 (lambda-2)(183 lambda-128)
        / (324(3 lambda-8)).

In particular J4<0 throughout 1/2 <= lambda <= 2/3.  Thus the fourth
window leaves one genuine real parameter free after exact quadratic-moment
cancellation.  This is the finite-dimensional degree of freedom intended for
the remaining signed N-mu functional.
-/

noncomputable section

open scoped Real

namespace Synthesis

def quarticFourAtomicRespAt (lam mu s : ℝ) : ℝ :=
  Real.cos (s * 0)
    - Real.cos (s * (Real.pi/3))
    + lam * Real.cos (s * (Real.pi/2))
    + mu * Real.cos (s * Real.pi)

def quarticFourAtomicMomentRespAt
    (lam mu : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  0^k * Real.cos (s*0)
    - (Real.pi/3)^k * Real.cos (s*(Real.pi/3))
    + lam * (Real.pi/2)^k * Real.cos (s*(Real.pi/2))
    + mu * Real.pi^k * Real.cos (s*Real.pi)

def quarticFourAtomicJAt
    (lam mu : ℝ) (k : ℕ) : ℝ :=
  quarticFourAtomicRespAt lam mu 1
      * quarticFourAtomicMomentRespAt lam mu k 2
    -
  quarticFourAtomicRespAt lam mu 2
      * quarticFourAtomicMomentRespAt lam mu k 1

private theorem four_atomic_cos_values :
    Real.cos (Real.pi/3) = 1/2
      ∧ Real.cos (Real.pi/2) = 0
      ∧ Real.cos Real.pi = -1
      ∧ Real.cos (2*(Real.pi/3)) = -1/2
      ∧ Real.cos (2*(Real.pi/2)) = -1
      ∧ Real.cos (2*Real.pi) = 1 := by
  constructor
  · simpa using Real.cos_pi_div_three
  constructor
  · simpa using Real.cos_pi_div_two
  constructor
  · exact Real.cos_pi
  constructor
  · have harg : 2*(Real.pi/3) = Real.pi - Real.pi/3 := by ring
    rw [harg, Real.cos_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_three]
    norm_num
  constructor
  · have harg : 2*(Real.pi/2) = Real.pi := by ring
    rw [harg, Real.cos_pi]
  · have harg : 2*Real.pi = Real.pi + Real.pi := by ring
    rw [harg, Real.cos_add, Real.cos_pi, Real.sin_pi]
    norm_num

theorem quarticFourAtomicJAt_two_formula
    (lam mu : ℝ) :
    quarticFourAtomicJAt lam mu 2
      =
    -(Real.pi^2 *
      (54*lam*mu + 13*lam - 144*mu - 8) / 72) := by
  rcases four_atomic_cos_values with
    ⟨hc1,hc2,hcp,h2c1,h2c2,h2cp⟩
  unfold quarticFourAtomicJAt quarticFourAtomicRespAt
    quarticFourAtomicMomentRespAt
  simp only [one_mul, mul_zero, Real.cos_zero,
    zero_pow (by norm_num : 2 ≠ 0)]
  rw [hc1,hc2,hcp,h2c1,h2c2,h2cp]
  ring

theorem quarticFourAtomicJAt_four_formula
    (lam mu : ℝ) :
    quarticFourAtomicJAt lam mu 4
      =
    -(Real.pi^4 *
      (2430*lam*mu + 97*lam - 5184*mu - 32) / 2592) := by
  rcases four_atomic_cos_values with
    ⟨hc1,hc2,hcp,h2c1,h2c2,h2cp⟩
  unfold quarticFourAtomicJAt quarticFourAtomicRespAt
    quarticFourAtomicMomentRespAt
  simp only [one_mul, mul_zero, Real.cos_zero,
    zero_pow (by norm_num : 4 ≠ 0)]
  rw [hc1,hc2,hcp,h2c1,h2c2,h2cp]
  ring

def quarticFourAtomicMu (lam : ℝ) : ℝ :=
  (13*lam - 8) / (144 - 54*lam)

theorem quarticFourAtomicMu_den_pos
    {lam : ℝ} (hlam : lam <= 2/3) :
    0 < 144 - 54*lam := by
  linarith

theorem quarticFourAtomicJ2_null
    {lam : ℝ} (hlam : lam <= 2/3) :
    quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 2 = 0 := by
  rw [quarticFourAtomicJAt_two_formula]
  unfold quarticFourAtomicMu
  have hden : 144 - 54*lam ≠ 0 :=
    ne_of_gt (quarticFourAtomicMu_den_pos hlam)
  field_simp [hden]
  ring

theorem quarticFourAtomicJ4_on_null_formula
    {lam : ℝ} (hlam : lam <= 2/3) :
    quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4
      =
    Real.pi^4 * (lam-2) * (183*lam-128)
      / (324*(3*lam-8)) := by
  rw [quarticFourAtomicJAt_four_formula]
  unfold quarticFourAtomicMu
  have hden : 144 - 54*lam ≠ 0 :=
    ne_of_gt (quarticFourAtomicMu_den_pos hlam)
  field_simp [hden]
  ring

theorem quarticFourAtomicJ4_neg_on_half_twoThirds
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4 < 0 := by
  rw [quarticFourAtomicJ4_on_null_formula hlam2]
  have hpi : 0 < Real.pi^4 := by positivity
  have h1 : lam - 2 < 0 := by linarith
  have h2 : 183*lam - 128 < 0 := by
    nlinarith
  have h3 : 3*lam - 8 < 0 := by
    linarith
  have hnum :
      0 < Real.pi^4 * (lam-2) * (183*lam-128) := by
    exact mul_pos hpi (mul_pos_of_neg_of_neg h1 h2)
  have hden : 324*(3*lam-8) < 0 := by
    nlinarith
  exact div_neg_of_pos_of_neg hnum hden

theorem quarticFourAtomicMu_small_on_half_twoThirds
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    |quarticFourAtomicMu lam| <= 1/50 := by
  unfold quarticFourAtomicMu
  have hden := quarticFourAtomicMu_den_pos hlam2
  rw [abs_div, abs_of_pos hden, abs_le]
  constructor
  · rw [neg_le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith

end Synthesis
