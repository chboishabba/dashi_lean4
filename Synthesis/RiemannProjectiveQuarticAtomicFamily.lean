import Synthesis.RiemannProjectiveQuarticAtomicCertificate

/-!
# One-parameter atomic quartic-escape family

Keep the three normalized radii

  0, pi/3, pi/2

and vary only the third signed weight:

  (1, -1, lambda).

For the atomic projective moments

  J_k(lambda)
    = A_lambda(1) M_{k,lambda}(2)
      - A_lambda(2) M_{k,lambda}(1),

the dependence is exactly affine in lambda:

  J_2(lambda) = -pi^2 (13 lambda - 8) / 72,
  J_4(lambda) = -pi^4 (97 lambda - 32) / 2592.

Hence J_2 changes sign between lambda=1/2 and lambda=3/4, while J_4 is
uniformly strictly negative on that whole interval.  This is the robust atomic
certificate used by the smooth three-window lift.
-/

noncomputable section

open scoped Real

namespace Synthesis

def quarticAtomicRespAt (lam s : ℝ) : ℝ :=
  Real.cos (s * 0)
    - Real.cos (s * (Real.pi / 3))
    + lam * Real.cos (s * (Real.pi / 2))

def quarticAtomicMomentRespAt (lam : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  0^k * Real.cos (s * 0)
    - (Real.pi / 3)^k * Real.cos (s * (Real.pi / 3))
    + lam * (Real.pi / 2)^k * Real.cos (s * (Real.pi / 2))

def quarticAtomicJAt (lam : ℝ) (k : ℕ) : ℝ :=
  quarticAtomicRespAt lam 1 * quarticAtomicMomentRespAt lam k 2
    - quarticAtomicRespAt lam 2 * quarticAtomicMomentRespAt lam k 1

private theorem atomic_cos_pi_thirds :
    Real.cos (Real.pi / 3) = 1/2
      ∧ Real.cos (Real.pi / 2) = 0
      ∧ Real.cos (2 * (Real.pi / 3)) = -1/2
      ∧ Real.cos (2 * (Real.pi / 2)) = -1 := by
  constructor
  · simpa using Real.cos_pi_div_three
  constructor
  · simpa using Real.cos_pi_div_two
  constructor
  · have harg : 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
    rw [harg, Real.cos_sub, Real.cos_pi, Real.sin_pi,
        Real.cos_pi_div_three]
    norm_num
  · have harg : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [harg, Real.cos_pi]

theorem quarticAtomicJAt_two_formula (lam : ℝ) :
    quarticAtomicJAt lam 2
      = -(Real.pi^2 * (13 * lam - 8) / 72) := by
  rcases atomic_cos_pi_thirds with ⟨hc1,hc2,h2c1,h2c2⟩
  unfold quarticAtomicJAt quarticAtomicRespAt quarticAtomicMomentRespAt
  simp only [one_mul, mul_zero, Real.cos_zero, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hc1, hc2, h2c1, h2c2]
  ring

theorem quarticAtomicJAt_four_formula (lam : ℝ) :
    quarticAtomicJAt lam 4
      = -(Real.pi^4 * (97 * lam - 32) / 2592) := by
  rcases atomic_cos_pi_thirds with ⟨hc1,hc2,h2c1,h2c2⟩
  unfold quarticAtomicJAt quarticAtomicRespAt quarticAtomicMomentRespAt
  simp only [one_mul, mul_zero, Real.cos_zero, zero_pow (by norm_num : 4 ≠ 0)]
  rw [hc1, hc2, h2c1, h2c2]
  ring

theorem quarticAtomicJAt_two_half_pos :
    0 < quarticAtomicJAt (1/2) 2 := by
  rw [quarticAtomicJAt_two_formula]
  have hp : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticAtomicJAt_two_three_quarters_neg :
    quarticAtomicJAt (3/4) 2 < 0 := by
  rw [quarticAtomicJAt_two_formula]
  have hp : 0 < Real.pi^2 := by positivity
  nlinarith

theorem quarticAtomicJAt_four_neg_of_half_le
    {lam : ℝ} (hlam : 1/2 ≤ lam) :
    quarticAtomicJAt lam 4 < 0 := by
  rw [quarticAtomicJAt_four_formula]
  have hp : 0 < Real.pi^4 := by positivity
  have hcoef : 0 < 97 * lam - 32 := by
    nlinarith
  positivity

theorem quarticAtomicJAt_four_uniform_margin
    {lam : ℝ} (hlam : 1/2 ≤ lam) :
    quarticAtomicJAt lam 4
      ≤ -(11 * Real.pi^4 / 1728) := by
  rw [quarticAtomicJAt_four_formula]
  have hp : 0 < Real.pi^4 := by positivity
  nlinarith

theorem quarticAtomicJAt_two_root :
    quarticAtomicJAt (8/13) 2 = 0 := by
  rw [quarticAtomicJAt_two_formula]
  ring

theorem quarticAtomicJAt_four_at_root :
    quarticAtomicJAt (8/13) 4
      = -(175 * Real.pi^4 / 4212) := by
  rw [quarticAtomicJAt_four_formula]
  ring

end Synthesis
