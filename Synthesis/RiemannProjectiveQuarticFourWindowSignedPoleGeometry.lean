import Synthesis.RiemannProjectiveQuarticFourWindowAtomicPoleSign

/-!
# Signed pole cancellation can preserve the quartic target at atomic level

The narrow four-window pole channel is positive, so nonnegative coefficient
cancellation is impossible.  Signed coefficients are nevertheless viable.

On the exact atomic J2-null curve let

  S(lambda) = -J4(lambda,mu(lambda)) > 0

be the leading quartic target strength, and let

  P(lambda) = 3(2-lambda)/4 > 0

be the high-ordinate projective pole coordinate.

At the endpoint witnesses lambda=1/2 and lambda=2/3,

  P(1/2) = 9/8,
  P(2/3) = 1,

  S(1/2) = 73*pi^4/2808,
  S(2/3) = pi^4/243.

Therefore the pole-cancelling signed coefficients

  c1 = P(2/3),   c2 = -P(1/2)

leave the strictly positive quartic target coefficient

  c1*S(1/2) + c2*S(2/3)
    = 5*pi^4/234 > 0.

Thus the pole-sign firewall rules out only the positive cone.  It does not rule
out a signed orthogonalization: the endpoint atomic family is explicitly
transverse to the pole channel in the target direction.
-/

noncomputable section

open scoped Real

namespace Synthesis

def quarticFourAtomicTargetStrength (lam : ℝ) : ℝ :=
  - quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 4

theorem quarticFourAtomicTargetStrength_pos
    {lam : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3) :
    0 < quarticFourAtomicTargetStrength lam := by
  unfold quarticFourAtomicTargetStrength
  exact neg_pos.mpr
    (quarticFourAtomicJ4_neg_on_half_twoThirds hlam1 hlam2)

theorem quarticFourAtomicPole_half :
    quarticFourAtomicHighPoleResidual
      (1/2) (quarticFourAtomicMu (1/2)) = 9/8 := by
  rw [quarticFourAtomicHighPoleResidual_formula]
  ring

theorem quarticFourAtomicPole_twoThirds :
    quarticFourAtomicHighPoleResidual
      (2/3) (quarticFourAtomicMu (2/3)) = 1 := by
  rw [quarticFourAtomicHighPoleResidual_formula]
  ring

theorem quarticFourAtomicTargetStrength_half :
    quarticFourAtomicTargetStrength (1/2)
      = 73 * Real.pi^4 / 2808 := by
  unfold quarticFourAtomicTargetStrength
  rw [quarticFourAtomicJ4_on_null_formula
      (by norm_num : (1/2 : ℝ) <= 2/3)]
  ring

theorem quarticFourAtomicTargetStrength_twoThirds :
    quarticFourAtomicTargetStrength (2/3)
      = Real.pi^4 / 243 := by
  unfold quarticFourAtomicTargetStrength
  rw [quarticFourAtomicJ4_on_null_formula
      (by norm_num : (2/3 : ℝ) <= 2/3)]
  ring

def quarticFourAtomicPoleCancelledTargetStrength : ℝ :=
  quarticFourAtomicHighPoleResidual
      (2/3) (quarticFourAtomicMu (2/3))
    * quarticFourAtomicTargetStrength (1/2)
  -
  quarticFourAtomicHighPoleResidual
      (1/2) (quarticFourAtomicMu (1/2))
    * quarticFourAtomicTargetStrength (2/3)

theorem quarticFourAtomicPoleCancelledTargetStrength_formula :
    quarticFourAtomicPoleCancelledTargetStrength
      = 5 * Real.pi^4 / 234 := by
  unfold quarticFourAtomicPoleCancelledTargetStrength
  rw [quarticFourAtomicPole_half,
      quarticFourAtomicPole_twoThirds,
      quarticFourAtomicTargetStrength_half,
      quarticFourAtomicTargetStrength_twoThirds]
  ring

theorem quarticFourAtomicPoleCancelledTargetStrength_pos :
    0 < quarticFourAtomicPoleCancelledTargetStrength := by
  rw [quarticFourAtomicPoleCancelledTargetStrength_formula]
  positivity

/--
Abstract two-channel algebra: the coefficients P2 and -P1 cancel the pole
coordinate exactly, while the target survives precisely when the pole/target
determinant is positive.
-/
theorem signed_two_detector_pole_cancel_target_pos
    {P1 P2 D1 D2 : ℝ}
    (hdet : 0 < P2*D1 - P1*D2) :
    (P2*P1 + (-P1)*P2 = 0)
      ∧ 0 < P2*D1 + (-P1)*D2 := by
  constructor
  · ring
  · simpa [sub_eq_add_neg] using hdet

end Synthesis
