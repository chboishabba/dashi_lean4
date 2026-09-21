import Synthesis.RiemannProjectiveQuarticAtomicFamily

/-!
# Atomic high-ordinate pole channel for the quartic family

For the atomic three-point profile with weights

  (1, -1, lambda)

at normalized radii

  0, pi/3, pi/2,

the high-ordinate limit of the projective pole channel is elementary.

After physical rescaling r=t/16 and then t -> infinity, the pole weight
cosh(u/2) becomes 1 in normalized coordinates while the t-frequency becomes
cos(16 v).  At the three atomic radii,

  cos(16*0)      = 1,
  cos(16*pi/3)   = -1/2,
  cos(16*pi/2)   = 1.

The selected- and doubled-radius pole responses are therefore

  P1(lambda) = 5/4,
  P2(lambda) = 3/4 - lambda,

whereas the on-line responses are

  A1(lambda) = 1/2,
  A2(lambda) = 3/2 - lambda.

With the projective orientation used by the pole defect,

  P_atom(lambda) = P1*A2 - P2*A1
                 = 3(2-lambda)/4.

Hence the atomic pole channel is uniformly strictly positive throughout the
whole quartic witness interval [1/2,3/4].  At the exact atomic quartic root
lambda=8/13 it equals 27/26.

This is the scalar sign that the smooth small-window/high-t family must overcome
if the positive-cone base/pole orthogonalization lane is to survive.
-/

noncomputable section

namespace Synthesis

def quarticAtomicOnLineOne (lam : ℝ) : ℝ := 1 / 2

def quarticAtomicOnLineTwo (lam : ℝ) : ℝ := 3 / 2 - lam

def quarticAtomicHighPoleOne (lam : ℝ) : ℝ := 5 / 4

def quarticAtomicHighPoleTwo (lam : ℝ) : ℝ := 3 / 4 - lam

def quarticAtomicHighPoleResidual (lam : ℝ) : ℝ :=
  quarticAtomicHighPoleOne lam * quarticAtomicOnLineTwo lam
    - quarticAtomicHighPoleTwo lam * quarticAtomicOnLineOne lam

theorem quarticAtomicHighPoleResidual_formula (lam : ℝ) :
    quarticAtomicHighPoleResidual lam = 3 * (2 - lam) / 4 := by
  unfold quarticAtomicHighPoleResidual
    quarticAtomicHighPoleOne quarticAtomicHighPoleTwo
    quarticAtomicOnLineOne quarticAtomicOnLineTwo
  ring

theorem quarticAtomicHighPoleResidual_pos_of_le_three_quarters
    {lam : ℝ} (hlam : lam <= 3/4) :
    0 < quarticAtomicHighPoleResidual lam := by
  rw [quarticAtomicHighPoleResidual_formula]
  nlinarith

theorem quarticAtomicHighPoleResidual_uniform_margin
    {lam : ℝ} (hlam : lam <= 3/4) :
    15/16 <= quarticAtomicHighPoleResidual lam := by
  rw [quarticAtomicHighPoleResidual_formula]
  nlinarith

theorem quarticAtomicHighPoleResidual_at_root :
    quarticAtomicHighPoleResidual (8/13) = 27/26 := by
  rw [quarticAtomicHighPoleResidual_formula]
  ring

/--
The exact atomic quartic root selected by J2=0 lies in the witness interval and
has a strictly positive pole channel.
-/
theorem quarticAtomic_root_has_positive_highPole :
    quarticAtomicJAt (8/13) 2 = 0
      ∧ 0 < quarticAtomicHighPoleResidual (8/13) := by
  constructor
  · exact quarticAtomicJAt_two_root
  · rw [quarticAtomicHighPoleResidual_at_root]
    norm_num

end Synthesis
