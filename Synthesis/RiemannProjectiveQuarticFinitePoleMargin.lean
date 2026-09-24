import Synthesis.RiemannProjectiveQuarticAtomicPoleSign

/-!
# Uniform finite-t atomic pole margin for the quartic witness interval

At physical radius r=t/16 the normalized pole weight contains

  cosh(8 v/t) cos(16 v).

Evaluating the atomic three-point profile at v=0, pi/3, pi/2 gives the finite-t
projective pole determinant

  P_t(lambda)
    = 1 - lambda
      + cosh(8*pi/(3*t)) * (1/2 - lambda/4)
      + lambda * cosh(4*pi/t) / 2.

For lambda in [1/2,3/4], every coefficient displayed above is nonnegative.
Using cosh >= 1 gives the uniform lower bound

  P_t(lambda) >= 9/16 > 0

for every nonzero t.  Thus the atomic pole coordinate never approaches the
origin anywhere in the quartic witness interval.

The final compiler in this file is intentionally abstract: any smooth pole
residual within 9/16 of this atomic value is strictly positive.  This isolates
the remaining work to a pure localization/same-object estimate.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticAtomicFinitePoleResidual (t lam : ℝ) : ℝ :=
  1 - lam
    + Real.cosh (8 * Real.pi / (3*t)) * (1/2 - lam/4)
    + lam * Real.cosh (4 * Real.pi / t) / 2

theorem quarticAtomicFinitePoleResidual_ge_nine_sixteenths
    {t lam : ℝ} (ht : t ≠ 0)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)) :
    9/16 <= quarticAtomicFinitePoleResidual t lam := by
  have hc1 : 1 <= Real.cosh (8 * Real.pi / (3*t)) :=
    Real.one_le_cosh _
  have hc2 : 1 <= Real.cosh (4 * Real.pi / t) :=
    Real.one_le_cosh _
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hcoef : 0 <= 1/2 - lam/4 := by linarith [hlam.2]
  have hterm1 :
      1/4 <= 1 - lam := by
    linarith [hlam.2]
  have hterm2 :
      5/16 <=
        Real.cosh (8 * Real.pi / (3*t)) * (1/2 - lam/4) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hc1 hcoef
    nlinarith [hlam.2]
  have hterm3 :
      0 <= lam * Real.cosh (4 * Real.pi / t) / 2 := by
    positivity
  unfold quarticAtomicFinitePoleResidual
  linarith

theorem quarticAtomicFinitePoleResidual_pos
    {t lam : ℝ} (ht : t ≠ 0)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ)) :
    0 < quarticAtomicFinitePoleResidual t lam := by
  have h :=
    quarticAtomicFinitePoleResidual_ge_nine_sixteenths ht hlam
  linarith

/--
Any smooth pole residual whose absolute error from the finite-t atomic channel
is strictly below the uniform 9/16 margin must itself be positive.
-/
theorem smoothPoleResidual_pos_of_close_atomic
    {t lam smoothPole : ℝ}
    (ht : t ≠ 0)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ))
    (hclose :
      |smoothPole - quarticAtomicFinitePoleResidual t lam| < 9/16) :
    0 < smoothPole := by
  have hatom :=
    quarticAtomicFinitePoleResidual_ge_nine_sixteenths ht hlam
  have hlo := (abs_lt.mp hclose).1
  linarith

/--
A convenient half-margin version for later localization estimates.
-/
theorem smoothPoleResidual_pos_of_close_atomic_halfMargin
    {t lam smoothPole : ℝ}
    (ht : t ≠ 0)
    (hlam : lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ))
    (hclose :
      |smoothPole - quarticAtomicFinitePoleResidual t lam| <= 9/32) :
    0 < smoothPole := by
  apply smoothPoleResidual_pos_of_close_atomic ht hlam
  exact lt_of_le_of_lt hclose (by norm_num)

end Synthesis
