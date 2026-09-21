import Synthesis.RiemannProjectiveQuarticFourWindowAtomic

/-!
# Atomic pole sign for the four-window quartic family

The extra fourth window does not create pole-sign freedom in the high-ordinate
atomic limit.

At normalized radii

  0, pi/3, pi/2, pi

with signed weights

  1, -1, lambda, mu,

the on-line radius responses are

  A1 = 1/2 - mu,
  A2 = 3/2 - lambda + mu,

while the high-ordinate pole responses are

  P1 = 5/4 - mu,
  P2 = 3/4 - lambda + mu.

The projective pole determinant is therefore

  P1*A2 - P2*A1 = 3(2-lambda)/4,

so mu cancels identically.  On lambda in [1/2,2/3] this is at least 1.

The finite-t atomic formula is also recorded.  Writing

  h1 = cosh(8*pi/(3t)),
  h2 = cosh(4*pi/t),
  h3 = cosh(8*pi/t),

the determinant is

  1-lambda
    + h1(1/2-lambda/4)
    + h2(lambda/2-lambda*mu)
    + h3(lambda*mu-2*mu)
    + 2*mu.

Equivalently its deviation from the high-ordinate value is

  (h1-1)(1/2-lambda/4)
  + (h2-1)(lambda/2-lambda*mu)
  + (h3-1)mu(lambda-2).

This isolates the only potentially negative finite-t correction: the last term
when mu>0.  In particular the fourth window does not supply an asymptotic pole
sign crossing.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticFourAtomicOnLineOne (lam mu : ℝ) : ℝ :=
  1/2 - mu

def quarticFourAtomicOnLineTwo (lam mu : ℝ) : ℝ :=
  3/2 - lam + mu

def quarticFourAtomicHighPoleOne (lam mu : ℝ) : ℝ :=
  5/4 - mu

def quarticFourAtomicHighPoleTwo (lam mu : ℝ) : ℝ :=
  3/4 - lam + mu

def quarticFourAtomicHighPoleResidual (lam mu : ℝ) : ℝ :=
  quarticFourAtomicHighPoleOne lam mu
      * quarticFourAtomicOnLineTwo lam mu
    - quarticFourAtomicHighPoleTwo lam mu
      * quarticFourAtomicOnLineOne lam mu

theorem quarticFourAtomicHighPoleResidual_formula
    (lam mu : ℝ) :
    quarticFourAtomicHighPoleResidual lam mu
      = 3 * (2-lam) / 4 := by
  unfold quarticFourAtomicHighPoleResidual
    quarticFourAtomicHighPoleOne quarticFourAtomicHighPoleTwo
    quarticFourAtomicOnLineOne quarticFourAtomicOnLineTwo
  ring

theorem quarticFourAtomicHighPoleResidual_independent_mu
    (lam mu1 mu2 : ℝ) :
    quarticFourAtomicHighPoleResidual lam mu1
      = quarticFourAtomicHighPoleResidual lam mu2 := by
  rw [quarticFourAtomicHighPoleResidual_formula,
      quarticFourAtomicHighPoleResidual_formula]

theorem quarticFourAtomicHighPoleResidual_ge_one
    {lam mu : ℝ}
    (hlam : lam <= 2/3) :
    1 <= quarticFourAtomicHighPoleResidual lam mu := by
  rw [quarticFourAtomicHighPoleResidual_formula]
  linarith

theorem quarticFourAtomicHighPoleResidual_pos
    {lam mu : ℝ}
    (hlam : lam <= 2/3) :
    0 < quarticFourAtomicHighPoleResidual lam mu := by
  have h := quarticFourAtomicHighPoleResidual_ge_one
    (mu:=mu) hlam
  linarith

/-- Exact finite-t atomic projective pole determinant. -/
def quarticFourAtomicFinitePoleResidual
    (t lam mu : ℝ) : ℝ :=
  let h1 := Real.cosh (8 * Real.pi / (3*t))
  let h2 := Real.cosh (4 * Real.pi / t)
  let h3 := Real.cosh (8 * Real.pi / t)
  1-lam
    + h1*(1/2-lam/4)
    + h2*(lam/2-lam*mu)
    + h3*(lam*mu-2*mu)
    + 2*mu

theorem quarticFourAtomicFinitePoleResidual_sub_high
    (t lam mu : ℝ) :
    quarticFourAtomicFinitePoleResidual t lam mu
      - quarticFourAtomicHighPoleResidual lam mu
      =
    (Real.cosh (8 * Real.pi / (3*t))-1) * (1/2-lam/4)
      + (Real.cosh (4 * Real.pi / t)-1) * (lam/2-lam*mu)
      + (Real.cosh (8 * Real.pi / t)-1) * (lam*mu-2*mu) := by
  unfold quarticFourAtomicFinitePoleResidual
  rw [quarticFourAtomicHighPoleResidual_formula]
  ring

/--
A purely algebraic robustness compiler.

On the four-window witness corridor, the first two finite-t corrections are
nonnegative.  If the largest cosh excess is at most one, the potentially
negative fourth-window correction cannot consume the unit high-ordinate pole
margin.
-/
theorem quarticFourAtomicFinitePoleResidual_pos_of_cosh_excess_le_one
    {t lam mu : ℝ}
    (hlam1 : 1/2 <= lam)
    (hlam2 : lam <= 2/3)
    (hmu : |mu| <= 1/10)
    (hcosh3 : Real.cosh (8 * Real.pi / t) - 1 <= 1) :
    0 < quarticFourAtomicFinitePoleResidual t lam mu := by
  have hhigh :
      1 <= quarticFourAtomicHighPoleResidual lam mu :=
    quarticFourAtomicHighPoleResidual_ge_one hlam2
  have h1non :
      0 <= Real.cosh (8 * Real.pi / (3*t)) - 1 := by
    linarith [Real.one_le_cosh (8 * Real.pi / (3*t))]
  have h2non :
      0 <= Real.cosh (4 * Real.pi / t) - 1 := by
    linarith [Real.one_le_cosh (4 * Real.pi / t)]
  have h3non :
      0 <= Real.cosh (8 * Real.pi / t) - 1 := by
    linarith [Real.one_le_cosh (8 * Real.pi / t)]
  have hcoef1 : 0 <= 1/2-lam/4 := by
    linarith
  have hcoef2 : 0 <= lam/2-lam*mu := by
    have hmule : mu <= 1/10 := (abs_le.mp hmu).2
    nlinarith
  have hmuLo : -1/10 <= mu := (abs_le.mp hmu).1
  have hmuHi : mu <= 1/10 := (abs_le.mp hmu).2
  have hterm1 :
      0 <=
        (Real.cosh (8 * Real.pi / (3*t))-1) * (1/2-lam/4) :=
    mul_nonneg h1non hcoef1
  have hterm2 :
      0 <=
        (Real.cosh (4 * Real.pi / t)-1) * (lam/2-lam*mu) :=
    mul_nonneg h2non hcoef2
  have hterm3 :
      -(3/20 : ℝ) <=
        (Real.cosh (8 * Real.pi / t)-1) * (lam*mu-2*mu) := by
    by_cases hm : 0 <= mu
    · have hcoef3 : -(3/20 : ℝ) <= lam*mu-2*mu := by
        nlinarith
      have hfac : 0 <= Real.cosh (8 * Real.pi / t)-1 := h3non
      have hfacle : Real.cosh (8 * Real.pi / t)-1 <= 1 := hcosh3
      have hcoef3nonpos : lam*mu-2*mu <= 0 := by
        nlinarith
      nlinarith [mul_nonneg hfac (by nlinarith : 3/20 + (lam*mu-2*mu) >= 0),
        mul_nonpos_of_nonneg_of_nonpos hfac hcoef3nonpos]
    · have hmneg : mu < 0 := lt_of_not_ge hm
      have hcoef3 : 0 <= lam*mu-2*mu := by
        nlinarith
      exact le_trans (by norm_num) (mul_nonneg h3non hcoef3)
  rw [← quarticFourAtomicFinitePoleResidual_sub_high t lam mu]
  linarith

end Synthesis
