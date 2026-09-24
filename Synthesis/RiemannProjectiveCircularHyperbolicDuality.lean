import Synthesis.RiemannProjectiveQuarticMomentEscape
import Synthesis.RiemannCompactCosineFourthDerivative

/-!
# Exact projective circular/hyperbolic profile duality

For a taper g and sampling radius r define the signed physical projective
profile

  P_{g,r}(u) = 4 g(u) B_r(u),

where

  B_r(u) = A_0(r) cos(2ru) - A_0(2r) cos(ru).

Then two apparently different Goal-1 observables are exactly the same profile
tested against circular and hyperbolic cosine:

  Phi_{g,r}(q) = integral P_{g,r}(u) cos(q u) du,

  D_{g,r}(a,0) = -1/4 integral P_{g,r}(u) cosh(a u) du.

The second identity is just the determinant definition expanded under the
integral.  It explains all even-order sign relations at once.

In particular:
* integral P = 0 exactly;
* integral P u^2 = 4 J2;
* integral P u^4 = 4 J4.

Thus J2=0 and J4<0 is an exact fourth-order bifurcation:
the circular kernel has negative fourth derivative at zero, while the target
height defect has positive fourth derivative at zero.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def genericProjectivePhysicalProfile
    (g : ℝ → ℝ) (r u : ℝ) : ℝ :=
  4 * g u * twoRadiusBracket g r u

def genericProjectiveBaseKernel
    (g : ℝ → ℝ) (r q : ℝ) : ℝ :=
  compactCosineTransform (genericProjectivePhysicalProfile g r) q

theorem genericProjectivePhysicalProfile_continuous
    {g : ℝ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous (genericProjectivePhysicalProfile g r) := by
  unfold genericProjectivePhysicalProfile twoRadiusBracket
  fun_prop

theorem genericProjectivePhysicalProfile_compact
    {g : ℝ → ℝ} (hgc : HasCompactSupport g) (r : ℝ) :
    HasCompactSupport (genericProjectivePhysicalProfile g r) := by
  unfold genericProjectivePhysicalProfile
  exact (hgc.mul_left).mul_right

private theorem projectiveBracketZerothMoment_eq_zero
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    (∫ u : ℝ, g u * twoRadiusBracket g r u) = 0 := by
  let f2 : ℝ → ℝ := fun u => g u * Real.cos ((2*r)*u)
  let f1 : ℝ → ℝ := fun u => g u * Real.cos (r*u)
  have hf2 : Integrable f2 :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hf1 : Integrable f1 :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  unfold twoRadiusBracket
  have hpoint :
      (fun u : ℝ =>
        g u *
          (evenResp g 0 r * Real.cos (2*r*u)
            - evenResp g 0 (2*r) * Real.cos (r*u)))
        =
      (fun u : ℝ =>
        evenResp g 0 r * f2 u
          - evenResp g 0 (2*r) * f1 u) := by
    funext u
    dsimp [f1, f2]
    ring
  rw [hpoint]
  rw [integral_sub (hf2.const_mul _) (hf1.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  have h2 : (∫ u : ℝ, f2 u) = evenResp g 0 (2*r) := by
    unfold f2 evenResp
    simp only [zero_mul, Real.cosh_zero, one_mul]
  have h1 : (∫ u : ℝ, f1 u) = evenResp g 0 r := by
    unfold f1 evenResp
    simp only [zero_mul, Real.cosh_zero, one_mul]
  rw [h2, h1]
  ring

theorem genericProjectivePhysicalProfile_integral_zero
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    (∫ u : ℝ, genericProjectivePhysicalProfile g r u) = 0 := by
  unfold genericProjectivePhysicalProfile
  rw [integral_const_mul]
  rw [projectiveBracketZerothMoment_eq_zero hg hgc r]
  ring

theorem genericProjectivePhysicalProfile_secondMoment
    {g : ℝ → ℝ}
    (r : ℝ) :
    (∫ u : ℝ, genericProjectivePhysicalProfile g r u * u^2)
      =
    4 * projectiveBracketSecondMoment g r := by
  unfold genericProjectivePhysicalProfile projectiveBracketSecondMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem genericProjectivePhysicalProfile_fourthMoment
    {g : ℝ → ℝ}
    (r : ℝ) :
    (∫ u : ℝ, genericProjectivePhysicalProfile g r u * u^4)
      =
    4 * projectiveBracketFourthMoment g r := by
  unfold genericProjectivePhysicalProfile projectiveBracketFourthMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

/--
Exact function-level duality between the target height defect and the same
signed projective profile used by the q-kernel.
-/
theorem heightDefect_eq_neg_quarter_projectiveCosh
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r a : ℝ) :
    heightDefect g r a 0
      =
    -(1/4 : ℝ) *
      ∫ u : ℝ,
        genericProjectivePhysicalProfile g r u * Real.cosh (a*u) := by
  let fr : ℝ → ℝ := fun u => g u * Real.cosh (a*u) * Real.cos (r*u)
  let f2r : ℝ → ℝ := fun u => g u * Real.cosh (a*u) * Real.cos ((2*r)*u)
  have hfr : Integrable fr :=
    (by dsimp [fr]; fun_prop : Continuous fr)
      |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)
  have hf2r : Integrable f2r :=
    (by dsimp [f2r]; fun_prop : Continuous f2r)
      |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)
  unfold heightDefect
  have hAr : (∫ u : ℝ, fr u) = evenResp g a r := by
    unfold fr evenResp
    rfl
  have hA2r : (∫ u : ℝ, f2r u) = evenResp g a (2*r) := by
    unfold f2r evenResp
    rfl
  rw [← hAr, ← hA2r]
  rw [← integral_const_mul, ← integral_const_mul]
  rw [← integral_sub (hfr.const_mul _) (hf2r.const_mul _)]
  apply Eq.symm
  rw [show (-(1/4 : ℝ)) * (∫ u : ℝ,
      genericProjectivePhysicalProfile g r u * Real.cosh (a*u))
      =
      ∫ u : ℝ,
        (-(1/4 : ℝ)) *
          (genericProjectivePhysicalProfile g r u * Real.cosh (a*u)) by
        rw [integral_const_mul]]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    unfold genericProjectivePhysicalProfile twoRadiusBracket
    dsimp [fr, f2r]
    ring

theorem genericProjectiveBaseKernel_zero
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    genericProjectiveBaseKernel g r 0 = 0 := by
  unfold genericProjectiveBaseKernel compactCosineTransform
  simp only [zero_mul, Real.cos_zero, mul_one]
  exact genericProjectivePhysicalProfile_integral_zero hg hgc r

end Synthesis
