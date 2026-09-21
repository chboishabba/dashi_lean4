import Synthesis.RiemannProjectiveCircularHyperbolicDuality
import Synthesis.RiemannCompactCoshFourthDerivative

/-!
# Positive local target detector from quartic projective moment cancellation

Let P=P_{g,r}=4 g B_r.  Under

  J2(g,r)=0,
  J4(g,r)<0,

the compact hyperbolic transform

  H(a)=integral P(u) cosh(a u) du

has

  H(0)=H'(0)=H''(0)=H'''(0)=0,
  H''''(0)=4 J4<0.

The fourth-order local-sign compiler therefore gives H(a)<0 for small nonzero
a.  The exact circular/hyperbolic duality then gives

  heightDefect(g,r,a,0) = -H(a)/4 > 0.

Thus the same moment-cancelled condition that creates a negative local q-lobe
also preserves a positive local target detector.  This pays the local
feasibility of the quartic escape at the level of actual observables.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

theorem compactCoshD1_zero (P : ℝ → ℝ) :
    compactCoshD1 P 0 = 0 := by
  unfold compactCoshD1
  simp

theorem compactCoshD3_zero (P : ℝ → ℝ) :
    compactCoshD3 P 0 = 0 := by
  unfold compactCoshD3
  simp

theorem genericProjectiveCosh_secondDeriv_zero
    {g : ℝ → ℝ} {r : ℝ}
    (hJ2 : projectiveBracketSecondMoment g r = 0) :
    compactCoshD2 (genericProjectivePhysicalProfile g r) 0 = 0 := by
  unfold compactCoshD2
  simp only [zero_mul, Real.cosh_zero, mul_one]
  have hm :=
    genericProjectivePhysicalProfile_secondMoment (g := g) r
  rw [hJ2] at hm
  exact hm.trans (by ring)

theorem genericProjectiveCosh_fourthDeriv_zero
    {g : ℝ → ℝ} {r : ℝ} :
    compactCoshD4 (genericProjectivePhysicalProfile g r) 0
      =
    4 * projectiveBracketFourthMoment g r := by
  unfold compactCoshD4
  simp only [zero_mul, Real.cosh_zero, mul_one]
  exact genericProjectivePhysicalProfile_fourthMoment (g := g) r

/-- The hyperbolic transform itself is negative near zero under quartic escape. -/
theorem exists_genericProjectiveCosh_neg_right_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < a → a < eps →
        compactCoshTransform
          (genericProjectivePhysicalProfile g r) a < 0 := by
  let P : ℝ → ℝ := genericProjectivePhysicalProfile g r
  have hP : Continuous P :=
    genericProjectivePhysicalProfile_continuous hg r
  have hPc : HasCompactSupport P :=
    genericProjectivePhysicalProfile_compact hgc r

  have h0 : compactCoshTransform P 0 = 0 := by
    unfold compactCoshTransform
    simp only [zero_mul, Real.cosh_zero, mul_one]
    simpa [P] using
      genericProjectivePhysicalProfile_integral_zero hg hgc r
  have h1 : compactCoshD1 P 0 = 0 :=
    compactCoshD1_zero P
  have h2 : compactCoshD2 P 0 = 0 := by
    simpa [P] using
      genericProjectiveCosh_secondDeriv_zero
        (g := g) (r := r) hJ2
  have h3 : compactCoshD3 P 0 = 0 :=
    compactCoshD3_zero P
  have h4 : compactCoshD4 P 0 < 0 := by
    rw [show compactCoshD4 P 0
        = 4 * projectiveBracketFourthMoment g r by
          simpa [P] using
            genericProjectiveCosh_fourthDeriv_zero
              (g := g) (r := r)]
    nlinarith

  exact
    exists_neg_right_of_fourth_deriv_neg
      (f := compactCoshTransform P)
      (f1 := compactCoshD1 P)
      (f2 := compactCoshD2 P)
      (f3 := compactCoshD3 P)
      (f4 := compactCoshD4 P)
      (fun a => compactCoshTransform_hasDerivAt hP hPc a)
      (fun a => compactCoshD1_deriv hP hPc a)
      (fun a => compactCoshD2_deriv hP hPc a)
      (fun a => compactCoshD3_deriv hP hPc a)
      (compactCoshD4_continuous hP hPc)
      h0 h1 h2 h3 h4

/-- Exact target-height defect is positive on a right punctured neighbourhood. -/
theorem exists_heightDefect_pos_right_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < a → a < eps →
        0 < heightDefect g r a 0 := by
  obtain ⟨eps, heps, hH⟩ :=
    exists_genericProjectiveCosh_neg_right_of_quartic_escape
      hg hgc hJ2 hJ4
  refine ⟨eps, heps, ?_⟩
  intro a ha0 hae
  rw [heightDefect_eq_neg_quarter_projectiveCosh hg hgc r a]
  have hneg := hH a ha0 hae
  nlinarith

theorem heightDefect_neg_height
    (g : ℝ → ℝ) (r a : ℝ) :
    heightDefect g r (-a) 0 = heightDefect g r a 0 := by
  unfold heightDefect
  simp [Real.cosh_neg]

/-- Evenness in height gives a two-sided punctured positive target band. -/
theorem exists_heightDefect_pos_punctured_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < |a| → |a| < eps →
        0 < heightDefect g r a 0 := by
  obtain ⟨eps, heps, hright⟩ :=
    exists_heightDefect_pos_right_of_quartic_escape
      hg hgc hJ2 hJ4
  refine ⟨eps, heps, ?_⟩
  intro a ha0 hae
  by_cases ha : 0 ≤ a
  · have habs : |a| = a := abs_of_nonneg ha
    rw [habs] at ha0 hae
    exact hright a ha0 hae
  · have haneg : a < 0 := lt_of_not_ge ha
    have habs : |a| = -a := abs_of_neg haneg
    have hp := hright (-a) (by linarith) (by simpa [habs] using hae)
    rw [heightDefect_neg_height] at hp
    exact hp

end Synthesis
