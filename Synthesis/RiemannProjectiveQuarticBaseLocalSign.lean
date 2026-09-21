import Synthesis.RiemannProjectiveCircularHyperbolicDuality

/-!
# Actual negative local lobe from quartic projective moment cancellation

This instantiates the generic fourth-order sign compiler on the exact signed
projective physical profile P_{g,r}.

If

  J2(g,r) = integral g u^2 B_r = 0,
  J4(g,r) = integral g u^4 B_r < 0,

then the q-kernel

  Phi_{g,r}(q) = integral P_{g,r}(u) cos(q u) du

has

  Phi(0)=Phi'(0)=Phi''(0)=Phi'''(0)=0,
  Phi''''(0)=4 J4 < 0.

Therefore Phi is strictly negative on a right punctured neighbourhood of zero.
Evenness upgrades this to a two-sided punctured band.

This is an actual local sign theorem, not coefficient shorthand.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveTaper

theorem compactCosineD1_zero (P : ℝ → ℝ) :
    compactCosineD1 P 0 = 0 := by
  unfold compactCosineD1
  simp

theorem compactCosineD3_zero (P : ℝ → ℝ) :
    compactCosineD3 P 0 = 0 := by
  unfold compactCosineD3
  simp

theorem genericProjectiveBaseKernel_secondDeriv_zero
    {g : ℝ → ℝ} {r : ℝ}
    (hJ2 : projectiveBracketSecondMoment g r = 0) :
    compactCosineD2 (genericProjectivePhysicalProfile g r) 0 = 0 := by
  unfold compactCosineD2
  simp only [zero_mul, Real.cos_zero, mul_one]
  have hm :=
    genericProjectivePhysicalProfile_secondMoment (g := g) r
  rw [hJ2] at hm
  rw [← integral_neg]
  linarith

theorem genericProjectiveBaseKernel_fourthDeriv_zero
    {g : ℝ → ℝ} {r : ℝ} :
    compactCosineD4 (genericProjectivePhysicalProfile g r) 0
      =
    4 * projectiveBracketFourthMoment g r := by
  unfold compactCosineD4
  simp only [zero_mul, Real.cos_zero, mul_one]
  exact genericProjectivePhysicalProfile_fourthMoment (g := g) r

/--
Quartic moment cancellation gives a genuine negative right lobe for the exact
projective q-kernel.
-/
theorem exists_genericProjectiveBaseKernel_neg_right_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < q → q < eps →
        genericProjectiveBaseKernel g r q < 0 := by
  let P : ℝ → ℝ := genericProjectivePhysicalProfile g r
  have hP : Continuous P :=
    genericProjectivePhysicalProfile_continuous hg r
  have hPc : HasCompactSupport P :=
    genericProjectivePhysicalProfile_compact hgc r

  have h0 : compactCosineTransform P 0 = 0 := by
    simpa [P, genericProjectiveBaseKernel] using
      genericProjectiveBaseKernel_zero hg hgc r
  have h1 : compactCosineD1 P 0 = 0 :=
    compactCosineD1_zero P
  have h2 : compactCosineD2 P 0 = 0 := by
    simpa [P] using
      genericProjectiveBaseKernel_secondDeriv_zero
        (g := g) (r := r) hJ2
  have h3 : compactCosineD3 P 0 = 0 :=
    compactCosineD3_zero P
  have h4 :
      compactCosineD4 P 0 < 0 := by
    rw [show compactCosineD4 P 0
        = 4 * projectiveBracketFourthMoment g r by
          simpa [P] using
            genericProjectiveBaseKernel_fourthDeriv_zero
              (g := g) (r := r)]
    nlinarith

  have hsign :=
    exists_neg_right_of_fourth_deriv_neg
      (f := compactCosineTransform P)
      (f1 := compactCosineD1 P)
      (f2 := compactCosineD2 P)
      (f3 := compactCosineD3 P)
      (f4 := compactCosineD4 P)
      (fun q => compactCosineTransform_hasDerivAt hP hPc q)
      (fun q => compactCosineD1_deriv hP hPc q)
      (fun q => compactCosineD2_deriv hP hPc q)
      (fun q => compactCosineD3_deriv hP hPc q)
      (compactCosineD4_continuous hP hPc)
      h0 h1 h2 h3 h4
  simpa [P, genericProjectiveBaseKernel] using hsign

theorem genericProjectiveBaseKernel_neg
    (g : ℝ → ℝ) (r q : ℝ) :
    genericProjectiveBaseKernel g r (-q)
      = genericProjectiveBaseKernel g r q := by
  unfold genericProjectiveBaseKernel compactCosineTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp [Real.cos_neg]

/-- Evenness gives the desired two-sided punctured negative band. -/
theorem exists_genericProjectiveBaseKernel_neg_punctured_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < |q| → |q| < eps →
        genericProjectiveBaseKernel g r q < 0 := by
  obtain ⟨eps, heps, hright⟩ :=
    exists_genericProjectiveBaseKernel_neg_right_of_quartic_escape
      hg hgc hJ2 hJ4
  refine ⟨eps, heps, ?_⟩
  intro q hq0 hqeps
  by_cases hq : 0 ≤ q
  · have habs : |q| = q := abs_of_nonneg hq
    rw [habs] at hq0 hqeps
    exact hright q hq0 hqeps
  · have hqneg : q < 0 := lt_of_not_ge hq
    have habs : |q| = -q := abs_of_neg hqneg
    have hp := hright (-q) (by linarith) (by simpa [habs] using hqeps)
    rw [genericProjectiveBaseKernel_neg] at hp
    exact hp

end Synthesis
