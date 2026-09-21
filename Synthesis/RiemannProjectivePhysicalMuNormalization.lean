import Synthesis.RiemannProjectiveQuarticOffPairNormalization
import Synthesis.RiemannProjectiveRvMMuGammaSameObject

/-!
# Exact Fourier normalization of the projective sample test

For an even real taper g, the literal projective sample at s=0 is

  k(u) = projTaper(g,r)(u) * exp(-i t u).

Its paper Fourier transform at real ordinate tau is therefore the ordinary
cosine transform of projTaper at frequency tau-t; the sine part vanishes by
oddness.  Since

  genericProjectivePhysicalProfile(g,r) = 4 * projTaper(g,r),

we obtain the exact pointwise normalization

  paperFT(k)(tau)
    = (1/4) * genericProjectiveBaseKernel(g,r,tau-t).

Consequently the signed RvM-mu projective pairing is

  projectiveRvMMuSignedPair(g,t,r)
    = -(1/4) integral Phi_{g,r}(tau-t) mu(tau) d tau.

This is the factor bookkeeping needed to identify the reflection-pair zero
normalization (1/2) plus the named Gamma defect (factor 2) with exactly one half
of a literal N-mu pairing.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper

theorem paperFT_literalProjectiveSampleTest_eq_quarter_baseKernel
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r tau : ℝ) :
    paperFT (literalProjectiveSampleTest g t r) tau
      =
    (((1/4 : ℝ) *
      genericProjectiveBaseKernel g r (tau-t) : ℝ) : ℂ) := by
  have hpcont :
      Continuous (projTaper g r) :=
    projTaper_continuous hg r
  have hpcomp :
      HasCompactSupport (projTaper g r) :=
    projTaper_hasCompactSupport hgc r
  have hpeven :
      ∀ u, projTaper g r (-u) = projTaper g r u :=
    projTaper_even heven r

  have hcos :
      Integrable
        (fun u : ℝ =>
          projTaper g r u * Real.cos ((tau-t)*u)) :=
    (hpcont.mul (by fun_prop)).integrable_of_hasCompactSupport
      hpcomp.mul_right
  have hsin :
      Integrable
        (fun u : ℝ =>
          projTaper g r u * Real.sin ((tau-t)*u)) :=
    (hpcont.mul (by fun_prop)).integrable_of_hasCompactSupport
      hpcomp.mul_right

  have hsin0 :
      (∫ u : ℝ,
        projTaper g r u * Real.sin ((tau-t)*u)) = 0 := by
    apply integral_odd_zero
    intro u
    rw [hpeven u]
    simp [Real.sin_neg]
    ring

  rw [paperFT]
  have hpoint :
      (fun u : ℝ =>
        literalProjectiveSampleTest g t r u
          * Complex.exp (Complex.I * (tau : ℂ) * u))
        =
      fun u : ℝ =>
        ((projTaper g r u * Real.cos ((tau-t)*u) : ℝ) : ℂ)
          + Complex.I *
            ((projTaper g r u * Real.sin ((tau-t)*u) : ℝ) : ℂ) := by
    funext u
    unfold literalProjectiveSampleTest sampleTest
    rw [← Complex.exp_add]
    have hexp :
        Complex.I * ((((0:ℝ)-t)*u : ℝ) : ℂ)
          + Complex.I * (tau : ℂ) * u
          =
        Complex.I * ((((tau-t)*u : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hexp, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  rw [hpoint, integral_ofReal_add_I hcos hsin, hsin0]
  simp only [ofReal_zero, mul_zero, add_zero]
  rw [integral_complex_ofReal]
  unfold genericProjectiveBaseKernel compactCosineTransform
    genericProjectivePhysicalProfile projTaper
  rw [← integral_const_mul]
  apply congrArg Complex.ofReal
  ring_nf
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    ring

/--
Exact real mu-pairing normalization for the projective physical cosine kernel.
-/
theorem projectiveRvMMuSignedPair_eq_neg_quarter_base_mu_integral
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    projectiveRvMMuSignedPair g t r
      =
    -(1/4 : ℝ) *
      ∫ tau : ℝ,
        genericProjectiveBaseKernel g r (tau-t)
          * Zeta23.mu tau := by
  unfold projectiveRvMMuSignedPair projectiveRvMMuPair
  have hfun :
      (fun tau : ℝ =>
        paperFT (literalProjectiveSampleTest g t r) tau
          * (Zeta23.mu tau : ℂ))
        =
      fun tau : ℝ =>
        ((((1/4 : ℝ) *
          genericProjectiveBaseKernel g r (tau-t)
          * Zeta23.mu tau : ℝ)) : ℂ) := by
    funext tau
    rw [paperFT_literalProjectiveSampleTest_eq_quarter_baseKernel
      hg hgc heven t r tau]
    push_cast
    ring
  rw [hfun, integral_complex_ofReal]
  simp [Zeta23Bridge.LiteralWeilParityBalance.reim]
  rw [← integral_const_mul]
  ring

end Synthesis
