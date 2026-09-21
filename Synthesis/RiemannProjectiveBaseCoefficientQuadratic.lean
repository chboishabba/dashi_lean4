import Synthesis.RiemannProjectiveQuarticMomentMixing
import Synthesis.RiemannProjectiveQuarticOffPairNormalization

/-!
# Quadratic coefficient algebra for the projective base kernel

The projective bracket is linear in the taper while the physical projective
profile multiplies the taper by that bracket.  Therefore for

  g_lambda = f + lambda h

the projective physical profile and its cosine kernel are exactly quadratic in
lambda.

This matters for the remaining Goal-1 signed discrepancy problem: every finite
N-mu pairing against the projective base kernel is consequently a scalar
quadratic polynomial in any linear taper coefficient.  Parameter selection can
therefore be studied as ordinary real algebra once signs of the coefficient
functionals are known.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper

def projectiveBracketCross
    (f h : ℝ → ℝ) (r u : ℝ) : ℝ :=
  evenResp f 0 r * Real.cos (2*r*u)
    - evenResp f 0 (2*r) * Real.cos (r*u)
    |> fun Bf =>
  Bf * h u
    +
  (evenResp h 0 r * Real.cos (2*r*u)
    - evenResp h 0 (2*r) * Real.cos (r*u)) * f u

def genericProjectivePhysicalProfileCross
    (f h : ℝ → ℝ) (r u : ℝ) : ℝ :=
  4 * projectiveBracketCross f h r u

theorem twoRadiusBracket_mix_linear
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r u : ℝ) :
    twoRadiusBracket (projectiveMixedTaper f h lam) r u
      =
    twoRadiusBracket f r u
      + lam * twoRadiusBracket h r u := by
  unfold twoRadiusBracket
  rw [evenResp_zero_mix hf hfc hh hhc lam r,
      evenResp_zero_mix hf hfc hh hhc lam (2*r)]
  ring

theorem genericProjectivePhysicalProfile_mix_quadratic
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r u : ℝ) :
    genericProjectivePhysicalProfile
        (projectiveMixedTaper f h lam) r u
      =
    genericProjectivePhysicalProfile f r u
      + lam * genericProjectivePhysicalProfileCross f h r u
      + lam^2 * genericProjectivePhysicalProfile h r u := by
  unfold genericProjectivePhysicalProfile
    genericProjectivePhysicalProfileCross
    projectiveBracketCross projectiveMixedTaper
  rw [twoRadiusBracket_mix_linear hf hfc hh hhc lam r u]
  unfold twoRadiusBracket
  ring

def genericProjectiveBaseKernelCross
    (f h : ℝ → ℝ) (r q : ℝ) : ℝ :=
  ∫ u : ℝ,
    genericProjectivePhysicalProfileCross f h r u
      * Real.cos (q*u)

theorem genericProjectivePhysicalProfileCross_continuous
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hh : Continuous h)
    (r : ℝ) :
    Continuous (genericProjectivePhysicalProfileCross f h r) := by
  unfold genericProjectivePhysicalProfileCross projectiveBracketCross
    evenResp
  fun_prop

theorem genericProjectivePhysicalProfileCross_compact
    {f h : ℝ → ℝ}
    (hfc : HasCompactSupport f)
    (hhc : HasCompactSupport h)
    (r : ℝ) :
    HasCompactSupport (genericProjectivePhysicalProfileCross f h r) := by
  unfold genericProjectivePhysicalProfileCross projectiveBracketCross
  exact
    ((hfc.mul_left.add hhc.mul_left).add
      (hhc.mul_left.add hfc.mul_left)).mul_left

theorem genericProjectiveBaseKernel_mix_quadratic
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r q : ℝ) :
    genericProjectiveBaseKernel
        (projectiveMixedTaper f h lam) r q
      =
    genericProjectiveBaseKernel f r q
      + lam * genericProjectiveBaseKernelCross f h r q
      + lam^2 * genericProjectiveBaseKernel h r q := by
  unfold genericProjectiveBaseKernel
    compactCosineTransform
    genericProjectiveBaseKernelCross
  have hff :
      Integrable
        (fun u : ℝ =>
          genericProjectivePhysicalProfile f r u
            * Real.cos (q*u)) :=
    ((genericProjectivePhysicalProfile_continuous hf r).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (genericProjectivePhysicalProfile_compact hfc r).mul_right
  have hcross :
      Integrable
        (fun u : ℝ =>
          genericProjectivePhysicalProfileCross f h r u
            * Real.cos (q*u)) :=
    ((genericProjectivePhysicalProfileCross_continuous hf hh r).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (genericProjectivePhysicalProfileCross_compact hfc hhc r).mul_right
  have hhh :
      Integrable
        (fun u : ℝ =>
          genericProjectivePhysicalProfile h r u
            * Real.cos (q*u)) :=
    ((genericProjectivePhysicalProfile_continuous hh r).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (genericProjectivePhysicalProfile_compact hhc r).mul_right
  have hpoint :
      (fun u : ℝ =>
        genericProjectivePhysicalProfile
          (projectiveMixedTaper f h lam) r u
          * Real.cos (q*u))
        =
      fun u : ℝ =>
        genericProjectivePhysicalProfile f r u * Real.cos (q*u)
          + lam *
            (genericProjectivePhysicalProfileCross f h r u
              * Real.cos (q*u))
          + lam^2 *
            (genericProjectivePhysicalProfile h r u
              * Real.cos (q*u)) := by
    funext u
    rw [genericProjectivePhysicalProfile_mix_quadratic
      hf hfc hh hhc lam r u]
    ring
  rw [hpoint,
    integral_add (hff.add (hcross.const_mul lam)) (hhh.const_mul (lam^2)),
    integral_add hff (hcross.const_mul lam),
    integral_const_mul, integral_const_mul]
  ring

end Synthesis
