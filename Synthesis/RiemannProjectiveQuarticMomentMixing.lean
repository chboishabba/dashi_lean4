import Synthesis.RiemannProjectiveQuarticTargetLocalSign

/-!
# Exact moment mixing algebra for quartic-escape projective tapers

To build an actual quartic-escape detector, mix two compact profiles

  g_lambda = f + lambda h.

For each even moment order used by the projective determinant, the projective
moment is quadratic in lambda because the two-radius bracket is linear in the
profile and is paired once more against the profile.

This file makes that algebra exact for J2 and J4:

  Jk(f + lambda h)
    = Jk(f) + lambda Cross_k(f,h) + lambda^2 Jk(h).

Consequently J2=0 is an ordinary quadratic equation.  When the discriminant is
nonnegative and J2(h) != 0, the standard quadratic roots give literal
moment-cancelled tapers.  The remaining design question is then only the sign of
J4 at one of those roots.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def projectiveMixedTaper
    (f h : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  fun u => f u + lam * h u

private theorem evenResp_zero_mix
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam s : ℝ) :
    evenResp (projectiveMixedTaper f h lam) 0 s
      = evenResp f 0 s + lam * evenResp h 0 s := by
  unfold evenResp projectiveMixedTaper
  simp only [zero_mul, Real.cosh_zero, one_mul]
  have hfi : Integrable (fun u : ℝ => f u * Real.cos (s*u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hhi : Integrable (fun u : ℝ => h u * Real.cos (s*u)) :=
    (hh.mul (by fun_prop)).integrable_of_hasCompactSupport hhc.mul_right
  have hpoint :
      (fun u : ℝ => (f u + lam*h u) * Real.cos (s*u))
        =
      (fun u : ℝ => f u * Real.cos (s*u)
        + lam * (h u * Real.cos (s*u))) := by
    funext u
    ring
  rw [hpoint, integral_add hfi (hhi.const_mul lam), integral_const_mul]

private theorem projectiveSqEvenResp_mix
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam s : ℝ) :
    projectiveSqEvenResp (projectiveMixedTaper f h lam) s
      =
    projectiveSqEvenResp f s + lam * projectiveSqEvenResp h s := by
  unfold projectiveSqEvenResp projectiveMixedTaper
  have hfi : Integrable
      (fun u : ℝ => f u * u^2 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hfc.mul_right).mul_right)
  have hhi : Integrable
      (fun u : ℝ => h u * u^2 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hhc.mul_right).mul_right)
  have hpoint :
      (fun u : ℝ => (f u + lam*h u) * u^2 * Real.cos (s*u))
        =
      (fun u : ℝ => f u * u^2 * Real.cos (s*u)
        + lam * (h u * u^2 * Real.cos (s*u))) := by
    funext u
    ring
  rw [hpoint, integral_add hfi (hhi.const_mul lam), integral_const_mul]

private theorem projectiveFourthEvenResp_mix
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam s : ℝ) :
    projectiveFourthEvenResp (projectiveMixedTaper f h lam) s
      =
    projectiveFourthEvenResp f s + lam * projectiveFourthEvenResp h s := by
  unfold projectiveFourthEvenResp projectiveMixedTaper
  have hfi : Integrable
      (fun u : ℝ => f u * u^4 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hfc.mul_right).mul_right)
  have hhi : Integrable
      (fun u : ℝ => h u * u^4 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hhc.mul_right).mul_right)
  have hpoint :
      (fun u : ℝ => (f u + lam*h u) * u^4 * Real.cos (s*u))
        =
      (fun u : ℝ => f u * u^4 * Real.cos (s*u)
        + lam * (h u * u^4 * Real.cos (s*u))) := by
    funext u
    ring
  rw [hpoint, integral_add hfi (hhi.const_mul lam), integral_const_mul]

def projectiveSecondMomentCross
    (f h : ℝ → ℝ) (r : ℝ) : ℝ :=
  evenResp f 0 r * projectiveSqEvenResp h (2*r)
    + evenResp h 0 r * projectiveSqEvenResp f (2*r)
    - evenResp f 0 (2*r) * projectiveSqEvenResp h r
    - evenResp h 0 (2*r) * projectiveSqEvenResp f r

def projectiveFourthMomentCross
    (f h : ℝ → ℝ) (r : ℝ) : ℝ :=
  evenResp f 0 r * projectiveFourthEvenResp h (2*r)
    + evenResp h 0 r * projectiveFourthEvenResp f (2*r)
    - evenResp f 0 (2*r) * projectiveFourthEvenResp h r
    - evenResp h 0 (2*r) * projectiveFourthEvenResp f r

theorem projectiveBracketSecondMoment_mix_quadratic
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r : ℝ) :
    projectiveBracketSecondMoment (projectiveMixedTaper f h lam) r
      =
    projectiveBracketSecondMoment f r
      + lam * projectiveSecondMomentCross f h r
      + lam^2 * projectiveBracketSecondMoment h r := by
  rw [projectiveBracketSecondMoment_eq_response_det
      (hf.add (continuous_const.mul hh))
      (hfc.add hhc.mul_left) r,
    projectiveBracketSecondMoment_eq_response_det hf hfc r,
    projectiveBracketSecondMoment_eq_response_det hh hhc r]
  rw [evenResp_zero_mix hf hfc hh hhc lam r,
      evenResp_zero_mix hf hfc hh hhc lam (2*r),
      projectiveSqEvenResp_mix hf hfc hh hhc lam r,
      projectiveSqEvenResp_mix hf hfc hh hhc lam (2*r)]
  unfold projectiveSecondMomentCross
  ring

theorem projectiveBracketFourthMoment_mix_quadratic
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r : ℝ) :
    projectiveBracketFourthMoment (projectiveMixedTaper f h lam) r
      =
    projectiveBracketFourthMoment f r
      + lam * projectiveFourthMomentCross f h r
      + lam^2 * projectiveBracketFourthMoment h r := by
  rw [projectiveBracketFourthMoment_eq_response_det
      (hf.add (continuous_const.mul hh))
      (hfc.add hhc.mul_left) r,
    projectiveBracketFourthMoment_eq_response_det hf hfc r,
    projectiveBracketFourthMoment_eq_response_det hh hhc r]
  rw [evenResp_zero_mix hf hfc hh hhc lam r,
      evenResp_zero_mix hf hfc hh hhc lam (2*r),
      projectiveFourthEvenResp_mix hf hfc hh hhc lam r,
      projectiveFourthEvenResp_mix hf hfc hh hhc lam (2*r)]
  unfold projectiveFourthMomentCross
  ring

def projectiveSecondMomentDiscriminant
    (f h : ℝ → ℝ) (r : ℝ) : ℝ :=
  (projectiveSecondMomentCross f h r)^2
    - 4 * projectiveBracketSecondMoment h r
        * projectiveBracketSecondMoment f r

def projectiveSecondMomentRootPlus
    (f h : ℝ → ℝ) (r : ℝ) : ℝ :=
  (- projectiveSecondMomentCross f h r
      + Real.sqrt (projectiveSecondMomentDiscriminant f h r))
    / (2 * projectiveBracketSecondMoment h r)

def projectiveSecondMomentRootMinus
    (f h : ℝ → ℝ) (r : ℝ) : ℝ :=
  (- projectiveSecondMomentCross f h r
      - Real.sqrt (projectiveSecondMomentDiscriminant f h r))
    / (2 * projectiveBracketSecondMoment h r)

private theorem secondMoment_quadratic_root
    {A B C : ℝ}
    (hA : A ≠ 0)
    (hdisc : 0 ≤ B^2 - 4*A*C) :
    A * ((-B + Real.sqrt (B^2 - 4*A*C)) / (2*A))^2
      + B * ((-B + Real.sqrt (B^2 - 4*A*C)) / (2*A))
      + C = 0 := by
  have hs := Real.sq_sqrt hdisc
  field_simp [hA]
  nlinarith

theorem projectiveSecondMomentRootPlus_cancels
    {f h : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    {r : ℝ}
    (hJh : projectiveBracketSecondMoment h r ≠ 0)
    (hdisc : 0 ≤ projectiveSecondMomentDiscriminant f h r) :
    projectiveBracketSecondMoment
      (projectiveMixedTaper f h (projectiveSecondMomentRootPlus f h r)) r = 0 := by
  rw [projectiveBracketSecondMoment_mix_quadratic
      hf hfc hh hhc (projectiveSecondMomentRootPlus f h r) r]
  unfold projectiveSecondMomentRootPlus projectiveSecondMomentDiscriminant
  have hroot := secondMoment_quadratic_root
    (A := projectiveBracketSecondMoment h r)
    (B := projectiveSecondMomentCross f h r)
    (C := projectiveBracketSecondMoment f r)
    hJh hdisc
  linarith

end Synthesis
