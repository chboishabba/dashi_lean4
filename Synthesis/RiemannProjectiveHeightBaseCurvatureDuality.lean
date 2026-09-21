import Synthesis.RiemannProjectiveCurvatureRadialGateNoGo

/-!
# Fixed-radius height/base curvature duality

There is an exact algebraic duality behind the Goal-1 curvature obstruction.

For a taper g and sampling radius r, write

  S_g(s) = integral g(u) u^2 cos(su) du.

The quadratic coefficient of the target height determinant at a=0 is

  H2(g,r)
    = 1/2 * (S_g(r) A0(2r) - S_g(2r) A0(r)).

The signed second moment of the projective bracket is

  J2(g,r)
    = integral g(u) u^2 B_r(u) du
    = A0(r) S_g(2r) - A0(2r) S_g(r).

Therefore, exactly,

  H2(g,r) = - J2(g,r) / 2.

The q-only projective cosine kernel with the conventional factor 4 has formal
curvature coefficient

  K2(g,r) = -4 J2(g,r) = 8 H2(g,r).

So the quadratic target detector and the local q-curvature are not independent
design knobs: they are the same fixed-radius second-moment determinant.

Under GateData the radial covariance theorem forces J2<0, hence both H2 and K2
are strictly positive.

This is not an asymptotic explicit-formula identity; it is an exact algebraic
identity at the chosen sampling radius.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-- u^2-weighted on-line cosine response. -/
def projectiveSqEvenResp (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u^2 * Real.cos (s*u)

/-- Exact quadratic coefficient in the horizontal-height variable at a=0. -/
def projectiveHeightQuadraticCoeff
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (projectiveSqEvenResp g r * evenResp g 0 (2*r)
      - projectiveSqEvenResp g (2*r) * evenResp g 0 r)

/-- Signed second moment of the exact projective bracket. -/
def projectiveBracketSecondMoment
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u^2 * twoRadiusBracket g r u

/-- Conventional q-kernel curvature coefficient for the physical factor 4. -/
def projectiveBaseCurvatureCoeff
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  -4 * projectiveBracketSecondMoment g r

theorem projectiveBracketSecondMoment_eq_response_det
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveBracketSecondMoment g r
      =
    evenResp g 0 r * projectiveSqEvenResp g (2*r)
      - evenResp g 0 (2*r) * projectiveSqEvenResp g r := by
  let f2 : ℝ → ℝ := fun u =>
    g u * u^2 * Real.cos ((2*r)*u)
  let f1 : ℝ → ℝ := fun u =>
    g u * u^2 * Real.cos (r*u)
  have hf2 : Integrable f2 := by
    dsimp [f2]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((hgc.mul_right).mul_right)
  have hf1 : Integrable f1 := by
    dsimp [f1]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((hgc.mul_right).mul_right)
  unfold projectiveBracketSecondMoment
  unfold twoRadiusBracket
  have hpoint :
      (fun u : ℝ =>
        g u * u^2 *
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
  unfold projectiveSqEvenResp
  rfl

/--
Exact fixed-radius duality:
  height quadratic coefficient = -1/2 * projective second moment.
-/
theorem projectiveHeightQuadraticCoeff_eq_neg_half_secondMoment
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveHeightQuadraticCoeff g r
      =
    -(1/2 : ℝ) * projectiveBracketSecondMoment g r := by
  rw [projectiveBracketSecondMoment_eq_response_det hg hgc r]
  unfold projectiveHeightQuadraticCoeff
  ring

/--
The conventional q-curvature coefficient is exactly eight times the target
height-quadratic coefficient.
-/
theorem projectiveBaseCurvatureCoeff_eq_eight_heightQuadraticCoeff
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveBaseCurvatureCoeff g r
      = 8 * projectiveHeightQuadraticCoeff g r := by
  rw [projectiveHeightQuadraticCoeff_eq_neg_half_secondMoment hg hgc r]
  unfold projectiveBaseCurvatureCoeff
  ring

/--
GateData forces the target's exact horizontal quadratic coefficient to be
strictly positive.
-/
theorem GateData.projectiveHeightQuadraticCoeff_pos
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : GateData g t r Lambda) :
    0 < projectiveHeightQuadraticCoeff g r := by
  rw [projectiveHeightQuadraticCoeff_eq_neg_half_secondMoment
    hd.smooth.continuous hd.compactSupport r]
  have hJ := hd.projective_u_sq_covariance_neg
  unfold projectiveBracketSecondMoment
  linarith

/--
The same GateData therefore forces positive q-curvature coefficient.
-/
theorem GateData.projectiveBaseCurvatureCoeff_pos
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : GateData g t r Lambda) :
    0 < projectiveBaseCurvatureCoeff g r := by
  rw [projectiveBaseCurvatureCoeff_eq_eight_heightQuadraticCoeff
    hd.smooth.continuous hd.compactSupport r]
  have hH := hd.projectiveHeightQuadraticCoeff_pos
  positivity

/--
Within GateData, a positive target quadratic detector and a negative local
q-curvature cannot be independently engineered: both signs are forced in the
same direction by the exact second-moment determinant.
-/
theorem GateData.not_projectiveBaseCurvatureCoeff_nonpos
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : GateData g t r Lambda) :
    ¬ projectiveBaseCurvatureCoeff g r ≤ 0 := by
  linarith [hd.projectiveBaseCurvatureCoeff_pos]

end Synthesis
