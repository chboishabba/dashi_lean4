import Synthesis.RiemannProjectiveHeightBaseCurvatureDuality

/-!
# Fourth-order escape from the quadratic projective curvature lock

The exact quadratic duality shows that, for a fixed two-radius projective test,
the target-height quadratic coefficient and the q-kernel curvature have the
same sign.  Reversing one while retaining the other is impossible.

There is, however, a different algebraic possibility: cancel the common
quadratic moment and let the quartic term lead.

Write

  J4(g,r) = integral g(u) u^4 B_r(u) du,

where B_r is the exact two-radius projective bracket.  The coefficient of a^4
in the target height determinant D(a,0) is

  H4(g,r) = - J4(g,r) / 24,

whereas the coefficient of q^4 in the conventional physical q-kernel
4 integral g(u) B_r(u) cos(q u) du is

  K4(g,r) = J4(g,r) / 6 = -4 H4(g,r).

Thus, after imposing J2=0, the sign relation reverses relative to the desired
observables:

  J4 < 0  ==>  H4 > 0  and  K4 < 0.

This is the first moment-cancelled projective design criterion compatible with
a positive target signal and a locally negative base lobe.

The file proves only exact coefficient algebra.  Turning these coefficients
into punctured local signs requires the corresponding fourth-order Taylor
remainder theorem and is kept as the next analytic layer.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-- u^4-weighted on-line cosine response. -/
def projectiveFourthEvenResp (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u^4 * Real.cos (s*u)

/-- Signed fourth moment of the exact two-radius projective bracket. -/
def projectiveBracketFourthMoment
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u^4 * twoRadiusBracket g r u

/-- Coefficient of a^4 in the formal height expansion of D(a,0). -/
def projectiveHeightQuarticCoeff
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1/24 : ℝ) *
    (projectiveFourthEvenResp g r * evenResp g 0 (2*r)
      - projectiveFourthEvenResp g (2*r) * evenResp g 0 r)

/-- Coefficient of q^4 in 4 integral g B_r cos(q u). -/
def projectiveBaseQuarticCoeff
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1/6 : ℝ) * projectiveBracketFourthMoment g r

theorem projectiveBracketFourthMoment_eq_response_det
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveBracketFourthMoment g r
      =
    evenResp g 0 r * projectiveFourthEvenResp g (2*r)
      - evenResp g 0 (2*r) * projectiveFourthEvenResp g r := by
  let f2 : ℝ → ℝ := fun u =>
    g u * u^4 * Real.cos ((2*r)*u)
  let f1 : ℝ → ℝ := fun u =>
    g u * u^4 * Real.cos (r*u)
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
  unfold projectiveBracketFourthMoment twoRadiusBracket
  have hpoint :
      (fun u : ℝ =>
        g u * u^4 *
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
  unfold projectiveFourthEvenResp
  rfl

/-- Exact fourth-order height coefficient identity. -/
theorem projectiveHeightQuarticCoeff_eq_neg_one_div_24_fourthMoment
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveHeightQuarticCoeff g r
      =
    -(1/24 : ℝ) * projectiveBracketFourthMoment g r := by
  rw [projectiveBracketFourthMoment_eq_response_det hg hgc r]
  unfold projectiveHeightQuarticCoeff
  ring

/-- Exact fourth-order height/base coefficient duality. -/
theorem projectiveBaseQuarticCoeff_eq_neg_four_heightQuarticCoeff
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    projectiveBaseQuarticCoeff g r
      =
    -4 * projectiveHeightQuarticCoeff g r := by
  rw [projectiveHeightQuarticCoeff_eq_neg_one_div_24_fourthMoment hg hgc r]
  unfold projectiveBaseQuarticCoeff
  ring

/--
Moment-cancelled quartic design criterion.

Once the shared quadratic moment has been cancelled, a negative fourth
projective moment points in exactly the useful directions: positive target
quartic coefficient and negative base quartic coefficient.
-/
theorem quartic_escape_signs
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    projectiveHeightQuadraticCoeff g r = 0
      ∧ 0 < projectiveHeightQuarticCoeff g r
      ∧ projectiveBaseCurvatureCoeff g r = 0
      ∧ projectiveBaseQuarticCoeff g r < 0 := by
  have hH2 :=
    projectiveHeightQuadraticCoeff_eq_neg_half_secondMoment hg hgc r
  have hK2 :=
    projectiveBaseCurvatureCoeff_eq_eight_heightQuadraticCoeff hg hgc r
  have hH4 :=
    projectiveHeightQuarticCoeff_eq_neg_one_div_24_fourthMoment hg hgc r
  have hK4 :=
    projectiveBaseQuarticCoeff_eq_neg_four_heightQuarticCoeff hg hgc r
  constructor
  · rw [hH2, hJ2]
    norm_num
  constructor
  · rw [hH4]
    nlinarith
  constructor
  · rw [hK2, hH2, hJ2]
    norm_num
  · rw [hK4]
    have : 0 < projectiveHeightQuarticCoeff g r := by
      rw [hH4]
      nlinarith
    nlinarith

/--
The quartic escape genuinely leaves the old GateData class: a nondegenerate
radial GateData can never satisfy J2=0 because its second projective moment is
strictly negative.
-/
theorem GateData.not_secondMoment_zero
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate.GateData
      g t r Lambda) :
    projectiveBracketSecondMoment g r ≠ 0 := by
  intro hzero
  have hneg := hd.projective_u_sq_covariance_neg
  unfold projectiveBracketSecondMoment at hzero
  rw [hzero] at hneg
  linarith

end Synthesis
