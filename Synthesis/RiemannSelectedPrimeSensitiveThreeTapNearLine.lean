import Synthesis.RiemannSelectedPrimeSensitiveThreeTapLocalBudget
import Synthesis.RiemannProjectiveQuarticTargetLocalSign

/-!
# Three-tap near-critical-line derivative coordinates

For the actual transformed signed projective profile P_eps define

  J2_eps = 1/4 * integral P_eps(u) u^2 du,
  J4_eps = 1/4 * integral P_eps(u) u^4 du.

The transformed pole-weighted same-ordinate target is exactly
-1/4 times the hyperbolic transform of P_eps.  Consequently its second and
fourth derivatives at the critical line are -J2_eps and -J4_eps.

This is the exact a->0 decision surface.  No vanishing or sign of J2_eps/J4_eps
is assumed.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def QuarticFourSignedPolePair.threeTapCombinedHeightDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps a : ℝ) : ℝ :=
  W.poleTwo *
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
        (W.threeTapHalf eps) (t/16) a 0
    +
  (-W.poleHalf) *
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
        (W.threeTapTwo eps) (t/16) a 0

theorem QuarticFourSignedPolePair.threeTapCombinedZeroHeightDefect_eq
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapCombinedZeroHeightDefect eps rho
      =
    ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.threeTapCombinedHeightDefect eps (heightOf rho) := by
  unfold QuarticFourSignedPolePair.threeTapCombinedZeroHeightDefect
    QuarticFourSignedPolePair.threeTapCombinedHeightDefect
    Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile.zeroHeightDefect
  ring

def QuarticFourSignedPolePair.threeTapSignedJ2
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  (1/4 : ℝ) *
    ∫ u : ℝ, W.threeTapSignedProjectiveProfile eps u * u^2

def QuarticFourSignedPolePair.threeTapSignedJ4
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  (1/4 : ℝ) *
    ∫ u : ℝ, W.threeTapSignedProjectiveProfile eps u * u^4

def QuarticFourSignedPolePair.threeTapCombinedHeightD1
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps a : ℝ) : ℝ :=
  -(1/4 : ℝ) *
    compactCoshD1 (W.threeTapSignedProjectiveProfile eps) a

def QuarticFourSignedPolePair.threeTapCombinedHeightD2
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps a : ℝ) : ℝ :=
  -(1/4 : ℝ) *
    compactCoshD2 (W.threeTapSignedProjectiveProfile eps) a

def QuarticFourSignedPolePair.threeTapCombinedHeightD3
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps a : ℝ) : ℝ :=
  -(1/4 : ℝ) *
    compactCoshD3 (W.threeTapSignedProjectiveProfile eps) a

def QuarticFourSignedPolePair.threeTapCombinedHeightD4
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps a : ℝ) : ℝ :=
  -(1/4 : ℝ) *
    compactCoshD4 (W.threeTapSignedProjectiveProfile eps) a

theorem QuarticFourSignedPolePair.threeTapCombinedHeightDefect_eq_cosh
    {t eps a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightDefect eps a
      =
    -(1/4 : ℝ) *
      compactCoshTransform (W.threeTapSignedProjectiveProfile eps) a := by
  have hhalf :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (W.threeTapProjectiveProfileHalf_continuous ht).1
      (detectorThreeTap_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t))
        eps (Real.log 2))
      (t/16) a
  have htwo :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (W.threeTapProjectiveProfileTwo_continuous ht).1
      (detectorThreeTap_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t))
        eps (Real.log 2))
      (t/16) a
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightDefect
    QuarticFourSignedPolePair.threeTapProjectiveProfileHalf at hhalf
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileTwo at htwo
  rw [hhalf, htwo]
  unfold compactCoshTransform
    QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
  have h1 :
      Integrable
        (fun u : ℝ =>
          W.threeTapProjectiveProfileHalf eps u * Real.cosh (a*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (W.threeTapProjectiveProfileHalf_compact ht).mul_right
  have h2 :
      Integrable
        (fun u : ℝ =>
          W.threeTapProjectiveProfileTwo eps u * Real.cosh (a*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (W.threeTapProjectiveProfileTwo_compact ht).mul_right
  rw [show
      (fun u : ℝ =>
        (W.poleTwo * W.threeTapProjectiveProfileHalf eps u
          + (-W.poleHalf) * W.threeTapProjectiveProfileTwo eps u)
          * Real.cosh (a*u))
      =
      fun u =>
        W.poleTwo *
          (W.threeTapProjectiveProfileHalf eps u * Real.cosh (a*u))
        + (-W.poleHalf) *
          (W.threeTapProjectiveProfileTwo eps u * Real.cosh (a*u)) by
      funext u
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.threeTapCombinedHeight_hasDerivAt
    {t eps a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapCombinedHeightDefect eps)
      (W.threeTapCombinedHeightD1 eps a) a := by
  rw [W.threeTapCombinedHeightDefect_eq_cosh ht]
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD1
  exact
    (compactCoshTransform_hasDerivAt
      (W.threeTapSignedProjectiveProfile_continuous ht)
      (W.threeTapSignedProjectiveProfile_compact ht) a).const_mul
      (-(1/4 : ℝ))

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD1_hasDerivAt
    {t eps a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapCombinedHeightD1 eps)
      (W.threeTapCombinedHeightD2 eps a) a := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD1
    QuarticFourSignedPolePair.threeTapCombinedHeightD2
  exact
    (compactCoshD1_deriv
      (W.threeTapSignedProjectiveProfile_continuous ht)
      (W.threeTapSignedProjectiveProfile_compact ht) a).const_mul
      (-(1/4 : ℝ))

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD2_hasDerivAt
    {t eps a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapCombinedHeightD2 eps)
      (W.threeTapCombinedHeightD3 eps a) a := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD2
    QuarticFourSignedPolePair.threeTapCombinedHeightD3
  exact
    (compactCoshD2_deriv
      (W.threeTapSignedProjectiveProfile_continuous ht)
      (W.threeTapSignedProjectiveProfile_compact ht) a).const_mul
      (-(1/4 : ℝ))

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD3_hasDerivAt
    {t eps a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapCombinedHeightD3 eps)
      (W.threeTapCombinedHeightD4 eps a) a := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD3
    QuarticFourSignedPolePair.threeTapCombinedHeightD4
  exact
    (compactCoshD3_deriv
      (W.threeTapSignedProjectiveProfile_continuous ht)
      (W.threeTapSignedProjectiveProfile_compact ht) a).const_mul
      (-(1/4 : ℝ))

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD2_zero_eq
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightD2 eps 0
      = - W.threeTapSignedJ2 eps := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD2
    QuarticFourSignedPolePair.threeTapSignedJ2
    compactCoshD2
  simp only [zero_mul, Real.cosh_zero, mul_one]
  ring

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD4_zero_eq
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightD4 eps 0
      = - W.threeTapSignedJ4 eps := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD4
    QuarticFourSignedPolePair.threeTapSignedJ4
    compactCoshD4
  simp only [zero_mul, Real.cosh_zero, mul_one]
  ring

/-- Near-line fork: if transformed J2 is nonzero then the target has a
nonzero second derivative at the line.  Quartic analysis is justified only
after proving J2_eps=0. -/
theorem QuarticFourSignedPolePair.threeTap_second_derivative_nonzero_iff_J2
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightD2 eps 0 ≠ 0
      ↔ W.threeTapSignedJ2 eps ≠ 0 := by
  rw [W.threeTapCombinedHeightD2_zero_eq]
  exact neg_ne_zero

end Synthesis
