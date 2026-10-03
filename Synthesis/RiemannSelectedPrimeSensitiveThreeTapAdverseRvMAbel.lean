import Synthesis.RiemannSelectedPrimeSensitiveThreeTapKernelAdverseLipschitz

/-!
# Literal RvM / Abel attachment for the transformed adverse ordinate envelope

Let r=t/16.  After paying a horizontal strip bound, each adverse pair is
majorized by the ordinate-only test

  phi_eps,A,t(x)
    = r^-2 * AdverseEnvelope_eps,A((x-t)/r).

The normalized envelope is globally Lipschitz with mass L_eps,A, hence this
physical test is globally Lipschitz with mass L_eps,A/r^3.  It is therefore
absolutely continuous and may be inserted into the exact AC N-mu Abel theorem.

This file is the requested same-object bridge from the sign-preserving pair
cut to the literal Riemann-von Mangoldt discrepancy.  No discrepancy estimate
or final sign is asserted.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators NNReal Interval

/-- Physical-ordinate adverse test, including the exact projective r^-2
coefficient from each reflection pair. -/
def QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A x : ℝ) : ℝ :=
  (1/(t/16)^2)
    * W.threeTapKernelAdverseAlphaEnvelope eps A ((x-t)/(t/16))

theorem QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest_nonneg
    {t eps A x : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapAdversePhysicalOrdinateTest eps A x := by
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest
  exact mul_nonneg (by positivity)
    W.threeTapKernelAdverseAlphaEnvelope_nonneg

/-- Explicit physical Lipschitz mass after q=(x-t)/r and the r^-2 pair
normalization. -/
def QuarticFourSignedPolePair.threeTapAdversePhysicalLipschitzMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A : ℝ) : ℝ :=
  W.threeTapKernelAdverseAlphaLipschitzMass eps A / (t/16)^3

theorem QuarticFourSignedPolePair.threeTapAdversePhysicalLipschitzMass_nonneg
    {t eps A : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapAdversePhysicalLipschitzMass eps A := by
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalLipschitzMass
  exact div_nonneg W.threeTapKernelAdverseAlphaLipschitzMass_nonneg
    (by positivity)

theorem QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest_sub_abs_le
    {t eps A x y : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    |W.threeTapAdversePhysicalOrdinateTest eps A x
      - W.threeTapAdversePhysicalOrdinateTest eps A y|
      <=
    W.threeTapAdversePhysicalLipschitzMass eps A * |x-y| := by
  let r : ℝ := t/16
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have henv :=
    W.threeTapKernelAdverseAlphaEnvelope_sub_abs_le
      (eps:=eps) (A:=A)
      (q1:=(x-t)/r) (q2:=(y-t)/r)
  have hq : |(x-t)/r - (y-t)/r| = |x-y|/r := by
    rw [show (x-t)/r - (y-t)/r = (x-y)/r by field_simp [hr0]; ring]
    rw [abs_div, abs_of_pos hr]
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest
    QuarticFourSignedPolePair.threeTapAdversePhysicalLipschitzMass
  change
    |(1/r^2) * W.threeTapKernelAdverseAlphaEnvelope eps A ((x-t)/r)
      - (1/r^2) * W.threeTapKernelAdverseAlphaEnvelope eps A ((y-t)/r)|
      <=
    W.threeTapKernelAdverseAlphaLipschitzMass eps A / r^3 * |x-y|
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 <= (1/r^2 : ℝ))]
  rw [hq] at henv
  have hscaled := mul_le_mul_of_nonneg_left henv
    (by positivity : 0 <= (1/r^2 : ℝ))
  calc
    (1/r^2) *
      |W.threeTapKernelAdverseAlphaEnvelope eps A ((x-t)/r)
        - W.threeTapKernelAdverseAlphaEnvelope eps A ((y-t)/r)|
      <=
    (1/r^2) *
      (W.threeTapKernelAdverseAlphaLipschitzMass eps A * (|x-y|/r)) :=
        hscaled
    _ = W.threeTapKernelAdverseAlphaLipschitzMass eps A / r^3 * |x-y| := by
        field_simp [hr0]
        ring

/-- Global physical-coordinate Lipschitz regularity. -/
theorem QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest_lipschitz
    {t eps A : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    LipschitzWith
      ⟨W.threeTapAdversePhysicalLipschitzMass eps A,
        W.threeTapAdversePhysicalLipschitzMass_nonneg ht⟩
      (W.threeTapAdversePhysicalOrdinateTest eps A) := by
  intro x y
  simpa [Real.dist_eq] using
    W.threeTapAdversePhysicalOrdinateTest_sub_abs_le
      ht (eps:=eps) (A:=A) (x:=x) (y:=y)

theorem QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest_ac
    {t eps A a b : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    AbsolutelyContinuousOnInterval
      (W.threeTapAdversePhysicalOrdinateTest eps A) a b := by
  exact
    (W.threeTapAdversePhysicalOrdinateTest_lipschitz
      ht (eps:=eps) (A:=A)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval

/-- Exact N-mu Abel identity for the physical adverse-envelope test on a
symmetric finite ordinate window. -/
theorem QuarticFourSignedPolePair.threeTapAdverseWindowMinusMu_eq_discrepancyAbel
    {t eps A R : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hR : 0 <= R) :
    zetaWindowMinusMuPair (t-R) (t+R)
      (W.threeTapAdversePhysicalOrdinateTest eps A)
      =
    W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
      * zetaMuCumulativeDiscrepancy (t-R) (t+R)
      -
    ∫ x in (t-R)..(t+R),
      deriv (W.threeTapAdversePhysicalOrdinateTest eps A) x
        * zetaMuCumulativeDiscrepancy (t-R) x := by
  exact zetaWindowMinusMuPair_eq_discrepancyAbel_ac
    (by linarith)
    (W.threeTapAdversePhysicalOrdinateTest_ac ht)

/-- Expanded weighted-zero form: the finite adverse majorant carrier is an
explicit smooth-density term plus one boundary discrepancy and one AC Abel
remainder. -/
theorem QuarticFourSignedPolePair.threeTapAdverseWindowPair_eq_mu_add_discrepancyAbel
    {t eps A R : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hR : 0 <= R) :
    zetaWindowWeightedPair (t-R) (t+R)
      (W.threeTapAdversePhysicalOrdinateTest eps A)
      =
    (∫ x in (t-R)..(t+R),
      W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x)
      +
    W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
      * zetaMuCumulativeDiscrepancy (t-R) (t+R)
      -
    ∫ x in (t-R)..(t+R),
      deriv (W.threeTapAdversePhysicalOrdinateTest eps A) x
        * zetaMuCumulativeDiscrepancy (t-R) x := by
  have h := W.threeTapAdverseWindowMinusMu_eq_discrepancyAbel
    ht (eps:=eps) (A:=A) hR
  unfold zetaWindowMinusMuPair at h
  linarith

end Synthesis
