import Synthesis.RiemannSelectedPrimeSensitiveThreeTapKernelAlphaEnvelope
import Synthesis.RiemannZetaMuAbsolutelyContinuousAbel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Lipschitz / AC regularity of the sign-preserving adverse ordinate envelope

The adverse alpha envelope contains a positive-part phase cut.  It is generally
not C1 at phase crossings, but it is globally Lipschitz in the normalized
ordinate q.  The explicit Lipschitz mass is

  L_eps,A = integral cosh(A|v|) |P_eps(v)| |v| dv.

Indeed positive-part is 1-Lipschitz and cosine is 1-Lipschitz.  Therefore

  |AdverseEnvelope(q1) - AdverseEnvelope(q2)|
    <= L_eps,A |q1-q2|.

This proves the exact regularity class needed by the AC N-mu Abel theorem,
without smoothing the adverse phase boundary or taking an absolute value of
the original signed zero sum.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators NNReal

/-- The scalar positive-part formula used by the adverse cuts is 1-Lipschitz. -/
theorem half_add_abs_lipschitz
    (x y : ℝ) :
    |(x + |x|)/2 - (y + |y|)/2| <= |x-y| := by
  have habs : ||x| - |y|| <= |x-y| :=
    abs_abs_sub_abs_le_abs_sub x y
  have hadd :
      |(x-y) + (|x|-|y|)|
        <= |x-y| + ||x|-|y|| := abs_add _ _
  have htwo : (0 : ℝ) < 2 := by norm_num
  calc
    |(x + |x|)/2 - (y + |y|)/2|
      = |((x-y) + (|x|-|y|))/2| := by
          congr 1
          ring
    _ = |(x-y) + (|x|-|y|)| / 2 := by
          rw [abs_div, abs_of_pos htwo]
    _ <= (|x-y| + ||x|-|y||) / 2 := by
          exact div_le_div_of_nonneg_right hadd htwo.le
    _ <= |x-y| := by linarith

/-- Pointwise phase-positive part is Lipschitz in q with weight |P(v)| |v|. -/
theorem QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart_sub_abs_le
    {t eps q1 q2 v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    |W.threeTapKernelPhaseAdversePart eps q1 v
      - W.threeTapKernelPhaseAdversePart eps q2 v|
      <=
    |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |v| * |q1-q2| := by
  have hpos := half_add_abs_lipschitz
    (W.threeTapKernelPhaseCore eps q1 v)
    (W.threeTapKernelPhaseCore eps q2 v)
  have hcos := Real.abs_cos_sub_cos_le (q1*v) (q2*v)
  calc
    |W.threeTapKernelPhaseAdversePart eps q1 v
      - W.threeTapKernelPhaseAdversePart eps q2 v|
      <=
    |W.threeTapKernelPhaseCore eps q1 v
      - W.threeTapKernelPhaseCore eps q2 v| := by
        simpa [QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart]
          using hpos
    _ =
    |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |Real.cos (q1*v) - Real.cos (q2*v)| := by
        unfold QuarticFourSignedPolePair.threeTapKernelPhaseCore
        rw [← mul_sub, abs_mul]
    _ <=
    |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |q1*v-q2*v| :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ =
    |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |v| * |q1-q2| := by
        rw [show q1*v-q2*v = (q1-q2)*v by ring, abs_mul]
        ring

/-- Explicit global Lipschitz mass of the adverse ordinate envelope. -/
def QuarticFourSignedPolePair.threeTapKernelAdverseAlphaLipschitzMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A : ℝ) : ℝ :=
  ∫ v : ℝ,
    Real.cosh (A*|v|)
      * |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |v|

theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaLipschitzMass_nonneg
    {t eps A : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelAdverseAlphaLipschitzMass eps A := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaLipschitzMass
  exact integral_nonneg fun v => by positivity

theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaLipschitzMass_integrable
    {t eps A : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun v : ℝ =>
        Real.cosh (A*|v|)
          * |W.threeTapNormalizedSignedProjectiveProfile eps v|
          * |v|) := by
  exact Continuous.integrable_of_hasCompactSupport
    (by fun_prop)
    ((W.threeTapNormalizedProjective_compact (eps:=eps)).abs.mul_left.mul_right)

/-- Explicit global Lipschitz estimate in the normalized ordinate q. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_sub_abs_le
    {t eps A q1 q2 : ℝ}
    (W : QuarticFourSignedPolePair t) :
    |W.threeTapKernelAdverseAlphaEnvelope eps A q1
      - W.threeTapKernelAdverseAlphaEnvelope eps A q2|
      <=
    W.threeTapKernelAdverseAlphaLipschitzMass eps A * |q1-q2| := by
  let F1 : ℝ → ℝ := fun v =>
    Real.cosh (A*|v|) * W.threeTapKernelPhaseAdversePart eps q1 v
  let F2 : ℝ → ℝ := fun v =>
    Real.cosh (A*|v|) * W.threeTapKernelPhaseAdversePart eps q2 v
  let M : ℝ → ℝ := fun v =>
    Real.cosh (A*|v|)
      * |W.threeTapNormalizedSignedProjectiveProfile eps v|
      * |v| * |q1-q2|
  have hF1 : Integrable F1 := by
    dsimp [F1]
    exact W.threeTapKernelAdverseAlphaEnvelope_integrable
  have hF2 : Integrable F2 := by
    dsimp [F2]
    exact W.threeTapKernelAdverseAlphaEnvelope_integrable
  have hM : Integrable M := by
    dsimp [M]
    exact (W.threeTapKernelAdverseAlphaLipschitzMass_integrable
      (eps:=eps) (A:=A)).mul_const _
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope
  rw [← integral_sub hF1 hF2]
  calc
    |∫ v : ℝ, F1 v - F2 v|
      <= ∫ v : ℝ, |F1 v - F2 v| := abs_integral_le_integral_abs
    _ <= ∫ v : ℝ, M v := by
      apply integral_mono (hF1.sub hF2).abs hM
      intro v
      dsimp [F1,F2,M]
      have hc : 0 <= Real.cosh (A*|v|) := (Real.cosh_pos _).le
      rw [← mul_sub, abs_mul, abs_of_nonneg hc]
      have hp := W.threeTapKernelPhaseAdversePart_sub_abs_le
        (eps:=eps) (q1:=q1) (q2:=q2) (v:=v)
      exact mul_le_mul_of_nonneg_left hp hc
    _ =
      W.threeTapKernelAdverseAlphaLipschitzMass eps A * |q1-q2| := by
      dsimp [M]
      rw [integral_mul_const]
      rfl

/-- Global Lipschitz regularity of the sign-preserving adverse envelope. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_lipschitz
    {t eps A : ℝ}
    (W : QuarticFourSignedPolePair t) :
    LipschitzWith
      ⟨W.threeTapKernelAdverseAlphaLipschitzMass eps A,
        W.threeTapKernelAdverseAlphaLipschitzMass_nonneg⟩
      (W.threeTapKernelAdverseAlphaEnvelope eps A) := by
  intro q1 q2
  simpa [Real.dist_eq] using
    W.threeTapKernelAdverseAlphaEnvelope_sub_abs_le
      (eps:=eps) (A:=A) (q1:=q1) (q2:=q2)

/-- Hence the adverse ordinate envelope is absolutely continuous on every
finite interval and is admissible for the AC literal N-mu Abel theorem. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_ac
    {t eps A a b : ℝ}
    (W : QuarticFourSignedPolePair t) :
    AbsolutelyContinuousOnInterval
      (W.threeTapKernelAdverseAlphaEnvelope eps A) a b := by
  exact
    (W.threeTapKernelAdverseAlphaEnvelope_lipschitz
      (eps:=eps) (A:=A)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval

end Synthesis
