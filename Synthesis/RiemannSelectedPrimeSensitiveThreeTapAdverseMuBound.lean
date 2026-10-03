import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseRvMBound

/-!
# Explicit smooth-mu budget for the transformed adverse finite core

The finite adverse RvM compiler retains one smooth term

  integral phi_eps,A,t(x) * mu(x) dx.

This file bounds it without touching the signed zero carrier.  Since

  phaseAdversePart(P(v) cos(qv)) <= |P(v)|

and cosh is positive, the normalized adverse envelope is uniformly bounded by

  S_eps,A = integral cosh(A|v|) |P_eps(v)| dv.

Thus the physical test is at most S_eps,A/r^2.  Combining this with the
existing theorem-bearing bound `|mu(x)| <= C_mu log(x+3)` gives an explicit
finite-window smooth-density budget.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Uniform mass controlling the adverse normalized envelope for every q. -/
def QuarticFourSignedPolePair.threeTapKernelAdverseAlphaSupMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A : ℝ) : ℝ :=
  ∫ v : ℝ,
    Real.cosh (A*|v|)
      * |W.threeTapNormalizedSignedProjectiveProfile eps v|

theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaSupMass_nonneg
    {t eps A : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelAdverseAlphaSupMass eps A := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaSupMass
  exact integral_nonneg fun v => by positivity

/-- Positive phase part never exceeds the profile magnitude. -/
theorem QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart_le_profileAbs
    {t eps q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelPhaseAdversePart eps q v
      <= |W.threeTapNormalizedSignedProjectiveProfile eps v| := by
  unfold QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
    QuarticFourSignedPolePair.threeTapKernelPhaseCore
  by_cases h :
      0 <= W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v)
  · rw [abs_of_nonneg h]
    have hc : |Real.cos (q*v)| <= 1 := Real.abs_cos_le_one _
    have hp :
        W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v)
          <=
        |W.threeTapNormalizedSignedProjectiveProfile eps v|
          * |Real.cos (q*v)| := by
      calc
        W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v)
          <= |W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v)| :=
            le_abs_self _
        _ = |W.threeTapNormalizedSignedProjectiveProfile eps v|
            * |Real.cos (q*v)| := abs_mul _ _
    calc
      (W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v)
          + W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v))/2
        = W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v) := by ring
      _ <= |W.threeTapNormalizedSignedProjectiveProfile eps v|
          * |Real.cos (q*v)| := hp
      _ <= |W.threeTapNormalizedSignedProjectiveProfile eps v| * 1 :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = _ := by ring
  · have h' :
      W.threeTapNormalizedSignedProjectiveProfile eps v * Real.cos (q*v) <= 0 :=
      le_of_not_ge h
    rw [abs_of_nonpos h']
    simp

/-- Uniform-in-q adverse envelope bound. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_le_supMass
    {t eps A q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelAdverseAlphaEnvelope eps A q
      <= W.threeTapKernelAdverseAlphaSupMass eps A := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope
    QuarticFourSignedPolePair.threeTapKernelAdverseAlphaSupMass
  have hleft := W.threeTapKernelAdverseAlphaEnvelope_integrable
    (eps:=eps) (A:=A) (q:=q)
  have hright :
      Integrable
        (fun v : ℝ =>
          Real.cosh (A*|v|)
            * |W.threeTapNormalizedSignedProjectiveProfile eps v|) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((W.threeTapNormalizedProjective_compact (eps:=eps)).abs.mul_left)
  apply integral_mono hleft hright
  intro v
  exact mul_le_mul_of_nonneg_left
    W.threeTapKernelPhaseAdversePart_le_profileAbs
    (Real.cosh_pos _).le

/-- Uniform physical-test bound after the projective r^-2 scaling. -/
theorem QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest_le_supMass
    {t eps A x : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdversePhysicalOrdinateTest eps A x
      <=
    (1/(t/16)^2) * W.threeTapKernelAdverseAlphaSupMass eps A := by
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest
  exact mul_le_mul_of_nonneg_left
    W.threeTapKernelAdverseAlphaEnvelope_le_supMass (by positivity)

/-- Existing Gamma/RvM density theory gives a fully explicit upper budget for
the smooth mu contribution on every high positive finite window. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdverseMuMass_bound :
    ∃ Cmu : ℝ, 0 <= Cmu ∧
      ∀ {t eps A R : ℝ},
        0 < t ->
        0 <= R ->
        1 <= t-R ->
        ∀ W : QuarticFourSignedPolePair t,
        W.threeTapAdverseMuMass eps A R
          <=
        (2*R)
          * ((1/(t/16)^2) * W.threeTapKernelAdverseAlphaSupMass eps A)
          * (Cmu * Real.log ((t+R)+3)) := by
  obtain ⟨Cmu,hCmu0,hmu⟩ := Zeta23.RvM.mu_le_log Zeta23.gammaFacts
  refine ⟨Cmu,hCmu0.le,?_⟩
  intro t eps A R ht hR hleft W
  let M : ℝ :=
    (1/(t/16)^2) * W.threeTapKernelAdverseAlphaSupMass eps A
  let U : ℝ := Cmu * Real.log ((t+R)+3)
  have hM : 0 <= M := by
    dsimp [M]
    exact mul_nonneg (by positivity)
      W.threeTapKernelAdverseAlphaSupMass_nonneg
  have hU : 0 <= U := by
    dsimp [U]
    exact mul_nonneg hCmu0.le (Real.log_nonneg (by linarith))
  have hpoint :
      ∀ x ∈ Set.uIoc (t-R) (t+R),
        |W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x|
          <= M * U := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith : t-R <= t+R)] at hx
    have hphi0 := W.threeTapAdversePhysicalOrdinateTest_nonneg ht
    have hphi := W.threeTapAdversePhysicalOrdinateTest_le_supMass ht
    have hx1 : 1 <= x := hleft.trans hx.1.le
    have hmuAbs := hmu x hx1
    have hlog : Real.log (x+3) <= Real.log ((t+R)+3) :=
      Real.log_le_log (by linarith) (by linarith [hx.2])
    have hmuAbs' : |Zeta23.mu x| <= U :=
      hmuAbs.trans (mul_le_mul_of_nonneg_left hlog hCmu0.le)
    rw [abs_mul, abs_of_nonneg hphi0]
    exact mul_le_mul hphi hmuAbs' (abs_nonneg _) hM
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x =>
        W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x)
      hpoint
  rw [Real.norm_eq_abs] at hraw
  have hlen : |(t+R)-(t-R)| = 2*R := by
    rw [show (t+R)-(t-R)=2*R by ring, abs_of_nonneg (by linarith)]
  rw [hlen] at hraw
  have hupper :
      (∫ x in (t-R)..(t+R),
        W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x)
        <= M * U * (2*R) := by
    exact (le_abs_self _).trans hraw
  unfold QuarticFourSignedPolePair.threeTapAdverseMuMass
  dsimp [M,U] at hupper ⊢
  nlinarith

end Synthesis
