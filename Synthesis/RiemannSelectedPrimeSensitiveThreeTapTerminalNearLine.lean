import Synthesis.RiemannSelectedPrimeSensitiveThreeTapNearLineDecision

/-!
# Whole-terminal near-line hierarchy

For fixed t, selected W and tap strength eps, the completed external carrier
and the canonical adaptive local slack are independent of the target
horizontal displacement a.  Hence the terminal profile has an exact constant
term at a=0.

Only when that constant cancels is the transformed J2 coordinate the leading
terminal coefficient.  This file makes that hierarchy explicit and prevents
silently assuming an a^2/a^4 leading terminal law.
-/

noncomputable section
namespace Synthesis

open scoped Real

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult a : ℝ) : ℝ :=
  2 * mult * W.threeTapCombinedHeightDefect eps a
    -
  (W.threeTapCompletedExternal eps
    + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps)

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalConstant
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  - (W.threeTapCompletedExternal eps
      + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps)

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile_zero
    {t eps mult : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveTerminalProfile eps mult 0
      =
    W.threeTapAdaptiveTerminalConstant eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile
    QuarticFourSignedPolePair.threeTapAdaptiveTerminalConstant
  rw [W.threeTapCombinedHeightDefect_zero]
  ring

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin_eq_profile
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapAdaptiveTerminalMargin eps rho
      =
    W.threeTapAdaptiveTerminalProfile eps
      ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
      (heightOf rho) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin
    QuarticFourSignedPolePair.threeTapSelectedTerminalMargin
    QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile
  rw [W.threeTapCombinedZeroHeightDefect_eq]
  ring

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult a : ℝ) : ℝ :=
  2 * mult * W.threeTapCombinedHeightD1 eps a

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult a : ℝ) : ℝ :=
  2 * mult * W.threeTapCombinedHeightD2 eps a

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile_hasDerivAt
    {t eps mult a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapAdaptiveTerminalProfile eps mult)
      (W.threeTapAdaptiveTerminalProfileD1 eps mult a) a := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfile
    QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1
  convert
    (W.threeTapCombinedHeight_hasDerivAt
      (eps:=eps) ht (a:=a)).const_mul (2*mult) using 1 <;> ring

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1_hasDerivAt
    {t eps mult a : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt
      (W.threeTapAdaptiveTerminalProfileD1 eps mult)
      (W.threeTapAdaptiveTerminalProfileD2 eps mult a) a := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1
    QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2
  convert
    (W.threeTapCombinedHeightD1_hasDerivAt
      (eps:=eps) ht (a:=a)).const_mul (2*mult) using 1 <;> ring

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1_zero
    {t eps mult : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveTerminalProfileD1 eps mult 0 = 0 := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD1
  rw [W.threeTapCombinedHeightD1_zero]
  ring

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2_zero
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveTerminalProfileD2 eps mult 0
      =
    -2 * mult * (1/(t/16)^4)
      *
    (eps * W.threeTapNormalizedJ2LinearCoeff
      + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2
  rw [W.threeTap_target_second_derivative_sign ht]
  ring

/-- If the completed constant is already positive, strict terminal positivity
holds on a punctured neighborhood independently of J2. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_pos_right_of_constant_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hconst : 0 < W.threeTapAdaptiveTerminalConstant eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have hcont :
      ContinuousAt
        (W.threeTapAdaptiveTerminalProfile eps mult) 0 :=
    (W.threeTapAdaptiveTerminalProfile_hasDerivAt
      (eps:=eps) (mult:=mult) ht (a:=0)).continuousAt
  have hopen :
      ∀ᶠ a : ℝ in 𝓝 0,
        0 < W.threeTapAdaptiveTerminalProfile eps mult a :=
    (isOpen_lt continuous_const
      (continuous_of_continuousAt_zero hcont)).mem_nhds
      (by simpa [W.threeTapAdaptiveTerminalProfile_zero] using hconst)
  rw [Metric.eventually_nhds_iff] at hopen
  obtain ⟨delta,hdelta,hband⟩ := hopen
  refine ⟨delta,hdelta,?_⟩
  intro a ha had
  apply hband
  rw [Real.dist_eq]
  simpa [abs_of_pos ha] using had

/-- If the completed constant is negative, the whole terminal scalar is
strictly negative near the line regardless of a favorable target quadratic
coefficient.  This is an immediate one-scale no-go regime. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_neg_right_of_constant_neg
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hconst : W.threeTapAdaptiveTerminalConstant eps < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hcont :
      ContinuousAt
        (W.threeTapAdaptiveTerminalProfile eps mult) 0 :=
    (W.threeTapAdaptiveTerminalProfile_hasDerivAt
      (eps:=eps) (mult:=mult) ht (a:=0)).continuousAt
  have hopen :
      ∀ᶠ a : ℝ in 𝓝 0,
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 :=
    (isOpen_lt
      (continuous_of_continuousAt_zero hcont)
      continuous_const).mem_nhds
      (by simpa [W.threeTapAdaptiveTerminalProfile_zero] using hconst)
  rw [Metric.eventually_nhds_iff] at hopen
  obtain ⟨delta,hdelta,hband⟩ := hopen
  refine ⟨delta,hdelta,?_⟩
  intro a ha had
  apply hband
  rw [Real.dist_eq]
  simpa [abs_of_pos ha] using had

/-- On the exactly balanced completed-constant locus, the normalized J2
polynomial is the leading second derivative of the whole terminal scalar.
For positive multiplicity, negative J2 polynomial gives a positive quadratic
terminal band. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_pos_right_of_balanced_J2poly_neg
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hmult : 0 < mult)
    (hconst : W.threeTapAdaptiveTerminalConstant eps = 0)
    (hJ :
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have h2 :
      0 < W.threeTapAdaptiveTerminalProfileD2 eps mult 0 := by
    rw [W.threeTapAdaptiveTerminalProfileD2_zero ht]
    have hr : 0 < t/16 := by linarith
    have hfac : 0 < (1/(t/16)^4 : ℝ) := by positivity
    nlinarith
  have hD2cont :
      Continuous (W.threeTapAdaptiveTerminalProfileD2 eps mult) := by
    unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2
    exact (W.threeTapCombinedHeightD2_continuous ht).const_mul _
  exact
    exists_pos_right_of_second_deriv_pos
      (f := W.threeTapAdaptiveTerminalProfile eps mult)
      (f1 := W.threeTapAdaptiveTerminalProfileD1 eps mult)
      (f2 := W.threeTapAdaptiveTerminalProfileD2 eps mult)
      (fun a => W.threeTapAdaptiveTerminalProfile_hasDerivAt ht)
      (fun a => W.threeTapAdaptiveTerminalProfileD1_hasDerivAt ht)
      hD2cont
      (by rw [W.threeTapAdaptiveTerminalProfile_zero, hconst])
      W.threeTapAdaptiveTerminalProfileD1_zero
      h2

/-- Balanced constant plus positive J2 polynomial gives a strictly negative
whole-terminal band near the critical line. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_neg_right_of_balanced_J2poly_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hmult : 0 < mult)
    (hconst : W.threeTapAdaptiveTerminalConstant eps = 0)
    (hJ :
      0 <
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have h2 :
      W.threeTapAdaptiveTerminalProfileD2 eps mult 0 < 0 := by
    rw [W.threeTapAdaptiveTerminalProfileD2_zero ht]
    have hr : 0 < t/16 := by linarith
    have hfac : 0 < (1/(t/16)^4 : ℝ) := by positivity
    nlinarith
  have h2neg :
      0 < - W.threeTapAdaptiveTerminalProfileD2 eps mult 0 := by
    linarith
  have hD2cont :
      Continuous (W.threeTapAdaptiveTerminalProfileD2 eps mult) := by
    unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalProfileD2
    exact (W.threeTapCombinedHeightD2_continuous ht).const_mul _
  obtain ⟨delta,hdelta,hband⟩ :=
    exists_pos_right_of_second_deriv_pos
      (f := fun a => - W.threeTapAdaptiveTerminalProfile eps mult a)
      (f1 := fun a => - W.threeTapAdaptiveTerminalProfileD1 eps mult a)
      (f2 := fun a => - W.threeTapAdaptiveTerminalProfileD2 eps mult a)
      (fun a => (W.threeTapAdaptiveTerminalProfile_hasDerivAt ht).neg)
      (fun a => (W.threeTapAdaptiveTerminalProfileD1_hasDerivAt ht).neg)
      hD2cont.neg
      (by rw [W.threeTapAdaptiveTerminalProfile_zero, hconst]; ring)
      (by rw [W.threeTapAdaptiveTerminalProfileD1_zero]; ring)
      h2neg
  refine ⟨delta,hdelta,?_⟩
  intro a ha had
  have h := hband a ha had
  linarith

end Synthesis
