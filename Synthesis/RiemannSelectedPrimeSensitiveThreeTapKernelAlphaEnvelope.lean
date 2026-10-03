import Synthesis.RiemannSelectedPrimeSensitiveThreeTapKernelPhaseCut

/-!
# Horizontal-strip envelope for the transformed adverse kernel

The phase-level cut shows that the adverse subset of the v-integral depends on
`eps`, `q` and `v`, but not on the horizontal displacement `alpha`.  Therefore
an a-priori bound `|alpha| <= A` can be paid only in the positive cosh weight,
leaving an ordinate-only adverse kernel envelope.

This is the same-object seam needed before applying zero-counting / RvM / Abel
machinery in the ordinate coordinate.  The strip bound is an explicit premise;
no unstated theorem about the zero strip is imported here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Positive part of the alpha-independent phase core. -/
def QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps q v : ℝ) : ℝ :=
  (W.threeTapKernelPhaseCore eps q v
    + |W.threeTapKernelPhaseCore eps q v|) / 2

theorem QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart_nonneg
    {t eps q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelPhaseAdversePart eps q v := by
  unfold QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
  by_cases h : 0 <= W.threeTapKernelPhaseCore eps q v
  · rw [abs_of_nonneg h]
    linarith
  · have h' : W.threeTapKernelPhaseCore eps q v <= 0 := le_of_not_ge h
    rw [abs_of_nonpos h']
    ring

theorem QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand_eq_cosh_mul_phaseAdversePart
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelAdverseIntegrand eps alpha q v
      =
    Real.cosh (alpha*v)
      * W.threeTapKernelPhaseAdversePart eps q v := by
  by_cases hp : 0 <= W.threeTapKernelPhaseCore eps q v
  · have hc : 0 <= Real.cosh (alpha*v) := (Real.cosh_pos _).le
    have hi :
        0 <= W.threeTapKernelIntegrand eps alpha q v := by
      rw [W.threeTapKernelIntegrand_eq_cosh_mul_phaseCore]
      exact mul_nonneg hc hp
    unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
      QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
    rw [abs_of_nonneg hi, abs_of_nonneg hp]
    rw [W.threeTapKernelIntegrand_eq_cosh_mul_phaseCore]
    ring
  · have hp' : W.threeTapKernelPhaseCore eps q v <= 0 := le_of_not_ge hp
    have hc : 0 <= Real.cosh (alpha*v) := (Real.cosh_pos _).le
    have hi :
        W.threeTapKernelIntegrand eps alpha q v <= 0 := by
      rw [W.threeTapKernelIntegrand_eq_cosh_mul_phaseCore]
      exact mul_nonpos_of_nonneg_of_nonpos hc hp'
    unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
      QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
    rw [abs_of_nonpos hi, abs_of_nonpos hp']
    ring

/-- Ordinate-only adverse envelope after paying a horizontal strip radius A. -/
def QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A q : ℝ) : ℝ :=
  ∫ v : ℝ,
    Real.cosh (A * |v|)
      * W.threeTapKernelPhaseAdversePart eps q v

theorem QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart_integrable
    {t eps q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable (W.threeTapKernelPhaseAdversePart eps q) := by
  let F : ℝ → ℝ := fun v => W.threeTapKernelPhaseCore eps q v
  have hF : Integrable F := by
    dsimp [F]
    unfold QuarticFourSignedPolePair.threeTapKernelPhaseCore
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (W.threeTapNormalizedProjective_compact (eps:=eps)).mul_right
  have hsum := hF.add hF.abs
  have hscaled := hsum.const_mul (1/2 : ℝ)
  simpa [F, QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_integrable
    {t eps A q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun v : ℝ =>
        Real.cosh (A * |v|)
          * W.threeTapKernelPhaseAdversePart eps q v) := by
  have hcont :
      Continuous
        (fun v : ℝ =>
          Real.cosh (A * |v|)
            * W.threeTapKernelPhaseAdversePart eps q v) := by
    unfold QuarticFourSignedPolePair.threeTapKernelPhaseAdversePart
      QuarticFourSignedPolePair.threeTapKernelPhaseCore
    fun_prop
  have hcomp :
      HasCompactSupport
        (fun v : ℝ =>
          Real.cosh (A * |v|)
            * W.threeTapKernelPhaseAdversePart eps q v) := by
    have hP := W.threeTapNormalizedProjective_compact (eps:=eps)
    apply hP.mul_left
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Cosh monotonicity pays the entire horizontal coordinate by its strip bound. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseMass_le_alphaEnvelope
    {t eps A alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (halpha : |alpha| <= A) :
    W.threeTapKernelAdverseMass eps alpha q
      <= W.threeTapKernelAdverseAlphaEnvelope eps A q := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseMass
    QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope
  have hleft := W.threeTapKernelAdverseIntegrand_integrable
    (eps:=eps) (alpha:=alpha) (q:=q)
  have hright := W.threeTapKernelAdverseAlphaEnvelope_integrable
    (eps:=eps) (A:=A) (q:=q)
  apply integral_mono hleft hright
  intro v
  rw [W.threeTapKernelAdverseIntegrand_eq_cosh_mul_phaseAdversePart]
  have hv : |alpha*v| <= |A * |v|| := by
    rw [abs_mul, abs_mul, abs_abs, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_right halpha (abs_nonneg v)
  have hcosh : Real.cosh (alpha*v) <= Real.cosh (A*|v|) := by
    exact (Real.cosh_le_cosh).2 hv
  exact mul_le_mul_of_nonneg_right hcosh
    W.threeTapKernelPhaseAdversePart_nonneg

theorem QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope_nonneg
    {t eps A q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelAdverseAlphaEnvelope eps A q := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaEnvelope
  exact integral_nonneg fun v =>
    mul_nonneg (Real.cosh_pos _).le
      W.threeTapKernelPhaseAdversePart_nonneg

/-- Per-zero pair adverse mass after removing alpha. -/
theorem QuarticFourSignedPolePair.threeTapPairAdversePart_le_alphaEnvelope
    {t eps A : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (rho : Zeros)
    (halpha : |heightOf rho / (t/16)| <= A) :
    W.threeTapPairAdversePart eps rho
      <=
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2)
      * W.threeTapKernelAdverseAlphaEnvelope eps A
          (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  have hpoint := W.threeTapPairAdversePart_le_kernelAdverseMass ht rho
  have henv := W.threeTapKernelAdverseMass_le_alphaEnvelope
    (eps:=eps)
    (A:=A)
    (alpha:=heightOf rho / (t/16))
    (q:=quarticSignedPoleNormalizedOrdinateOffset t rho)
    hA halpha
  have hc := W.threeTapAdaptivePairCoefficient_pos ht rho
  exact hpoint.trans (mul_le_mul_of_nonneg_left henv hc.le)

/-- Same-object aggregate interface: any uniform strip bound converts the
transformed adverse pair problem into an ordinate-only envelope.  This theorem
is deliberately pointwise; summing it requires a summable ordinate producer,
which is the next analytic cut. -/
def QuarticFourSignedPolePair.ThreeTapAlphaStripBound
    {t : ℝ} (W : QuarticFourSignedPolePair t) (A : ℝ) : Prop :=
  ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
    |heightOf (sigma : Zeros) / (t/16)| <= A

theorem QuarticFourSignedPolePair.threeTapPairAdversePart_le_ordinateEnvelope_of_strip
    {t eps A : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hstrip : W.ThreeTapAlphaStripBound A)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.threeTapPairAdversePart eps (sigma : Zeros)
      <=
    (((zetaZeroConfig).mult (sigma : Zeros) : ℝ) / (t/16)^2)
      * W.threeTapKernelAdverseAlphaEnvelope eps A
          (quarticSignedPoleNormalizedOrdinateOffset t (sigma : Zeros)) := by
  exact W.threeTapPairAdversePart_le_alphaEnvelope ht hA _ (hstrip sigma)

end Synthesis
