import Synthesis.RiemannSelectedPrimeSensitiveThreeTapPairSignedCut

/-!
# Phase-level signed cut inside the transformed pair kernel

For the actual normalized transformed signed profile P_eps,

  K_eps(alpha,q)
    = integral P_eps(v) cosh(alpha v) cos(q v) dv.

Because `cosh(alpha v)` is strictly positive, the pointwise adverse/favorable
phase is controlled entirely by

  P_eps(v) * cos(q v),

independently of the horizontal displacement alpha.  This file records that
fact and splits the kernel integral into a nonnegative adverse mass minus a
nonnegative favorable credit before any absolute-value estimate is taken.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Literal integrand of the transformed normalized reflection-pair kernel. -/
def QuarticFourSignedPolePair.threeTapKernelIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q v : ℝ) : ℝ :=
  W.threeTapNormalizedSignedProjectiveProfile eps v
    * Real.cosh (alpha*v) * Real.cos (q*v)

/-- The sign-driving phase core; notably independent of alpha. -/
def QuarticFourSignedPolePair.threeTapKernelPhaseCore
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps q v : ℝ) : ℝ :=
  W.threeTapNormalizedSignedProjectiveProfile eps v
    * Real.cos (q*v)

/-- Pointwise adverse part of the exact kernel integrand. -/
def QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q v : ℝ) : ℝ :=
  (W.threeTapKernelIntegrand eps alpha q v
    + |W.threeTapKernelIntegrand eps alpha q v|) / 2

/-- Magnitude of the pointwise favorable part of the exact kernel integrand. -/
def QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q v : ℝ) : ℝ :=
  (|W.threeTapKernelIntegrand eps alpha q v|
    - W.threeTapKernelIntegrand eps alpha q v) / 2

/-- Pointwise adverse phase condition.  Alpha does not occur. -/
def QuarticFourSignedPolePair.threeTapKernelPhaseAdverse
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps q v : ℝ) : Prop :=
  0 < W.threeTapKernelPhaseCore eps q v

theorem QuarticFourSignedPolePair.threeTapKernelIntegrand_eq_cosh_mul_phaseCore
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelIntegrand eps alpha q v
      = Real.cosh (alpha*v) * W.threeTapKernelPhaseCore eps q v := by
  unfold QuarticFourSignedPolePair.threeTapKernelIntegrand
    QuarticFourSignedPolePair.threeTapKernelPhaseCore
  ring

/-- The integrand sign is exactly the alpha-independent phase-core sign. -/
theorem QuarticFourSignedPolePair.threeTapKernelIntegrand_pos_iff_phaseAdverse
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapKernelIntegrand eps alpha q v
      <-> W.threeTapKernelPhaseAdverse eps q v := by
  rw [W.threeTapKernelIntegrand_eq_cosh_mul_phaseCore]
  unfold QuarticFourSignedPolePair.threeTapKernelPhaseAdverse
  have hc : 0 < Real.cosh (alpha*v) := Real.cosh_pos _
  constructor
  · intro h
    by_contra hp
    have hp' : W.threeTapKernelPhaseCore eps q v <= 0 := le_of_not_gt hp
    have hnonpos :
        Real.cosh (alpha*v) * W.threeTapKernelPhaseCore eps q v <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le hp'
    linarith
  · intro hp
    exact mul_pos hc hp

theorem QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand_nonneg
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelAdverseIntegrand eps alpha q v := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
  by_cases h : 0 <= W.threeTapKernelIntegrand eps alpha q v
  · rw [abs_of_nonneg h]
    linarith
  · have h' : W.threeTapKernelIntegrand eps alpha q v <= 0 := le_of_not_ge h
    rw [abs_of_nonpos h']
    ring

theorem QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand_nonneg
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelFavorableCreditIntegrand eps alpha q v := by
  unfold QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand
  exact div_nonneg (sub_nonneg.mpr (le_abs_self _)) (by norm_num)

theorem QuarticFourSignedPolePair.threeTapKernelIntegrand_eq_adverse_sub_credit
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelIntegrand eps alpha q v
      = W.threeTapKernelAdverseIntegrand eps alpha q v
        - W.threeTapKernelFavorableCreditIntegrand eps alpha q v := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
    QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand
  ring

theorem QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand_eq_zero_of_not_phaseAdverse
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (h : ¬ W.threeTapKernelPhaseAdverse eps q v) :
    W.threeTapKernelAdverseIntegrand eps alpha q v = 0 := by
  have hnonpos : W.threeTapKernelIntegrand eps alpha q v <= 0 := by
    have hp : W.threeTapKernelPhaseCore eps q v <= 0 := by
      exact le_of_not_gt h
    rw [W.threeTapKernelIntegrand_eq_cosh_mul_phaseCore]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.cosh_pos _).le hp
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
  rw [abs_of_nonpos hnonpos]
  ring

theorem QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand_eq_integrand_of_phaseAdverse
    {t eps alpha q v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (h : W.threeTapKernelPhaseAdverse eps q v) :
    W.threeTapKernelAdverseIntegrand eps alpha q v
      = W.threeTapKernelIntegrand eps alpha q v := by
  have hpos : 0 < W.threeTapKernelIntegrand eps alpha q v :=
    (W.threeTapKernelIntegrand_pos_iff_phaseAdverse).2 h
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand
  rw [abs_of_pos hpos]
  ring

theorem QuarticFourSignedPolePair.threeTapKernelIntegrand_integrable
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable (W.threeTapKernelIntegrand eps alpha q) := by
  unfold QuarticFourSignedPolePair.threeTapKernelIntegrand
  exact Continuous.integrable_of_hasCompactSupport
    (by fun_prop)
    ((W.threeTapNormalizedProjective_compact (eps:=eps)).mul_right.mul_right)

theorem QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand_integrable
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable (W.threeTapKernelAdverseIntegrand eps alpha q) := by
  have h := W.threeTapKernelIntegrand_integrable (eps:=eps) (alpha:=alpha) (q:=q)
  have hsum := h.add h.abs
  have hscaled := hsum.const_mul (1/2 : ℝ)
  simpa [QuarticFourSignedPolePair.threeTapKernelAdverseIntegrand,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand_integrable
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable (W.threeTapKernelFavorableCreditIntegrand eps alpha q) := by
  have h := W.threeTapKernelIntegrand_integrable (eps:=eps) (alpha:=alpha) (q:=q)
  have hdiff := h.abs.sub h
  have hscaled := hdiff.const_mul (1/2 : ℝ)
  simpa [QuarticFourSignedPolePair.threeTapKernelFavorableCreditIntegrand,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

def QuarticFourSignedPolePair.threeTapKernelAdverseMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q : ℝ) : ℝ :=
  ∫ v : ℝ, W.threeTapKernelAdverseIntegrand eps alpha q v

def QuarticFourSignedPolePair.threeTapKernelFavorableCredit
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q : ℝ) : ℝ :=
  ∫ v : ℝ, W.threeTapKernelFavorableCreditIntegrand eps alpha q v

theorem QuarticFourSignedPolePair.threeTapKernelAdverseMass_nonneg
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelAdverseMass eps alpha q := by
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseMass
  exact integral_nonneg fun v => W.threeTapKernelAdverseIntegrand_nonneg

theorem QuarticFourSignedPolePair.threeTapKernelFavorableCredit_nonneg
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapKernelFavorableCredit eps alpha q := by
  unfold QuarticFourSignedPolePair.threeTapKernelFavorableCredit
  exact integral_nonneg fun v => W.threeTapKernelFavorableCreditIntegrand_nonneg

/-- Exact adverse-minus-credit normal form for the actual transformed kernel. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedPairKernel_eq_adverse_sub_credit
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedPairKernel eps alpha q
      = W.threeTapKernelAdverseMass eps alpha q
        - W.threeTapKernelFavorableCredit eps alpha q := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedPairKernel
    QuarticFourSignedPolePair.threeTapKernelAdverseMass
    QuarticFourSignedPolePair.threeTapKernelFavorableCredit
    QuarticFourSignedPolePair.threeTapKernelIntegrand
  have ha := W.threeTapKernelAdverseIntegrand_integrable
    (eps:=eps) (alpha:=alpha) (q:=q)
  have hf := W.threeTapKernelFavorableCreditIntegrand_integrable
    (eps:=eps) (alpha:=alpha) (q:=q)
  rw [← integral_sub ha hf]
  apply integral_congr_ae
  filter_upwards with v
  exact W.threeTapKernelIntegrand_eq_adverse_sub_credit

/-- One-sided kernel bound that pays only the pointwise adverse phase. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedPairKernel_le_adverseMass
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedPairKernel eps alpha q
      <= W.threeTapKernelAdverseMass eps alpha q := by
  rw [W.threeTapNormalizedPairKernel_eq_adverse_sub_credit]
  have hf := W.threeTapKernelFavorableCredit_nonneg
    (eps:=eps) (alpha:=alpha) (q:=q)
  linarith

/-- Per-zero upper majorant for the adverse pair contribution.  The majorant
still retains the oscillatory phase cut inside the v-integral. -/
theorem QuarticFourSignedPolePair.threeTapPairAdversePart_le_kernelAdverseMass
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapPairAdversePart eps rho
      <=
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2)
      * W.threeTapKernelAdverseMass eps
          (heightOf rho / (t/16))
          (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  have hc := W.threeTapAdaptivePairCoefficient_pos ht rho
  have hA := W.threeTapKernelAdverseMass_nonneg
    (eps:=eps)
    (alpha:=heightOf rho / (t/16))
    (q:=quarticSignedPoleNormalizedOrdinateOffset t rho)
  by_cases hk :
      0 <= W.threeTapNormalizedPairKernel eps
        (heightOf rho / (t/16))
        (quarticSignedPoleNormalizedOrdinateOffset t rho)
  · have hpairNonneg : 0 <= W.threeTapAdaptivePairTerm eps rho := by
      unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
      exact mul_nonneg hc.le hk
    rw [W.threeTapPairAdversePart_eq_self_of_nonneg rho hpairNonneg]
    unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
    exact mul_le_mul_of_nonneg_left
      W.threeTapNormalizedPairKernel_le_adverseMass hc.le
  · have hk' :
        W.threeTapNormalizedPairKernel eps
          (heightOf rho / (t/16))
          (quarticSignedPoleNormalizedOrdinateOffset t rho) <= 0 :=
      le_of_not_ge hk
    have hpairNonpos : W.threeTapAdaptivePairTerm eps rho <= 0 := by
      unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hk'
    rw [W.threeTapPairAdversePart_eq_zero_of_nonpos rho hpairNonpos]
    exact mul_nonneg hc.le hA

end Synthesis
