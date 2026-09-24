import Synthesis.MillenniumBSDCMEta32QProduct
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Rapid decay and strong Mellin functional-equation package for eta32

The literal q-product writes the normalized kernel as

  F(x) = q(x) * B(q(x)),
  q(x) = exp(-2*pi*x/sqrt(32)),

where B(q) tends to 1 as q tends to 0.  Hence F has exponential, therefore
super-polynomial, decay at +infinity.  Together with the exact inversion
`F(1/x)=x^2 F(x)`, this gives a self-dual strong FE-pair of weight 2 and
root number +1 in mathlib's AbstractFuncEq framework.
-/

namespace Synthesis.Millennium.BSD

open Complex Filter Asymptotics Set MeasureTheory

noncomputable def etaEulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

theorem etaEulerProduct_eq_tprod (q : ℂ) :
    etaEulerProduct q = ∏' n : ℕ, (1 - q ^ (n + 1)) := rfl

theorem etaEulerProduct_zero : etaEulerProduct 0 = 1 := by
  simp [etaEulerProduct]

theorem etaEulerProduct_continuousAt_zero :
    ContinuousAt etaEulerProduct 0 := by
  have hmem : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
  have h := ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn
  exact h.continuousAt (Metric.isOpen_ball.mem_nhds hmem)

theorem etaEulerProduct_tendsto_zero :
    Tendsto etaEulerProduct (𝓝 0) (𝓝 1) := by
  simpa [etaEulerProduct_zero] using etaEulerProduct_continuousAt_zero

noncomputable def etaEulerProductScaled (m : ℕ) (q : ℂ) : ℂ :=
  etaEulerProduct (q ^ m)

theorem etaEulerProductScaled_tendsto_zero
    (m : ℕ) (hm : 0 < m) :
    Tendsto (etaEulerProductScaled m) (𝓝 0) (𝓝 1) := by
  unfold etaEulerProductScaled
  exact etaEulerProduct_tendsto_zero.comp
    ((continuousAt_id.pow m).tendsto.trans <| by simpa [hm.ne'] using tendsto_nhds)

noncomputable def cmEta32BoundedFactor (q : ℂ) : ℂ :=
  (etaEulerProductScaled 4 q) ^ 2 *
    (etaEulerProductScaled 8 q) ^ 2

theorem cmEta32BoundedFactor_tendsto_zero :
    Tendsto cmEta32BoundedFactor (𝓝 0) (𝓝 1) := by
  unfold cmEta32BoundedFactor
  simpa using
    ((etaEulerProductScaled_tendsto_zero 4 (by norm_num)).pow 2).mul
      ((etaEulerProductScaled_tendsto_zero 8 (by norm_num)).pow 2)

theorem cmEta32QProduct_eq_q_mul_factor (q : ℂ) :
    cmEta32QProduct q = q * cmEta32BoundedFactor q := by
  unfold cmEta32QProduct cmEta32BoundedFactor etaEulerProductScaled etaEulerProduct
  rfl

noncomputable def cmEta32DecayRate : ℝ :=
  2 * Real.pi / cmEta32Scale

theorem cmEta32DecayRate_pos : 0 < cmEta32DecayRate := by
  unfold cmEta32DecayRate
  positivity

theorem qParam_eta32Kernel (x : ℝ) :
    Function.Periodic.qParam 1
      (Complex.I * ((x / cmEta32Scale : ℝ) : ℂ))
      = (Real.exp (-cmEta32DecayRate * x) : ℂ) := by
  unfold Function.Periodic.qParam cmEta32DecayRate
  rw [← Complex.ofReal_exp]
  congr 1
  field_simp [cmEta32Scale_ne_zero]
  ring

theorem cmEta32Kernel_factorization (x : ℝ) :
    cmEta32Kernel x =
      (Real.exp (-cmEta32DecayRate * x) : ℂ) *
        cmEta32BoundedFactor
          (Real.exp (-cmEta32DecayRate * x) : ℂ) := by
  unfold cmEta32Kernel
  rw [cmEta32_eq_qProduct, qParam_eta32Kernel,
    cmEta32QProduct_eq_q_mul_factor]

theorem eta32_q_tendsto_atTop :
    Tendsto
      (fun x : ℝ => (Real.exp (-cmEta32DecayRate * x) : ℂ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Complex.norm_real, abs_of_pos (Real.exp_pos _)] using
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg
        (neg_neg_of_pos cmEta32DecayRate_pos))

theorem cmEta32BoundedFactor_tendsto_atTop :
    Tendsto
      (fun x : ℝ =>
        cmEta32BoundedFactor
          (Real.exp (-cmEta32DecayRate * x) : ℂ))
      atTop (𝓝 1) :=
  cmEta32BoundedFactor_tendsto_zero.comp eta32_q_tendsto_atTop

theorem cmEta32Kernel_isBigO_exp :
    cmEta32Kernel =O[atTop]
      (fun x : ℝ => Real.exp (-cmEta32DecayRate * x)) := by
  have hfactor :
      (fun x : ℝ =>
        cmEta32BoundedFactor
          (Real.exp (-cmEta32DecayRate * x) : ℂ))
        =O[atTop] (fun _ : ℝ => (1 : ℂ)) :=
    isBigO_const_of_tendsto cmEta32BoundedFactor_tendsto_atTop
      (one_ne_zero : (1 : ℂ) ≠ 0)
  have hq :
      (fun x : ℝ => (Real.exp (-cmEta32DecayRate * x) : ℂ))
        =O[atTop]
      (fun x : ℝ => Real.exp (-cmEta32DecayRate * x)) := by
    simpa using isBigO_refl
      (fun x : ℝ => Real.exp (-cmEta32DecayRate * x)) atTop
  simpa [cmEta32Kernel_factorization, mul_comm] using hq.mul hfactor

theorem cmEta32Kernel_rapid_decay (r : ℝ) :
    cmEta32Kernel =O[atTop] (fun x : ℝ => x ^ r) := by
  exact cmEta32Kernel_isBigO_exp.trans
    (isLittleO_exp_neg_mul_rpow_atTop cmEta32DecayRate_pos r).isBigO

theorem cmEta32Kernel_continuousOn_pos :
    ContinuousOn cmEta32Kernel (Ioi 0) := by
  intro x hx
  exact (cmEta32_differentiableAt
    (cmEta32Kernel_arg_mem_upperHalfPlane hx)).continuousAt.continuousWithinAt

theorem cmEta32Kernel_locallyIntegrableOn :
    LocallyIntegrableOn cmEta32Kernel (Ioi 0) :=
  cmEta32Kernel_continuousOn_pos.locallyIntegrableOn measurableSet_Ioi

noncomputable def cmEta32FEPair : WeakFEPair ℂ where
  f := cmEta32Kernel
  g := cmEta32Kernel
  k := 2
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := cmEta32Kernel_locallyIntegrableOn
  hg_int := cmEta32Kernel_locallyIntegrableOn
  hk := by norm_num
  hε := one_ne_zero
  h_feq := by
    intro x hx
    rw [cmEta32Kernel_inversion_rpow hx]
    simp [smul_eq_mul]
  hf_top := by
    intro r
    simpa using cmEta32Kernel_rapid_decay r
  hg_top := by
    intro r
    simpa using cmEta32Kernel_rapid_decay r

theorem cmEta32FEPair_isStrong :
    IsStrongFEPair cmEta32FEPair where
  hf₀ := rfl
  hg₀ := rfl

noncomputable def cmEta32CompletedMellin (s : ℂ) : ℂ :=
  cmEta32FEPair.Λ s

theorem cmEta32CompletedMellin_entire :
    Differentiable ℂ cmEta32CompletedMellin := by
  exact cmEta32FEPair_isStrong.differentiable_Λ

theorem cmEta32CompletedMellin_eq_mellin (s : ℂ) :
    cmEta32CompletedMellin s = mellin cmEta32Kernel s := by
  exact congrFun cmEta32FEPair_isStrong.Λ_eq s

theorem cmEta32CompletedMellin_functional_equation (s : ℂ) :
    cmEta32CompletedMellin (2 - s) = cmEta32CompletedMellin s := by
  simpa [cmEta32CompletedMellin, cmEta32FEPair] using
    (cmEta32FEPair.functional_equation s)

end Synthesis.Millennium.BSD
