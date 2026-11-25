import Integration.Paper9OriginalEisensteinDerivative

/-! Paper 9: actual bracket cusp packaging, source-written, not elaborated.
The sole remaining input to bracketValue is actual weight-12 slash covariance.
No assumed cusp form or first coefficient, and no new analytic carrier. -/
namespace Integration.Paper9BracketCuspClosure

open Function Complex Filter UpperHalfPlane ModularForm ModularFormClass
open SlashInvariantFormClass
open scoped MatrixGroups Topology Real Manifold

noncomputable section

open Integration.Paper9OriginalEisensteinDerivative

def bracketAt (τ : ℍ) : ℂ := bracketQ (Periodic.qParam 1 τ)

theorem qNorm (τ : ℍ) : ‖Periodic.qParam 1 τ‖ < 1 := by
  simpa [Periodic.qParam] using UpperHalfPlane.norm_exp_two_pi_I_lt_one τ

theorem xAnalyticDisk (q : ℂ) (hq : ‖q‖ < 1) : AnalyticAt ℂ x q :=
  DifferentiableOn.analyticAt
    (fun z hz => (xDifferentiable z (mem_ball_zero_iff.mp hz)).differentiableWithinAt)
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq))

theorem yAnalyticDisk (q : ℂ) (hq : ‖q‖ < 1) : AnalyticAt ℂ y q :=
  DifferentiableOn.analyticAt
    (fun z hz => (yDifferentiable z (mem_ball_zero_iff.mp hz)).differentiableWithinAt)
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq))

theorem bracketAnalyticDisk (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ bracketQ q := by
  have hx := xAnalyticDisk q hq
  have hy := yAnalyticDisk q hq
  have hu : AnalyticAt ℂ bracketUnit q := by
    unfold bracketUnit
    exact ((analyticAt_const.mul hy).mul hx.deriv).sub
      ((analyticAt_const.mul hx).mul hy.deriv)
  rw [show bracketQ = fun z => z * bracketUnit z from funext bracketFactor]
  exact analyticAt_id.mul hu

theorem bracketHolo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) bracketAt := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ : ℍ := ⟨z, hz⟩
  have hq : ‖Periodic.qParam 1 z‖ < 1 := qNorm τ
  have hd : DifferentiableAt ℂ (fun w : ℂ => Periodic.qParam 1 w) z := by
    unfold Periodic.qParam
    fun_prop
  have hc := (bracketAnalyticDisk _ hq).differentiableAt.comp z hd
  apply (hc.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp [Function.comp_def, bracketAt, ofComplex_apply_of_im_pos hw]

theorem bracketZeroAtInfty : IsZeroAtImInfty bracketAt := by
  have ht := (bracketAnalyticDisk 0 (by simp)).continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos)
  rw [bracketZero] at ht
  exact ht

-- Exact polynomial covariance after the two derivative chain rules.
-- c denotes the original scaled lower-left matrix entry.
theorem bracketCovarianceAlgebra (x y u v j c : ℂ) :
    3 * (j^6*y) * (j^6*u+4*c*j^5*x) -
      2 * (j^4*x) * (j^8*v+6*c*j^7*y) =
      j^12*(3*y*u-2*x*v) := by ring

-- Input explicitly uses the ACTUAL derivative coordinates. It is not
-- the desired bracket identity or an arbitrary cusp form.
theorem bracketSlashFromDerivativeTransport
    (h4 : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      dx (γ • τ) = ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^6 * dx τ +
        4*((γ 1 0 : ℂ)/(2*Real.pi*Complex.I)) *
          ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^5 *
          Integration.MoonshineEisensteinAnalytic.E4 τ)
    (h6 : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      dy (γ • τ) = ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^8 * dy τ +
        6*((γ 1 0 : ℂ)/(2*Real.pi*Complex.I)) *
          ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^7 *
          Integration.MoonshineEisensteinAnalytic.E6 τ) :
    ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt := by
  intro γ
  funext τ
  apply (slash_action_eq'_iff 12 bracketAt γ τ).2
  have hg : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  have hx := (slash_action_eq'_iff 4
    Integration.MoonshineEisensteinAnalytic.E4 γ τ).1
    (congrFun (by simpa [SL_slash] using
      (Integration.MoonshineEisensteinAnalytic.E4.slash_action_eq' _ hg)) τ)
  have hy := (slash_action_eq'_iff 6
    Integration.MoonshineEisensteinAnalytic.E6 γ τ).1
    (congrFun (by simpa [SL_slash] using
      (Integration.MoonshineEisensteinAnalytic.E6.slash_action_eq' _ hg)) τ)
  simp only [bracketAt, bracketSource]
  rw [h4 γ τ,h6 γ τ,hx,hy]
  push_cast
  norm_num [zpow_ofNat]
  <;> ring

def bracketCusp
    (hs : ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt) :
    CuspForm 𝒮ℒ 12 where
  toFun := bracketAt
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ (by simpa [SL_slash] using hs γ)
  holo' := bracketHolo
  zero_at_cusps' {c} hc γ hγ := by
    rw [hs γ]
    exact bracketZeroAtInfty

theorem bracketCuspFunctionOnDisk
    (hs : ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt)
    (q : ℂ) (hq : ‖q‖ < 1) :
    cuspFunction 1 (bracketCusp hs) q = bracketQ q := by
  by_cases h : q = 0
  · subst q
    rw [bracketZero]
    exact IsZeroAtImInfty.cuspFunction_apply_zero bracketZeroAtInfty one_pos
  · let τ : ℍ := ⟨Periodic.invQParam 1 q,
        Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq h⟩
    have hr : Periodic.qParam 1 τ = q := Periodic.qParam_right_inv one_ne_zero h
    rw [← hr, eq_cuspFunction (bracketCusp hs) τ
      one_mem_strictPeriods_SL one_ne_zero]
    rfl

theorem bracketCuspCoeffOne
    (hs : ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt) :
    (qExpansion 1 (bracketCusp hs)).coeff 1 = 1728 := by
  have hEq : cuspFunction 1 (bracketCusp hs) =ᶠ[𝓝 0] bracketQ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with q hq
    exact bracketCuspFunctionOnDisk hs q (mem_ball_zero_iff.mp hq)
  simpa [qExpansion_coeff, hEq.deriv_eq] using bracketHasDerivAtZero.deriv

theorem bracketValue
    (hs : ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt)
    (τ : ℍ) :
    bracketAt τ = 1728 * Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ :=
  bracketCuspValue (bracketCusp hs) (bracketCuspCoeffOne hs) τ

theorem ramanujan46FromSlash
    (hs : ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt)
    (τ : ℍ) :
    3 * dx τ = e2 τ * Integration.MoonshineEisensteinAnalytic.E4 τ -
      Integration.MoonshineEisensteinAnalytic.E6 τ ∧
    2 * dy τ = e2 τ * Integration.MoonshineEisensteinAnalytic.E6 τ -
      Integration.MoonshineEisensteinAnalytic.E4 τ ^ 2 :=
  ramanujan46FromBracket τ (qNorm τ) (bracketValue hs τ)

end
end Integration.Paper9BracketCuspClosure
