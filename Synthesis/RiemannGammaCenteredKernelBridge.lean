import Synthesis.RiemannGammaPartialResponseKernel
import Synthesis.RiemannGammaCenteredQuadraticMass
import Zeta23Bridge.LiteralWeilGammaChannel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal centered Gamma response equals the archimedean time-domain kernel

For the actual centered taper

  h_r(u) = g(u)(cos(r u)-1),

this file passes the anchored digamma partial responses to the limit and proves

  gammaResp h_r t 0
    = - integral_u h_r(u) cos(tu) gammaArchKernel(|u|).

This is the literal consumer bridge needed by the paired Gamma/pole ratio
analysis.  It is derived from the vendored digamma series, the exact
Lorentzian-cosFT convolution, and dominated convergence.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaChannel

theorem gammaArchKernel_le_inv_two_abs
    {u : ℝ} (hu : u ≠ 0) :
    gammaArchKernel |u| <= 1/(2*|u|) := by
  have hs : 0 < |u| := abs_pos.mpr hu
  rw [gammaArchKernel_eq_inv_two_sinh hs]
  have hle : |u| <= Real.sinh |u| :=
    Real.self_le_sinh_iff.mpr hs.le
  have hposU : 0 < 2*|u| := by positivity
  have hposS : 0 < 2*Real.sinh |u| := by
    exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hs)
  exact one_div_le_one_div_of_le hposU
    (mul_le_mul_of_nonneg_left hle (by norm_num))

theorem centeredKernelProduct_bound
    {g : ℝ → ℝ} (r t u : ℝ) :
    |gammaCenteredTaper g r u
        * Real.cos (t*u) * gammaArchKernel |u||
      <= (r^2/4) * (|u| * |g u|) := by
  by_cases hu : u = 0
  · subst u
    simp [gammaCenteredTaper, gammaArchKernel]
  · have hcenter :=
      abs_cos_sub_one_le_sq_div_two (r*u)
    have hK := gammaArchKernel_le_inv_two_abs hu
    have hK0 : 0 <= gammaArchKernel |u| :=
      (gammaArchKernel_pos (abs_pos.mpr hu)).le
    have hcos := Real.abs_cos_le_one (t*u)
    unfold gammaCenteredTaper
    rw [abs_mul, abs_mul]
    have h1 :
        |g u| * |Real.cos (r*u)-1|
          <= |g u| * ((r*u)^2/2) :=
      mul_le_mul_of_nonneg_left hcenter (abs_nonneg _)
    have h2 :
        (|g u| * |Real.cos (r*u)-1|)
          * |Real.cos (t*u)|
          <= |g u| * ((r*u)^2/2) := by
      exact le_trans
        (mul_le_mul_of_nonneg_left hcos
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        (by nlinarith)
    have h3 :
        ((|g u| * |Real.cos (r*u)-1|)
          * |Real.cos (t*u)|)
          * gammaArchKernel |u|
        <= (|g u| * ((r*u)^2/2)) * (1/(2*|u|)) := by
      exact mul_le_mul h2 hK hK0
        (by positivity)
    have huabs : 0 < |u| := abs_pos.mpr hu
    field_simp [ne_of_gt huabs] at h3 ⊢
    nlinarith [sq_abs u]

theorem centeredKernelDominating_integrable
    {g : ℝ → ℝ}
    (hg : Continuous g) (hcompact : HasCompactSupport g)
    (r : ℝ) :
    Integrable
      (fun u : ℝ => (r^2/4) * (|u| * |g u|)) := by
  have hc :
      Continuous (fun u : ℝ => (r^2/4) * (|u| * |g u|)) := by
    fun_prop
  have hs :
      HasCompactSupport
        (fun u : ℝ => (r^2/4) * (|u| * |g u|)) := by
    exact hcompact.abs.mul_left.comp_left
  exact hc.integrable_of_hasCompactSupport hs

theorem gammaKernelPartial_centered_dominated
    {g : ℝ → ℝ} (r t : ℝ) (N : ℕ) :
    ∀ u,
      |gammaCenteredTaper g r u
          * Real.cos (t*u) * gammaKernelPartial N u|
        <= (r^2/4) * (|u| * |g u|) := by
  intro u
  by_cases hu : u = 0
  · subst u
    simp [gammaCenteredTaper, gammaKernelPartial]
  · have hpartial := gammaKernelPartial_le_arch (N:=N) hu
    have hp0 := gammaKernelPartial_nonneg N u
    have hcenterArch := centeredKernelProduct_bound (g:=g) r t u
    rw [abs_mul, abs_mul]
    have hmul :
        |gammaCenteredTaper g r u| * |Real.cos (t*u)|
            * gammaKernelPartial N u
          <=
        |gammaCenteredTaper g r u| * |Real.cos (t*u)|
            * gammaArchKernel |u| := by
      exact mul_le_mul_of_nonneg_left hpartial
        (mul_nonneg
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (by norm_num))
    simpa [abs_of_nonneg hp0] using
      le_trans hmul hcenterArch

theorem gammaRespPartial_centered_tendsto_kernel
    {g : ℝ → ℝ}
    (hgC2 : ContDiff ℝ 2 g)
    (hcompact : HasCompactSupport g)
    (heven : ∀ u, g (-u)=g u)
    (r t : ℝ) :
    Tendsto
      (fun N => gammaRespPartial N (gammaCenteredTaper g r) t)
      atTop
      (nhds
        (- ∫ u : ℝ,
          gammaCenteredTaper g r u
            * Real.cos (t*u) * gammaArchKernel |u|)) := by
  have hcenterC2 := gammaCenteredTaper_contDiff hgC2 r
  have hcenterCompact := gammaCenteredTaper_hasCompactSupport hcompact r
  have hcenterEven := gammaCenteredTaper_even heven r
  have hcenter0 : gammaCenteredTaper g r 0 = 0 := by
    simp [gammaCenteredTaper]
  have hdom :=
    centeredKernelDominating_integrable
      hgC2.continuous hcompact r
  have htend :
      Tendsto
        (fun N =>
          ∫ u : ℝ,
            gammaCenteredTaper g r u
              * Real.cos (t*u) * gammaKernelPartial N u)
        atTop
        (nhds
          (∫ u : ℝ,
            gammaCenteredTaper g r u
              * Real.cos (t*u) * gammaArchKernel |u|)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u => (r^2/4) * (|u| * |g u|))
    · exact Eventually.of_forall fun N => by fun_prop
    · exact Eventually.of_forall fun N =>
        ae_of_all _ (gammaKernelPartial_centered_dominated
          (g:=g) r t N)
    · exact hdom
    · exact ae_of_all _ fun u =>
        gammaKernelPartial_centered_product_tendsto
          (h:=gammaCenteredTaper g r) hcenter0 t u
  have hpartial :
      ∀ N,
      gammaRespPartial N (gammaCenteredTaper g r) t
        =
      - ∫ u : ℝ,
        gammaCenteredTaper g r u
          * Real.cos (t*u) * gammaKernelPartial N u :=
    fun N => gammaRespPartial_eq_kernelPartial
      hcenterC2 hcenterCompact hcenterEven hcenter0 t N
  simpa [hpartial] using htend.neg

theorem gammaRespPartial_centered_tendsto_literal
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgC2 : ContDiff ℝ 2 g)
    (hcompact : HasCompactSupport g)
    (heven : ∀ u, g (-u)=g u)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Λ)
    (hΛ : 0 <= Λ)
    (r t : ℝ) :
    Tendsto
      (fun N => gammaRespPartial N (gammaCenteredTaper g r) t)
      atTop
      (nhds (gammaResp (gammaCenteredTaper g r) t 0)) := by
  let h := gammaCenteredTaper g r
  have hC2 := gammaCenteredTaper_contDiff hgC2 r
  have hcompactH := gammaCenteredTaper_hasCompactSupport hcompact r
  have hevenH := gammaCenteredTaper_even heven r
  have hsuppH : ∀ u, h u ≠ 0 -> |u| <= Λ := by
    intro u hu
    apply hsupp u
    intro hg0
    apply hu
    simp [h, gammaCenteredTaper, hg0]
  have hGammaInt :=
    integrable_gammaIntegrand
      hC2 hcompactH hevenH hsuppH hΛ t 0
  have hCos := cosFT_integrable hC2 hcompactH
  have hCosShift := hCos.comp_sub_right t
  let bound : ℝ → ℝ :=
    fun x =>
      |Zeta23.EF.gammaBracket 0| * |cosFT h (x-t)|
        + |gammaIntegrand h t 0 x|
  have hboundInt : Integrable bound := by
    exact (hCosShift.abs.const_mul _).add hGammaInt.abs
  have hpoint :
      ∀ N x,
      |cosFT h (x-t) * gammaBracketPartial N x|
        <= bound x := by
    intro N x
    have hlo := gammaBracket_zero_le_partial N x
    have hhi := gammaBracketPartial_le N x
    have habs :
        |gammaBracketPartial N x|
          <= |Zeta23.EF.gammaBracket 0|
              + |Zeta23.EF.gammaBracket x| := by
      have h1 :
          gammaBracketPartial N x
            <= |Zeta23.EF.gammaBracket 0|
                + |Zeta23.EF.gammaBracket x| := by
        exact le_trans hhi
          (le_trans (le_abs_self _)
            (le_add_of_nonneg_left (abs_nonneg _)))
      have h2 :
          -( |Zeta23.EF.gammaBracket 0|
                + |Zeta23.EF.gammaBracket x|)
            <= gammaBracketPartial N x := by
        exact le_trans
          (neg_le_neg
            (le_add_of_nonneg_right (le_abs_self _)
              (abs_nonneg _)))
          hlo
      exact abs_le.2 ⟨h2,h1⟩
    unfold bound gammaIntegrand
    rw [abs_mul]
    have hm :=
      mul_le_mul_of_nonneg_left habs
        (abs_nonneg (cosFT h (x-t)))
    nlinarith [abs_nonneg (cosFT h (x-t)),
      abs_nonneg (Zeta23.EF.gammaBracket x)]
  have hlim :
      ∀ x,
      Tendsto
        (fun N => cosFT h (x-t) * gammaBracketPartial N x)
        atTop
        (nhds (gammaIntegrand h t 0 x)) := by
    intro x
    unfold gammaIntegrand
    exact (gammaBracketPartial_tendsto x).const_mul
      (cosFT h (x-t))
  have hIntTend :
      Tendsto
        (fun N =>
          ∫ x : ℝ,
            cosFT h (x-t) * gammaBracketPartial N x)
        atTop
        (nhds (∫ x : ℝ, gammaIntegrand h t 0 x)) := by
    apply tendsto_integral_filter_of_dominated_convergence bound
    · exact Eventually.of_forall fun N => by fun_prop
    · exact Eventually.of_forall fun N =>
        ae_of_all _ (hpoint N)
    · exact hboundInt
    · exact ae_of_all _ hlim
  unfold gammaRespPartial gammaResp
  exact hIntTend.const_mul (1/(2*Real.pi))

/--
Literal centered Gamma kernel identity.
-/
theorem gammaResp_centered_archKernel_exact
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgC2 : ContDiff ℝ 2 g)
    (hcompact : HasCompactSupport g)
    (heven : ∀ u, g (-u)=g u)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Λ)
    (hΛ : 0 <= Λ)
    (r t : ℝ) :
    gammaResp (gammaCenteredTaper g r) t 0
      =
    - ∫ u : ℝ,
      gammaCenteredTaper g r u
        * Real.cos (t*u) * gammaArchKernel |u| := by
  have h1 :=
    gammaRespPartial_centered_tendsto_literal
      hgC2 hcompact heven hsupp hΛ r t
  have h2 :=
    gammaRespPartial_centered_tendsto_kernel
      hgC2 hcompact heven r t
  exact tendsto_nhds_unique h1 h2

end Synthesis
