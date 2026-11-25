import Integration.Paper9HeckeFiniteRemainder
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall

/-! SOURCE-WRITTEN, UNCOMPILED. Mathlib v4.28.0, rev
8f9d9cff6bd728b17a24e163c9402775d9e6a365.
The product proof follows Mathlib NumberTheory/ModularForms/QExpansion
(qExpansion_mul); analytic tail uses Beffara/Kebekus IsolatedZeros.
No new j, Delta, Hecke carrier, or numerical coefficient oracle. -/
namespace Integration.Paper9ActualTaylorUnit
open Complex Filter Function UpperHalfPlane ModularForm FormalMultilinearSeries
open scoped Topology BigOperators
open Integration.Paper9ActualJSourceJet
open Integration.Paper9DiscriminantUnitReflection
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HeckeFiniteRemainder

noncomputable section

def taylor (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (↑n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

theorem taylorCoeff (f : ℂ → ℂ) (n : ℕ) :
    (taylor f).coeff n = (↑n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 := by
  simp [taylor]

theorem taylorCongr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) :
    taylor f=taylor g := by
  ext n
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq n]

-- The same factorial normalization and antidiagonal proof as pinned
-- Mathlib qExpansion_mul, now on the original scalar analytic germs.
theorem taylorMul (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (f*g)=taylor f*taylor g := by
  ext n
  simp only [taylorCoeff,iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.mul_sum,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

theorem taylorId : taylor (fun z : ℂ => z)=PowerSeries.X := by
  ext n
  rw [taylorCoeff,iteratedDeriv_fun_id_zero]
  by_cases hn : n=1
  · subst n; simp [PowerSeries.coeff_X]
  · simp [hn,PowerSeries.coeff_X]

theorem taylorX : taylor x=E4PS := by
  ext n
  simp [taylorCoeff,E4PS,x,qExpansion_coeff]

theorem taylorDelta : taylor deltaQ=deltaPS := by
  ext n
  simp [taylorCoeff,deltaPS,deltaQ,qExpansion_coeff]

theorem actualU : taylor deltaUnit=U := by
  have ha : AnalyticAt ℂ deltaUnit 0 := deltaUnitAnalytic 0 (by norm_num)
  have he : deltaQ =ᶠ[𝓝 0] ((fun z : ℂ => z)*deltaUnit) := by
    filter_upwards [deltaUnitSourceLocal 0 (by norm_num)] with z hz
    exact hz
  have h := taylorCongr he
  rw [taylorDelta,taylorMul _ _ analyticAt_id ha,taylorId,← shiftDelta] at h
  ext n
  have hn := congrArg (fun P : PowerSeries ℂ => P.coeff (n+1)) h
  simpa [PowerSeries.coeff_succ_X_mul] using hn.symm

theorem actualJ : taylor jUnit=J := by
  have hu : AnalyticAt ℂ deltaUnit 0 := deltaUnitAnalytic 0 (by norm_num)
  have hj : AnalyticAt ℂ jUnit 0 := jUnitAnalytic 0 (by norm_num)
  have he : deltaUnit*jUnit =ᶠ[𝓝 0] (x*x)*x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ)<1)]
      with z hz
    have hn := deltaUnitNonzero z (Metric.mem_ball_zero_iff.mp hz)
    change deltaUnit z*(x z^3/deltaUnit z)=x z*x z*x z
    field_simp [hn] <;> ring
  have h := taylorCongr he
  rw [taylorMul _ _ hu hj,actualU,
    taylorMul _ _ (xAnalyticZero.mul xAnalyticZero) xAnalyticZero,
    taylorMul _ _ xAnalyticZero xAnalyticZero,taylorX] at h
  apply JUnique
  simpa [pow_succ] using h

-- The actual analytic series with the same formal J coefficients.
theorem actualJSeries :
    HasFPowerSeriesAt jUnit
      (FormalMultilinearSeries.ofScalars ℂ (fun n => J.coeff n)) 0 := by
  have ha := (jUnitAnalytic 0 (by norm_num)).hasFPowerSeriesAt
  have hc (n : ℕ) : iteratedDeriv n jUnit 0 / (n.factorial : ℂ) = J.coeff n := by
    rw [← actualJ,taylorCoeff,div_eq_mul_inv,mul_comm]
  simpa only [hc] using ha

-- Exact shifted tail, including its value at the cusp. The pinned
-- iterate_dslope/fslope theorem supplies analytic regularity.
theorem seriesTail (f : ℂ → ℂ) (c : ℕ → ℂ)
    (h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0)
    (n : ℕ) :
    Rem n f (fun z => ∑ i ∈ Finset.range n, c i*z^i) := by
  let r := (Function.swap dslope (0 : ℂ))^[n] f
  have hr := h.has_fpower_series_iterate_dslope_fslope n
  refine ⟨r,hr.continuousAt,?_⟩
  have hs := hasFPowerSeriesAt_iff'.mp h
  have ht := hasFPowerSeriesAt_iff'.mp hr
  filter_upwards [hs,ht] with z hz ht'
  simp only [FormalMultilinearSeries.coeff_ofScalars,sub_zero,smul_eq_mul] at hz
  simp only [FormalMultilinearSeries.coeff_iterate_fslope,
    FormalMultilinearSeries.coeff_ofScalars,sub_zero,smul_eq_mul] at ht'
  have hm := ht'.const_smul (z^n)
  have ht'' : HasSum (fun k : ℕ => z^(k+n)*c (k+n)) (z^n*r z) := by
    convert hm using 1
    funext k
    simp [smul_eq_mul,pow_add]
    ring
  have hfull := (hasSum_nat_add_iff' n).mp ht''
  have he := hz.unique hfull
  simp only [mul_comm (z^_)] at he
  linear_combination he

theorem actualJTruncation (m : ℕ) : Rem (m+1) jUnit (truncJ m) :=
  seriesTail _ _ actualJSeries (m+1)

end
end Integration.Paper9ActualTaylorUnit
