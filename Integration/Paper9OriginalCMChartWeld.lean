import Integration.Paper9SeparatedCusp
import Integration.Paper9SignedCMPeriod
import Integration.BishopVendoredMachinPiSemantics
import Integration.BishopVendoredExponentialSemantics

/-! SOURCE-WRITTEN, UNCOMPILED. Reuse the original scalar Taylor tail
(seriesTail), jExt derivatives, selected CM positivity, and Machin
and exponential semantic owners. No new Taylor analytic theory. -/
namespace Integration.Paper9OriginalCMChartWeld
open Complex Filter UpperHalfPlane Function
open scoped Topology BigOperators
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet
open Integration.Paper9ActualTaylorUnit
open Integration.Paper9HeckePoleRemoval
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9SignedCMPeriod
open Integration.Paper9EulerMobiusTransport

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def centeredJ (u : ℂ) := jExt (u+cmPoint)
def a : ℂ := deriv jExt cmPoint
def b : ℂ := deriv (deriv jExt) cmPoint

theorem centeredJAnalytic : AnalyticAt ℂ centeredJ 0 := by
  have h : AnalyticAt ℂ jExt cmPoint := jExtAnalytic cmTau
  have hi : AnalyticAt ℂ (fun u : ℂ => u+cmPoint) 0 :=
    analyticAt_id.add analyticAt_const
  simpa [centeredJ] using h.comp hi

theorem centeredJTaylor :
    Rem 3 centeredJ (fun u => j cmTau+a*u+b*u^2/2) := by
  have h := seriesTail centeredJ _ centeredJAnalytic.hasFPowerSeriesAt 3
  convert h using 1
  funext u
  unfold centeredJ a b
  simp [Finset.sum_range_succ,iteratedDeriv_comp_add_const,iteratedDeriv_succ,
    Nat.factorial,show jExt cmPoint=j cmTau from jExtAt cmTau]
  ring

-- The actual first jet is already nonzero from the existing positivity
-- bands and exact CM integer. No inverse j chart is used.
theorem aNonzero (hj : j cmTau=-(640320:ℂ)^3) : a≠0 := by
  have h := (jExtDeriv (cmTau:ℂ) (qNorm cmTau) cmQNonzero cmXNonzero).deriv
  unfold a
  change deriv jExt (cmTau:ℂ)≠0
  rw [h]
  unfold jFirst
  rw [jExtAt,hj]
  unfold scaleD
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (by
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hpi)
      Complex.I_ne_zero)) (by norm_num)) cmYNonzero) cmXNonzero

def centeredHecke (u : ℂ) := hecke (u+cmPoint)-cmPoint

-- Exact rational remainder, stronger than a derivative-limit argument.
theorem centeredHeckeTaylor :
    Rem 3 centeredHecke
      (fun u => tangent cmPoint*u+secondTangent cmPoint*u^2/2) := by
  let z := cmPoint+1
  have hz : z≠0 := cmApart
  have hc : ContinuousAt (fun u : ℂ => z+u) 0 := continuousAt_const.add continuousAt_id
  refine ⟨fun u => 41/(z^3*(z+u)),?_,?_⟩
  · exact continuousAt_const.div (continuousAt_const.mul hc)
      (by simpa using mul_ne_zero (pow_ne_zero 3 hz) hz)
  have he : ∀ᶠ u in 𝓝 (0:ℂ), z+u≠0 :=
    hc.eventually_ne (by simpa using hz)
  filter_upwards [he] with u hu
  have hf := fixedPoint
  unfold hecke at hf
  unfold centeredHecke hecke tangent secondTangent
  have hu' : u+cmPoint+1=z+u := by dsimp [z]; ring
  rw [hu',← hf]
  change -41/(z+u)-(-41/z)-(41/z^2*u+(-82/z^3)*u^2/2)=
    u^3*(41/(z^3*(z+u)))
  field_simp [hz,hu] <;> ring

-- Actual branch, not only the CM fixed-point evaluation.
theorem heckeChartAt (τ : ℍ) :
    ((ModularGroup.S • chartPoint 1 τ : ℍ):ℂ)=hecke τ := by
  rw [UpperHalfPlane.modular_S_smul]
  change -(((τ:ℂ)+1)/41)⁻¹= -41/((τ:ℂ)+1)
  ring

theorem branchVanish (τ : ℍ) :
    actualProduct τ (j (ModularGroup.S • chartPoint 1 τ))=0 := by
  unfold actualProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (1:Chart))
  unfold chartValue
  rw [Integration.MoonshineEisensteinAgdaTarget.jTarget_S_invariant,sub_self]

-- A7 consumes exactly the signed scalar combination from A5.
theorem correctionFromTransverse (P3 S2 S3 : ℂ)
    (ha : a≠0) (hs : S2≠0)
    (h : 163*S2*((tangent cmPoint^2-tangent cmPoint)*b+a*secondTangent cmPoint)=
      a^2*(tangent cmPoint^2-tangent cmPoint)*(41*P3-326*S3)) :
    b/a^2+2/((2*cmPoint+1)*a)=(41*P3-326*S3)/(163*S2) := by
  let al := tangent cmPoint
  have hf : 41*al^2+81*al+41=0 := tangentPolynomial
  have hn0 : al≠0 := by intro he; rw [he] at hf; norm_num at hf
  have hn1 : al-1≠0 := by
    intro he
    have hh : al=1 := sub_eq_zero.mp he
    rw [hh] at hf
    norm_num at hf
  have hn : al^2-al≠0 := by
    rw [show al^2-al=al*(al-1) by ring]
    exact mul_ne_zero hn0 hn1
  have hz : 2*cmPoint+1≠0 := by
    intro he
    have hh := gammaIdentity
    rw [he, mul_zero] at hh
    exact hn (by linear_combination -hh/2)
  have hg := gammaIdentity
  change secondTangent cmPoint*(2*cmPoint+1)=2*(al^2-al) at hg
  have hgamma : secondTangent cmPoint=2*(al^2-al)/(2*cmPoint+1) :=
    (eq_div_iff hz).2 hg
  change 163*S2*((al^2-al)*b+a*secondTangent cmPoint)=
    a^2*(al^2-al)*(41*P3-326*S3) at h
  rw [hgamma] at h
  apply (mul_left_cancel₀ (show 163*S2*(al^2-al)*a^2*(2*cmPoint+1)≠0 by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) hn)
      (pow_ne_zero 2 ha)) hz))
  field_simp [ha,hs,hz] at h ⊢
  linear_combination h

end
end Integration.Paper9OriginalCMChartWeld
