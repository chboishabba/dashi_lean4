import Integration.Paper9ActualCMPoint

/-! SOURCE-WRITTEN, UNCOMPILED.
Actual j, not a new j carrier. Reuse the already-owned positive-weight
transformation, eta/Delta identity, analytic q unit, Ramanujan system,
and signed CM point. The Hecke polynomial and dyadic reflection remain
separate obligations. -/
namespace Integration.Paper9ActualJSourceJet

open Complex Function Filter UpperHalfPlane
open scoped Topology Real
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9EulerMobiusTransport
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9SelectedCMDomain
open Integration.Paper9ActualCMPoint

local notation "E₄" => Integration.MoonshineEisensteinAnalytic.E4
local notation "Δ" => Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit
local notation "Δf" => Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

noncomputable section

-- Full SL2 invariance is just cancellation of the common weight 12.
-- The old S-only theorem is not the entire Hecke prerequisite.
theorem jInvariant (g : SL(2, ℤ)) (t : ℍ) : j (g • t) = j t := by
  have h4 := formTransform 3 E₄ g t
  have hd := formTransform 11 Δf g t
  simp only [Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply] at hd
  have hn := linear_ne_zero g t
  have hΔ := Integration.MoonshineDeltaFinalMinCut.normalizedDelta_ne_zero_canonical t
  unfold Integration.MoonshineEisensteinAgdaTarget.jTarget
  rw [h4,hd]
  field_simp [hn,hΔ] <;> ring

-- Actual normalized J(q)=q*j(q) including the retained cusp zero mode.
def jUnit (q : ℂ) : ℂ := x q^3/deltaUnit q
def jQ (q : ℂ) : ℂ := jUnit q/q
def jExt (t : ℂ) : ℂ := jQ (qExt t)

theorem jUnitZero : jUnit 0 = 1 := by simp [jUnit,xZero,deltaUnitZero]

theorem jUnitAnalytic (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ jUnit q :=
  ((xAnalyticDisk q hq).pow 3).div (deltaUnitAnalytic q hq)
    (deltaUnitNonzero q hq)

theorem jQAnalytic (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0) :
    AnalyticAt ℂ jQ q :=
  (jUnitAnalytic q hq).div analyticAt_id hn

theorem actualJUnit (t : ℍ) :
    jUnit (qExt t) = qExt t*j t := by
  have hn : qExt t ≠ 0 := Periodic.qParam_ne_zero 1 t
  have hu := deltaUnitNonzero (qExt t) (qNorm t)
  have hs := deltaUnitSourceOnDisk (Metric.mem_ball_zero_iff.mpr (qNorm t))
  have hd : deltaQ (qExt t) = Δ t :=
    (formExtAt Δf t).trans
      (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply t)
  change deltaQ (qExt t) = qExt t * deltaUnit (qExt t) at hs
  unfold jUnit Integration.MoonshineEisensteinAgdaTarget.jTarget
  rw [show x (qExt t) = E₄ t from xAtQ t,← hd,hs]
  field_simp [hn,hu] <;> ring

theorem jExtAt (t : ℍ) : jExt t = j t := by
  have hn : qExt t ≠ 0 := Periodic.qParam_ne_zero 1 t
  unfold jExt jQ
  rw [actualJUnit]
  field_simp [hn]

-- First two actual Euler derivatives; these retain the signed quotient
-- and use the original q flow rather than a local inverse of j.
theorem jQEuler (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0)
    (hx : x q ≠ 0) :
    euler jQ q = -jQ q*y q/x q := by
  have hu := deltaUnitNonzero q hq
  obtain ⟨_,hxD,_⟩ := ramanujanQ q hq hn
  have hdx : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    unfold euler at hxD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hxD
  have hd := (((xDifferentiable q hq).hasDerivAt.pow 3).div
    (deltaUnitAnalytic q hq).differentiableAt.hasDerivAt hu).div
      (hasDerivAt_id q) hn
  unfold euler jQ jUnit
  rw [hd.deriv,hdx]
  unfold e2Q
  field_simp [hn,hu,hx] <;> ring

def jFirst (t : ℂ) : ℂ :=
  -scaleD*jExt t*y (qExt t)/x (qExt t)

def secondEuler (q : ℂ) : ℂ :=
  jQ q*(-e2Q q*x q*y q+3*x q^3+4*y q^2)/(6*x q^2)

theorem jExtDeriv (t : ℂ) (hq : ‖qExt t‖ < 1)
    (hn : qExt t ≠ 0) (hx : x (qExt t) ≠ 0) :
    HasDerivAt jExt (jFirst t) t := by
  have h := ((jQAnalytic (qExt t) hq hn).differentiableAt.hasDerivAt).comp
    t (qExtDeriv t)
  have he := jQEuler (qExt t) hq hn hx
  unfold euler at he
  have hval : deriv jQ (qExt t)*(scaleD*qExt t) = jFirst t := by
    unfold jFirst jExt
    linear_combination scaleD*he
  simpa [jExt,Function.comp_def,hval] using h

theorem jFirstDeriv (t : ℂ) (hq : ‖qExt t‖ < 1)
    (hn : qExt t ≠ 0) (hx : x (qExt t) ≠ 0) :
    HasDerivAt jFirst (scaleD^2*secondEuler (qExt t)) t := by
  let q := qExt t
  obtain ⟨_,hxD,hyD⟩ := ramanujanQ q hq hn
  have hdx : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    unfold euler at hxD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hxD
  have hdy : deriv y q = (e2Q q*y q-x q^2)/(2*q) := by
    unfold euler at hyD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hyD
  have hX := (xDifferentiable q hq).hasDerivAt.comp t (qExtDeriv t)
  have hY := (yDifferentiable q hq).hasDerivAt.comp t (qExtDeriv t)
  have hj := jExtDeriv t hq hn hx
  have h := ((hj.const_mul (-scaleD)).mul hY).div hX hx
  convert h using 1
  · rfl
  · change scaleD^2*secondEuler q = _
    rw [hdx,hdy]
    unfold secondEuler jFirst jExt
    field_simp [hn,hx] <;> ring

-- This is a second derivative of the ACTUAL local j extension.
theorem jExtSecond (t : ℂ) (hq : ‖qExt t‖ < 1)
    (hn : qExt t ≠ 0) (hx : x (qExt t) ≠ 0) :
    deriv (deriv jExt) t = scaleD^2*secondEuler (qExt t) := by
  have hqc := (qExtDeriv t).continuousAt
  have hxc := (xDifferentiable (qExt t) hq).continuousAt.comp hqc
  have hlocal : ∀ᶠ w in 𝓝 t,
      ‖qExt w‖ < 1 ∧ qExt w ≠ 0 ∧ x (qExt w) ≠ 0 := by
    filter_upwards
      [continuous_norm.continuousAt.comp hqc |>.eventually_lt continuousAt_const hq,
       hqc (isOpen_compl_singleton.mem_nhds (by simpa using hn)),
       hxc (isOpen_compl_singleton.mem_nhds (by simpa using hx))]
      with w hw hwn hwx
    exact ⟨hw,hwn,hwx⟩
  have he : deriv jExt =ᶠ[𝓝 t] jFirst :=
    hlocal.mono fun w hw => (jExtDeriv w hw.1 hw.2.1 hw.2.2).deriv
  rw [he.deriv_eq,(jFirstDeriv t hq hn hx).deriv]

-- Reverse-solve the correction on the authentic signed scale.
-- p is pi*Im(tau), NOT pi*sqrt(163).
theorem correctionFromJet (X Y e J p k : ℂ)
    (hx : X ≠ 0) (hy : Y ≠ 0) (hj : J ≠ 0) (hp : p ≠ 0)
    (hk : k = (J*(-e*X*Y+3*X^3+4*Y^2)/(6*X^2))/
      (J*Y/X)^2+X/(2*J*p*Y)) :
    4+3*X^3/Y^2-6*J*k = (X/Y)*(e-3/p) := by
  rw [hk]
  field_simp [hx,hy,hj,hp] <;> ring

theorem reopenCorrection (X Y e J p k : ℂ)
    (hx : X ≠ 0) (hy : Y ≠ 0) (hj : J ≠ 0) (hp : p ≠ 0)
    (hk : 4+3*X^3/Y^2-6*J*k = (X/Y)*(e-3/p)) :
    k = (J*(-e*X*Y+3*X^3+4*Y^2)/(6*X^2))/
      (J*Y/X)^2+X/(2*J*p*Y) := by
  apply (mul_left_cancel₀ (show 6*J ≠ 0 by positivity))
  have h := correctionFromJet X Y e J p
    ((J*(-e*X*Y+3*X^3+4*Y^2)/(6*X^2))/(J*Y/X)^2+X/(2*J*p*Y))
    hx hy hj hp rfl
  linear_combination h-hk

end
end Integration.Paper9ActualJSourceJet
