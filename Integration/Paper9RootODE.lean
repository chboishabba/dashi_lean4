import Integration.Paper9AnalyticGermClosure

/-! Source-written, uncompiled. Complete intended local product-rule
assembly on the actual normalized branch. Explicit open-set hypotheses
are source geometry, not assumptions of the desired derivative values. -/
namespace Integration.Paper9RootODE

open Complex Filter Set
open scoped Topology
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9AnalyticGermClosure

noncomputable section

def Good (q : ℂ) : Prop :=
  ‖q‖ < 1 ∧ x q ∈ Complex.slitPlane ∧ y q ≠ 0

theorem goodZero : Good 0 := by
  simp [Good,xZero,yZero,Complex.slitPlane]

theorem aZero : aCoord 0 = 0 := by simp [aCoord,e2QZero,xZero,yZero]
theorem hZero : hCoord 0 = 0 := by simp [hCoord,xZero,yZero]

theorem goodLocal (q : ℂ) (hq : Good q) :
    ∀ᶠ w in 𝓝 q, Good w := by
  have hd : ∀ᶠ w in 𝓝 q, ‖w‖ < 1 :=
    (continuous_norm.continuousAt.eventually_lt continuousAt_const hq.1)
  have hx := (xDifferentiable q hq.1).continuousAt
    (Complex.isOpen_slitPlane.mem_nhds hq.2.1)
  have hy : ∀ᶠ w in 𝓝 q, y w ≠ 0 :=
    (yDifferentiable q hq.1).continuousAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hq.2.2))
  filter_upwards [hd,hx,hy] with w h1 h2 h3
  exact ⟨h1,h2,h3⟩

theorem rootFirstAll (q : ℂ) (hq : Good q) :
    L rootF q = aCoord q*rootF q := by
  by_cases h : q = 0
  · subst q; simp [L,euler,aZero]
  · exact rootFirst q hq.1 h hq.2.1 hq.2.2

theorem aFlowAll (q : ℂ) (hq : Good q) :
    L aCoord q = aFlow (aCoord q) (hCoord q) := by
  by_cases h : q = 0
  · subst q; simp [L,euler,aFlow,aZero,hZero]
  · exact aTransport q hq.1 h hq.2.2

theorem hFlowAll (q : ℂ) (hq : Good q) :
    L hCoord q = hFlow (hCoord q) := by
  by_cases h : q = 0
  · subst q; simp [L,euler,hFlow,hZero]
  · exact hTransport q hq.1 h hq.2.2

theorem zFlowAll (q : ℂ) (hq : Good q) : L zCoord q = zCoord q := by
  by_cases h : q = 0
  · subst q; simp [L,euler,zZero]
  · exact zTransport q hq.1 h (Complex.slitPlane_ne_zero hq.2.1) hq.2.2

theorem aDiff (q : ℂ) (hq : Good q) : DifferentiableAt ℂ aCoord q := by
  unfold aCoord
  exact ((((e2QAnalytic q hq.1).differentiableAt.mul (xDifferentiable q hq.1)).div
    (yDifferentiable q hq.1) hq.2.2).sub_const 1).div_const 6

theorem hDiff (q : ℂ) (hq : Good q) : DifferentiableAt ℂ hCoord q := by
  unfold hCoord
  exact (((xDifferentiable q hq.1).pow 3).div
    ((yDifferentiable q hq.1).pow 2) (pow_ne_zero _ hq.2.2)).sub_const 1

theorem rootDiff (q : ℂ) (hq : Good q) : DifferentiableAt ℂ rootF q :=
  (rootFDeriv q hq.1 hq.2.1).differentiableAt

theorem LcongrAt (q : ℂ) {f g : ℂ → ℂ}
    (h : f =ᶠ[𝓝 q] g) : L f q = L g q := by
  unfold L euler
  rw [h.deriv_eq]

theorem Lprod (f g : ℂ → ℂ) (q : ℂ)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g q) :
    L (fun z => f z*g z) q = L f q*g q+f q*L g q := by
  unfold L euler
  rw [(hf.hasDerivAt.mul hg.hasDerivAt).deriv]
  ring

def bAt (q : ℂ) : ℂ := bCoord (aCoord q) (hCoord q)

theorem bDiff (q : ℂ) (hq : Good q) : DifferentiableAt ℂ bAt q := by
  unfold bAt bCoord
  exact (((aDiff q hq).pow 2).div_const 2).add
    ((hDiff q hq).mul (((aDiff q hq).div_const 2).add_const (5/72)))

theorem bTransport (q : ℂ) (hq : Good q) :
    L bAt q = (aCoord q+hCoord q/2)*L aCoord q+
      (aCoord q/2+5/72)*L hCoord q := by
  have ha := (aDiff q hq).hasDerivAt
  have hh := (hDiff q hq).hasDerivAt
  have hd := ((ha.pow 2).div_const 2).add
    (hh.mul ((ha.div_const 2).add_const (5/72)))
  unfold L euler bAt bCoord
  rw [hd.deriv]
  ring

theorem rootSecond (q : ℂ) (hq : Good q) :
    L2 rootF q = bAt q*rootF q := by
  have hlocal : L rootF =ᶠ[𝓝 q] fun z => aCoord z*rootF z :=
    (goodLocal q hq).mono fun z hz => rootFirstAll z hz
  change L (L rootF) q = _
  rw [LcongrAt q hlocal,Lprod aCoord rootF q (aDiff q hq) (rootDiff q hq),
    aFlowAll q hq,rootFirstAll q hq]
  unfold bAt
  rw [← secondMultiplier]
  ring

theorem rootThird (q : ℂ) (hq : Good q) :
    L3 rootF q =
      hCoord q*(3/2*bAt q+23/36*aCoord q+5/72)*rootF q := by
  have hlocal : L2 rootF =ᶠ[𝓝 q] fun z => bAt z*rootF z :=
    (goodLocal q hq).mono fun z hz => rootSecond z hz
  change L (L2 rootF) q = _
  rw [LcongrAt q hlocal,Lprod bAt rootF q (bDiff q hq) (rootDiff q hq),
    bTransport q hq,aFlowAll q hq,hFlowAll q hq,rootFirstAll q hq]
  unfold bAt
  rw [← thirdMultiplier]
  ring

theorem rootODE (q : ℂ) (hq : Good q) : ode rootF q = 0 := by
  have hz := (coordBridge (x q) (y q) (Complex.slitPlane_ne_zero hq.2.1) hq.2.2).1
  have h := odeFromMultiplier (rootF q) (L rootF q) (L2 rootF q)
    (L3 rootF q) (aCoord q) (hCoord q) (zCoord q)
    (rootFirstAll q hq) (rootSecond q hq) (rootThird q hq) hz
  unfold ode
  exact sub_eq_zero.mpr h

theorem rootODEGerm : ode rootF =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 :=
  (goodLocal 0 goodZero).mono fun q hq => rootODE q hq

-- This is the only analytic equation missing for the second solution.
-- No arbitrary scalar equality is accepted as evidence of that equation.
theorem rootEqualsHyperGerm
    (hF : AnalyticAt ℂ rootF 0)
    (hH : AnalyticAt ℂ (H ∘ zCoord) 0)
    (hode : ode (H ∘ zCoord) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0) :
    rootF =ᶠ[𝓝 (0 : ℂ)] H ∘ zCoord := by
  apply normalizedGermUnique rootF (H ∘ zCoord) hF hH
  · simp [rootFZero,Function.comp_def,zZero,HZero]
  · exact rootODEGerm
  · exact hode

end
end Integration.Paper9RootODE
