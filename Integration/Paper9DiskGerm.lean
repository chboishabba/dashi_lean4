import Integration.Paper9DiskGeometry
import Integration.Paper9CMExpWindow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! SOURCE-WRITTEN, UNCOMPILED. The original Taylor remainder pays
the normalized disk germ, both literal Hecke branches, and the finite
complement's continuity. No new j, inverse j, or derivative of the
forty-factor residual. The endpoint retains the eight finite checks. -/
namespace Integration.Paper9DiskGerm
open Complex Filter Function UpperHalfPlane
open scoped Topology BigOperators
open Integration.Paper9ActualCMPoint
open Integration.Paper9OriginalCMChartWeld
open Integration.Paper9MobiusDiskPeriod
open Integration.Paper9DiskGeometry
open Integration.Paper9ActualJSourceJet
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9HeckePoleRemoval
open Integration.Paper9Hecke41ChartGeometry hiding (a)
open Integration.Paper9ScalarReciprocal
open Integration.Paper9ActualCMRoot
open Integration.Paper9ScalarCross
open Integration.Paper9ActualCross
open Integration.Paper9ExecutableCM163

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def A : ℂ := a*d
def B : ℂ := a*d+b*d^2/2
def L (w : ℂ) : ℂ := d/(1-w)

theorem LZero : L 0=d := by simp [L]
theorem LDeriv : HasDerivAt L d 0 := by
  have h := (hasDerivAt_const (0:ℂ) d).div
    ((hasDerivAt_const (0:ℂ) (1:ℂ)).sub (hasDerivAt_id 0)) (by simp)
  simpa [L] using h

-- The sole derivative rule for a continuous residual. No differentiability
-- of f is needed at zero or elsewhere.
theorem coordinateMulDeriv (f : ℂ → ℂ) (hf : ContinuousAt f 0) :
    HasDerivAt (fun w => w*f w) (f 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have ht : Tendsto f (𝓝[≠] (0:ℂ)) (𝓝 (f 0)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hn : w≠0 := by simpa using hw
  simp [smul_eq_mul,← mul_assoc,hn]

theorem denominatorLocal (c : ℂ) :
    ∀ᶠ w in 𝓝 (0:ℂ), 1-c*w≠0 := by
  have h : ContinuousAt (fun w : ℂ => 1-c*w) 0 := by fun_prop
  exact h.eventually_ne (by simp)

-- Pull back the ORIGINAL Taylor tail along u=w*d/(1-w).
-- Its coefficient at w=0 remains the actual derivative.
theorem actualNormalizedGerm (hj : j cmTau=(K:ℂ)) :
    ∃ X : ℂ → ℂ, X 0=A ∧ HasDerivAt X B 0 ∧
      ∀ᶠ w in 𝓝 (0:ℂ), jExt (undisk w)-(K:ℂ)=w*X w := by
  obtain ⟨r,hr,he⟩ := centeredJTaylor
  let u : ℂ → ℂ := fun w => w*L w
  have hu : ContinuousAt u 0 := continuousAt_id.mul LDeriv.continuousAt
  have hu0 : u 0=0 := by simp [u]
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by simpa [hu0] using hu.tendsto
  let R : ℂ → ℂ := fun w => L w^3*r (u w)
  have hR : ContinuousAt R 0 :=
    (LDeriv.continuousAt.pow 3).mul (hr.comp_of_eq hu hu0)
  let X : ℂ → ℂ := fun w => a*L w+(b/2)*w*L w^2+w*(w*R w)
  have htail := coordinateMulDeriv (fun w => w*R w)
    (continuousAt_id.mul hR)
  have h1 := LDeriv.const_mul a
  have h2 := (coordinateMulDeriv (fun w => L w^2)
    (LDeriv.continuousAt.pow 2)).const_mul (b/2)
  have hX : HasDerivAt X B 0 := by
    convert (h1.add h2).add htail using 1
    · funext w
      dsimp [X]
      ring
    · simp [B,LZero]
      ring
  refine ⟨X,by simp [X,A,LZero],hX,?_⟩
  filter_upwards [ht.eventually he] with w hw
  have hwu : undisk w=u w+cmPoint := by
    unfold undisk u L
    ring
  rw [hwu]
  change centeredJ (u w)-(K:ℂ)=w*X w
  rw [hj] at hw
  dsimp [u] at hw
  dsimp [X,R,u]
  linear_combination hw

-- All three branches on the original indexed chart, with denominators
-- excluded locally, not by deleting the center.
theorem actualThreeBranches (X : ℂ → ℂ)
    (h : ∀ᶠ w in 𝓝 (0:ℂ), jExt (undisk w)-(K:ℂ)=w*X w) :
    (∀ᶠ w in 𝓝 (0:ℂ), j (diskTau w)-(K:ℂ)=w*X w) ∧
    (∀ᶠ w in 𝓝 (0:ℂ), chartValue 1 (diskTau w)-(K:ℂ)=
      w*(alpha*X (alpha*w))) ∧
    (∀ᶠ w in 𝓝 (0:ℂ), chartValue 0 (diskTau w)-(K:ℂ)=
      w*(alpha⁻¹*X (alpha⁻¹*w))) := by
  have hc (c : ℂ) : Tendsto (fun w : ℂ => c*w) (𝓝 0) (𝓝 0) := by
    have h' : ContinuousAt (fun w : ℂ => c*w) 0 := by fun_prop
    simpa using h'.tendsto
  have hden : ∀ᶠ w in 𝓝 (0:ℂ), 1-w≠0 := by
    simpa using denominatorLocal 1
  refine ⟨?_,?_,?_⟩
  · filter_upwards [diskTauLocal,h] with w hw he
    rw [← jExtAt (diskTau w),hw]
    exact he
  · filter_upwards [diskTauLocal,hden,denominatorLocal alpha,
      (hc alpha).eventually h] with w hw hd ha he
    rw [forwardChartValue,hw,forwardUndisk w hd ha]
    linear_combination he
  · filter_upwards [diskTauLocal,hden,denominatorLocal alpha⁻¹,
      (hc alpha⁻¹).eventually h] with w hw hd ha he
    rw [reverseChartValue,hw,reverseUndisk w hd ha]
    linear_combination he

-- Original affine chart and actual j extension imply continuity at the
-- disk center for EVERY chart, including all forty residual indices.
theorem chartContinuous (i : Chart) :
    ContinuousAt (fun w => chartValue i (diskTau w)) 0 := by
  have ha : ContinuousAt (fun w => chartAffine i (undisk w)) 0 :=
    (chartAffineAnalytic i cmPoint).continuousAt.comp_of_eq
      undiskContinuous undiskZero
  have he : chartAffine i (undisk 0)=(chartPoint i cmTau : ℂ) := by
    rw [undiskZero]
    exact chartAffineAt i cmTau
  have hc : ContinuousAt (fun w => jExt (chartAffine i (undisk w))) 0 :=
    (jExtAnalytic (chartPoint i cmTau)).continuousAt.comp_of_eq ha he
  have heq : (fun w => chartValue i (diskTau w)) =ᶠ[𝓝 (0:ℂ)]
      (fun w => jExt (chartAffine i (undisk w))) := by
    filter_upwards [diskTauLocal] with w hw
    unfold chartValue
    rw [← jExtAt,← chartAffineAt,hw]
  exact hc.congr heq.symm

-- Each coefficient of a finite product is a finite convolution of
-- continuous coefficients; use the literal polynomial carrier.
theorem restCoeffContinuous (s : Finset Chart) (n : ℕ) :
    ContinuousAt (fun w : ℂ =>
      (∏ i ∈ s, (Polynomial.X+Polynomial.C
        ((K:ℂ)-chartValue i (diskTau w)))).coeff n) 0 := by
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | @insert i s hi ih =>
    have hc (k : ℕ) : ContinuousAt (fun w : ℂ =>
        (Polynomial.X+Polynomial.C ((K:ℂ)-chartValue i (diskTau w))).coeff k) 0 := by
      simp only [Polynomial.coeff_add,Polynomial.coeff_X,Polynomial.coeff_C]
      split <;> split <;> first
        | exact continuousAt_const
        | exact continuousAt_const.add (continuousAt_const.sub (chartContinuous i))
    simp only [Finset.prod_insert hi,Polynomial.coeff_mul]
    apply continuousAt_finset_sum
    intro k hk
    exact (hc k.1).mul (ih k.2)

theorem restSlopeContinuous (Y : ℂ → ℂ) (hY : ContinuousAt Y 0) :
    ContinuousAt (fun w => (restSlope (diskTau w)).eval (Y w)) 0 := by
  simp only [restSlope,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  apply continuousAt_finset_sum
  intro i hi
  exact (restCoeffContinuous remaining (i+1)).mul (hY.pow i)

theorem polyGerm (Q : Polynomial ℂ) (X : ℂ → ℂ)
    (h0 : X 0=A) (hX : HasDerivAt X B 0) :
    HasDerivAt (fun w => Q.eval (w*X w)) (Q.coeff 1*A) 0 := by
  have h := coordinateMulDeriv X hX.continuousAt
  rw [h0] at h
  have hd := (Q.hasDerivAt 0).comp_of_eq h (by simp)
  simpa [Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative,
    Function.comp_def] using hd

-- Reciprocal branch products: retain alpha and alpha^-1 separately
-- until the exact trace identity is applied.
theorem branchProducts (X : ℂ → ℂ) (x0 : X 0=A)
    (hx : HasDerivAt X B 0) :
    let Xp := fun w => alpha*X (alpha*w)
    let Xm := fun w => alpha⁻¹*X (alpha⁻¹*w)
    let N := fun w => Xp w*Xm w
    let M := fun w => (X w-Xp w)*(X w-Xm w)
    N 0=A^2 ∧ M 0=(163/41)*A^2 ∧
    HasDerivAt N (-(81/41)*A*B) 0 ∧
    HasDerivAt M ((163/1681)*A*B) 0 := by
  dsimp
  have hi : alpha*alpha⁻¹=1 := mul_inv_cancel₀ alphaNe
  have htr := alphaTrace
  have hp := (hx.comp_of_eq (hasDerivAt_const_mul alpha) (by simp)).const_mul alpha
  have hm := (hx.comp_of_eq (hasDerivAt_const_mul alpha⁻¹) (by simp)).const_mul alpha⁻¹
  have hpn : HasDerivAt (fun w => alpha*X (alpha*w)) (B*alpha^2) 0 := by
    convert hp using 1 <;> simp [Function.comp_def] <;> ring
  have hmn : HasDerivAt (fun w => alpha⁻¹*X (alpha⁻¹*w)) (B*(alpha⁻¹)^2) 0 := by
    convert hm using 1 <;> simp [Function.comp_def] <;> ring
  have hn := hpn.mul hmn
  have hM := (hx.sub hpn).mul (hx.sub hmn)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [mul_zero,x0]
    calc
      _ = (alpha*alpha⁻¹)*A^2 := by ring
      _ = _ := by rw [hi,one_mul]
  · simp only [mul_zero,x0]
    linear_combination A^2*hi-A^2*htr
  · convert hn using 1
    simp only [mul_zero,x0]
    linear_combination A*B*(alpha+alpha⁻¹)*hi+A*B*htr
  · convert hM using 1
    simp only [mul_zero,x0]
    have hsq : alpha^2+(alpha⁻¹)^2=(81/41:ℂ)^2-2 := by
      linear_combination (alpha+alpha⁻¹-81/41)*htr-2*hi
    linear_combination A*B*(-hsq+(alpha+alpha⁻¹)*hi)

-- All analytic inputs are constructed above. Only literal finite
-- predicates and the selected original CM root are arguments.
theorem actualDiskCorrection (hu : unitOK=true) (hd : diagOK=true)
    (hs : sliceOK=true) (hc : jetOK=true)
    (hj : j cmTau=(K:ℂ)) :
    2*(a*d+b*d^2/2)/(a*d)^2 =
      (41*(shiftedZ 3:ℂ)-326*(sliceShiftZ 3:ℂ))/(163*(sliceShiftZ 2:ℂ)) := by
  obtain ⟨X,x0,hX,hg⟩ := actualNormalizedGerm hj
  obtain ⟨h0,hp,hm⟩ := actualThreeBranches X hg
  let Xp := fun w => alpha*X (alpha*w)
  let Xm := fun w => alpha⁻¹*X (alpha⁻¹*w)
  let N := fun w => Xp w*Xm w
  let M := fun w => (X w-Xp w)*(X w-Xm w)
  let p := fun w => complement.eval (w*X w)
  let s := fun w => sliceComplement.eval (w*X w)
  let T := fun w => (restSlope (diskTau w)).eval (w*X w)
  obtain ⟨n0,m0,hn,hM⟩ := branchProducts X x0 hX
  have hp0 : p 0=(shiftedZ 2:ℂ) := by
    simp [p,← Polynomial.coeff_zero_eq_eval_zero,complementCoeff]
  have hs0 : s 0=(sliceShiftZ 2:ℂ) := by
    simp [s,← Polynomial.coeff_zero_eq_eval_zero,sliceComplementCoeff]
  have hpd := polyGerm complement X x0 hX
  rw [complementCoeff] at hpd
  have hsd := polyGerm sliceComplement X x0 hX
  rw [sliceComplementCoeff] at hsd
  have hTc : ContinuousAt T 0 :=
    restSlopeContinuous _ (continuousAt_id.mul hX.continuousAt)
  have hT0 : T 0=(sliceShiftZ 3:ℂ) := by
    simpa [T,diskTauZero] using actualTZero hu hs hc hj
  have hw := coordinateMulDeriv T hTc
  rw [hT0] at hw
  have he := normalizedActualCross hu hd hs hc diskTau X Xp Xm A h0 hp hm n0 m0
  obtain ⟨_,_,_,_,hS,_,_⟩ := jetFacts hc
  have hA : A≠0 := mul_ne_zero (aNonzero (by simpa [K] using hj)) dNe
  exact crossPeriodOfCross X N M p s T A B
    (shiftedZ 2:ℂ) (shiftedZ 3:ℂ) (sliceShiftZ 2:ℂ) (sliceShiftZ 3:ℂ)
    hA hS x0 n0 m0 hp0 hs0 hX hn hM hpd hsd hw he

-- A4 plus A5 plus the already existing positive A7 period.
-- The six root and two slice/jet checks are the ONLY explicit inputs.
theorem literalPrefixFromFiniteChecks
    (hu : unitOK=true) (hd : diagOK=true) (hz : shiftOK=true)
    (hs : sliceOK=true) (hc : jetOK=true)
    (hp : Integration.Paper9CMOriginalMachinWindow.piRoundOK)
    (hq : Integration.Paper9CMOriginalMachinWindow.sqrtRoundOK)
    (hw : Integration.Paper9CMExpWindow.expWindowOK) :
    Tendsto (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N : ℂ))
      atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi : ℝ) : ℂ)) := by
  have hj := Integration.Paper9CMExpWindow.rootFromOriginalFiniteChecks hu hd hz hp hq hw
  exact literalPeriodFromDisk (by simpa [K] using hj) hc
    (actualDiskCorrection hu hd hs hc hj)

end
end Integration.Paper9DiskGerm
