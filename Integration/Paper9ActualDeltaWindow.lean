import Integration.Paper9SignedEisensteinCuspTail

/-! SOURCE-WRITTEN, UNCOMPILED. Actual normalized Delta unit from
the signed original E4/E6 tails. All estimates retain the same q.
No new cusp form or Monster representation assumption. -/
namespace Integration.Paper9ActualDeltaWindow
open Complex UpperHalfPlane
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9ActualJSourceJet
open Integration.Paper9SignedEisensteinCuspTail
open Integration.Paper9ActualCMPoint
open Integration.Paper9CMNormalizedCuspWindow

noncomputable section

theorem smallBands (q u v : ℂ)
    (hr : ‖q‖≤(1/2:ℝ)^36)
    (h4 : ‖u-240*q-2160*q^2‖≤38880*‖q‖^3)
    (h6 : ‖v+504*q+16632*q^2‖≤734832*‖q‖^3) :
    ‖u-240*q‖≤2161*‖q‖^2 ∧ ‖u‖≤241*‖q‖ ∧
    ‖v+504*q‖≤16633*‖q‖^2 ∧ ‖v‖≤505*‖q‖ := by
  let r := ‖q‖
  have h0 : 0≤r := norm_nonneg _
  have h1 : 38880*r≤1 := by linarith
  have h2 : 734832*r≤1 := by linarith
  have h3 : 2161*r≤1 := by linarith
  have h5 : 16633*r≤1 := by linarith
  have hu : ‖u-240*q‖≤2161*r^2 := by
    calc
      _ = ‖(u-240*q-2160*q^2)+2160*q^2‖ := by congr 1 <;> ring
      _ ≤ ‖u-240*q-2160*q^2‖+‖2160*q^2‖ := norm_add_le _ _
      _ ≤ 38880*r^3+2160*r^2 := by
        rw [norm_mul,norm_ofNat,norm_pow]
        exact add_le_add_right h4 _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg r)]
  have hv : ‖v+504*q‖≤16633*r^2 := by
    calc
      _ = ‖(v+504*q+16632*q^2)-16632*q^2‖ := by congr 1 <;> ring
      _ ≤ ‖v+504*q+16632*q^2‖+‖16632*q^2‖ := norm_sub_le _ _
      _ ≤ 734832*r^3+16632*r^2 := by
        rw [norm_mul,norm_ofNat,norm_pow]
        exact add_le_add_right h6 _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg r)]
  refine ⟨hu,?_,hv,?_⟩
  · calc
      _ = ‖(u-240*q)+240*q‖ := by congr 1 <;> ring
      _ ≤ ‖u-240*q‖+‖240*q‖ := norm_add_le _ _
      _ ≤ 2161*r^2+240*r := by rw [norm_mul,norm_ofNat]; exact add_le_add_right hu _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h3 h0]
  · calc
      _ = ‖(v+504*q)-504*q‖ := by congr 1 <;> ring
      _ ≤ ‖v+504*q‖+‖504*q‖ := norm_sub_le _ _
      _ ≤ 16633*r^2+504*r := by rw [norm_mul,norm_ofNat]; exact add_le_add_right hv _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h5 h0]

theorem cubeSquareTails (q u v : ℂ)
    (hr : ‖q‖≤(1/2:ℝ)^36)
    (h4 : ‖u-240*q-2160*q^2‖≤38880*‖q‖^3)
    (h6 : ‖v+504*q+16632*q^2‖≤734832*‖q‖^3) :
    ‖(1+u)^3-(1+720*q+179280*q^2)‖≤17232484*‖q‖^3 ∧
    ‖(1+v)^2-(1-1008*q+220752*q^2)‖≤18252361*‖q‖^3 := by
  obtain ⟨hu,hu',hv,hv'⟩ := smallBands q u v hr h4 h6
  let r := ‖q‖
  have hplus : ‖u+240*q‖≤481*r := by
    calc
      _ ≤ ‖u‖+‖240*q‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul,norm_ofNat]; linarith
  have hminus : ‖v-504*q‖≤1009*r := by
    calc
      _ ≤ ‖v‖+‖504*q‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul,norm_ofNat]; linarith
  constructor
  · rw [show (1+u)^3-(1+720*q+179280*q^2)=
      3*(u-240*q-2160*q^2)+3*((u-240*q)*(u+240*q))+u^3 by ring]
    calc
      _ ≤ ‖3*(u-240*q-2160*q^2)+3*((u-240*q)*(u+240*q))‖+‖u^3‖ := norm_add_le _ _
      _ ≤ ‖3*(u-240*q-2160*q^2)‖+‖3*((u-240*q)*(u+240*q))‖+‖u^3‖ :=
        add_le_add_right (norm_add_le _ _) _
      _ ≤ 3*(38880*r^3)+3*((2161*r^2)*(481*r))+(241*r)^3 := by
        simp only [norm_mul,norm_ofNat,norm_pow]
        gcongr
      _ = _ := by ring
  · rw [show (1+v)^2-(1-1008*q+220752*q^2)=
      2*(v+504*q+16632*q^2)+(v+504*q)*(v-504*q) by ring]
    calc
      _ ≤ ‖2*(v+504*q+16632*q^2)‖+‖(v+504*q)*(v-504*q)‖ := norm_add_le _ _
      _ ≤ 2*(734832*r^3)+(16633*r^2)*(1009*r) := by
        simp only [norm_mul,norm_ofNat]
        gcongr
      _ = _ := by ring

theorem deltaTail (q N Y D : ℂ)
    (hq : q≠0) (he : 1728*q*D=N-Y)
    (hN : ‖N-(1+720*q+179280*q^2)‖≤17232484*‖q‖^3)
    (hY : ‖Y-(1-1008*q+220752*q^2)‖≤18252361*‖q‖^3) :
    ‖D-(1-24*q)‖≤24000*‖q‖^2 := by
  have h : 1728*q*(D-(1-24*q)) =
      (N-(1+720*q+179280*q^2))-(Y-(1-1008*q+220752*q^2)) := by
    linear_combination he
  have hb := norm_sub_le (N-(1+720*q+179280*q^2)) (Y-(1-1008*q+220752*q^2))
  rw [← h,norm_mul,norm_mul,norm_ofNat] at hb
  have hp : 0<‖q‖ := norm_pos_iff.mpr hq
  apply (le_of_mul_le_mul_left ?_ (show 0<1728*‖q‖ by positivity))
  calc
    _ ≤ (17232484+18252361)*‖q‖^3 := by linarith
    _ ≤ (1728*‖q‖)*(24000*‖q‖^2) := by
      nlinarith [pow_nonneg hp.le 3]

-- Bind to the original Delta cusp function and actual j, at the
-- selected H point. No additional analytic hypothesis at this seam.
theorem originalDeltaRelation (τ : ℍ) :
    1728*Periodic.qParam 1 τ*deltaUnit (Periodic.qParam 1 τ) =
      x (Periodic.qParam 1 τ)^3-y (Periodic.qParam 1 τ)^2 := by
  have hd := deltaUnitSourceOnDisk (Metric.mem_ball_zero_iff.mpr
    (Integration.Paper9EulerMobiusTransport.qNorm τ))
  have hf := Integration.Paper9OriginalEisensteinDerivative.deltaCuspFunction
  -- deltaQ is the actual cusp function of normalizedDeltaForm.
  have hs := Integration.Paper9EulerMobiusTransport.formExtAt
    Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm τ
  change deltaQ (Periodic.qParam 1 τ) = _ at hs
  rw [hd,Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply] at hs
  rw [xAtQ,yAtQ]
  unfold Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit at hs
  rw [Integration.MoonshineEisensteinAgdaTarget.e4Limit_eq_mathlib_E4,
    Integration.MoonshineEisensteinAgdaTarget.e6Limit_eq_mathlib_E6] at hs
  linear_combination 1728*hs

theorem actualCuspRemainder (τ : ℍ)
    (hr : ‖Periodic.qParam 1 (τ:ℂ)‖≤(1/2:ℝ)^36) :
    ‖Integration.MoonshineEisensteinAgdaTarget.jTarget τ-
      1/Periodic.qParam 1 τ-744‖≤500000*‖Periodic.qParam 1 (τ:ℂ)‖ := by
  let q := Periodic.qParam 1 (τ:ℂ)
  have hq : q≠0 := Periodic.qParam_ne_zero 1 τ
  have h4 := e4TwoTailAt τ hr
  have h6 := e6TwoTailAt τ hr
  have hu : ‖x q-1-240*q-2160*q^2‖≤38880*‖q‖^3 := by
    convert h4 using 1 <;> ring
  have hv : ‖y q-1+504*q+16632*q^2‖≤734832*‖q‖^3 := by
    convert h6 using 1 <;> ring
  obtain ⟨hn,hy⟩ := cubeSquareTails q (x q-1) (y q-1) hr hu hv
  rw [show 1+(x q-1)=x q by ring] at hn
  rw [show 1+(y q-1)=y q by ring] at hy
  have hd := deltaTail q (x q)^3 (y q)^2 (deltaUnit q) hq
    (originalDeltaRelation τ) hn hy
  have hN : ‖x q^3-(1+720*q+179280*q^2)‖≤20000000*‖q‖^3 :=
    hn.trans (by gcongr; norm_num)
  have h := cuspRemainder q (x q)^3 (deltaUnit q) hq hr hN hd
  rw [← jExtAt τ]
  exact h

theorem actualCMFourierQuarter :
    ‖Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau+
      (Real.exp (Real.pi*root163):ℂ)-744‖≤1/4 := by
  have h := actualCuspRemainder cmTau cmQSmall.le
  have he : 1/Periodic.qParam 1 (cmTau:ℂ) =
      -(Real.exp (Real.pi*root163):ℂ) := by
    rw [cmQPhase,show -Real.pi*root163=-(Real.pi*root163) by ring,
      Real.exp_neg]
    push_cast
    field_simp [Real.exp_ne_zero]
  rw [he,sub_neg_eq_add] at h
  exact h.trans (by nlinarith [cmQSmall])

end
end Integration.Paper9ActualDeltaWindow
