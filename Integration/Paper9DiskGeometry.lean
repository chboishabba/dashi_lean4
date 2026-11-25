import Integration.Paper9ActualCross

/-! SOURCE-WRITTEN, UNCOMPILED.
Actual local CM disk geometry, and ramification-indexed scalar cross
algebra. No inverse j. The local normalized analytic germs and actual
period instantiation remain separate. Classical fixed-point and quadratic
algebra identities are not novelty claims.
-/
namespace Integration.Paper9DiskGeometry
open Complex Filter UpperHalfPlane
open scoped Topology
open Integration.Paper9ActualCMPoint
open Integration.Paper9MobiusDiskPeriod

noncomputable section
def alpha : ℂ := tangent cmPoint

theorem alphaNe : alpha≠0 := by
  unfold alpha tangent
  exact div_ne_zero (by norm_num) (pow_ne_zero 2 cmApart)

theorem cmNe : cmPoint≠0 := by
  intro h
  have hq := cmQuadratic
  rw [h] at hq
  norm_num at hq

theorem undiskZero : undisk 0=cmPoint := by simp [undisk]

theorem undiskContinuous : ContinuousAt undisk 0 := by
  unfold undisk
  exact continuousAt_const.add
    ((continuousAt_const.mul continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by simp))

theorem undiskUpper : ∀ᶠ w in 𝓝 (0:ℂ), 0<(undisk w).im := by
  have h : (0:ℝ)<(undisk 0).im := by
    rw [undiskZero,cmPoint_im]
    linarith [root163_gt]
  exact continuousAt_const.eventually_lt
    (Complex.continuous_im.continuousAt.comp undiskContinuous) h

-- Outside the local open disk use the original point; all germ
-- statements below refer only to the original upper-half-plane locus.
def diskTau (w : ℂ) : ℍ :=
  if h : 0<(undisk w).im then ⟨undisk w,h⟩ else cmTau

theorem diskTauZero : diskTau 0=cmTau := by
  have h : 0<(undisk 0).im := by
    rw [undiskZero,cmPoint_im]
    linarith [root163_gt]
  unfold diskTau
  rw [dif_pos h]
  apply UpperHalfPlane.ext
  exact undiskZero

theorem diskTauLocal : ∀ᶠ w in 𝓝 (0:ℂ), (diskTau w:ℂ)=undisk w := by
  filter_upwards [undiskUpper] with w hw
  simp [diskTau,hw]

theorem alphaLinear : (cmPoint+1)*alpha=-cmPoint := by
  unfold alpha
  rw [tangentRatio]
  field_simp [cmApart]

theorem alphaTrace : alpha+alpha⁻¹=-(81/41:ℂ) := by
  have h : 41*alpha^2+81*alpha+41=0 := tangentPolynomial
  apply (mul_left_cancel₀ alphaNe)
  field_simp [alphaNe]
  linear_combination h/41

-- Exact multiplication of the denominator, prior to division.
theorem forwardDiskDen (w : ℂ) (hw : 1-w≠0) :
    (undisk w+1)*(1-w)=(cmPoint+1)*(1-alpha*w) := by
  unfold undisk d
  field_simp [hw]
  ring_nf
  linear_combination w*alphaLinear

theorem forwardUndisk (w : ℂ) (hw : 1-w≠0) (ha : 1-alpha*w≠0) :
    hecke (undisk w)=undisk (alpha*w) := by
  have hd := forwardDiskDen w hw
  have hden : undisk w+1≠0 := by
    intro hn
    rw [hn,zero_mul] at hd
    exact (mul_ne_zero cmApart ha) hd.symm
  have hf : -41=cmPoint*(cmPoint+1) := by
    linear_combination -cmQuadratic
  have hright : undisk (alpha*w)*(1-alpha*w)=cmPoint*(1-w) := by
    unfold undisk d
    field_simp [ha]
    linear_combination w*alphaLinear
  unfold hecke
  apply (div_eq_iff hden).2
  apply (mul_right_cancel₀ ha)
  calc
    -41*(1-alpha*w) = cmPoint*((cmPoint+1)*(1-alpha*w)) := by rw [hf]; ring
    _ = cmPoint*((undisk w+1)*(1-w)) := by rw [hd]
    _ = undisk (alpha*w)*(undisk w+1)*(1-alpha*w) := by
      rw [show undisk (alpha*w)*(undisk w+1)*(1-alpha*w)=
        (undisk (alpha*w)*(1-alpha*w))*(undisk w+1) by ring,hright]
      ring

theorem reverseUndisk (w : ℂ) (hw : 1-w≠0)
    (hr : 1-alpha⁻¹*w≠0) :
    reverseHecke (undisk w)=undisk (alpha⁻¹*w) := by
  have hmul : alpha*(alpha⁻¹*w)=w := by
    rw [← mul_assoc,mul_inv_cancel₀ alphaNe,one_mul]
  have hf := forwardUndisk (alpha⁻¹*w) hr (by rwa [hmul])
  rw [hmul] at hf
  have hn : undisk (alpha⁻¹*w)+1≠0 := by
    have hd := forwardDiskDen (alpha⁻¹*w) hr
    rw [hmul] at hd
    intro h
    rw [h,zero_mul] at hd
    exact (mul_ne_zero cmApart hw) hd.symm
  rw [← hf,reverseForward _ hn]

-- General ramified cross algebra in W=w^e. For beta=alpha^e the
-- reciprocal trace is t=beta+beta^-1 and c=2-t.
-- No analytic assumption or physical conclusion in this lemma.
theorem ramifiedScalarAlgebra (A B P2 P3 S2 S3 t : ℂ)
    (hA : A≠0) (hS : S2≠0) (hc : 2-t≠0)
    (hq : P2=(2-t)*S2)
    (h : A^3*(A^2*(P3-2*(2-t)*S3)-2*(2-t)*B*S2)=0) :
    2*B/A^2=(P3-2*(2-t)*S3)/((2-t)*S2) := by
  have hh := (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hA)
  field_simp [hA,hS,hc] <;> linear_combination -hh

end
end Integration.Paper9DiskGeometry
