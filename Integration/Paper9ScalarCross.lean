import Integration.Paper9ScalarReciprocal
import Integration.Paper9CMExpWindow

/-! SOURCE-WRITTEN, UNCOMPILED.
Use the original literal fixed slice and diagonal. Eliminate the
remaining 40-factor residual before differentiating. The actual
disk pullback and normalized germ instantiation are not asserted here.
No new Hecke carrier or analytic premise is admitted as a theorem. -/
namespace Integration.Paper9ScalarCross
open Complex Filter Polynomial UpperHalfPlane
open scoped BigOperators Topology
open Integration.Paper9CM163LiteralPacket
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9ActualCMRoot
open Integration.Paper9ExecutableCM163
open Integration.Paper9ActualCMPoint
open Integration.Paper9OriginalCMChartWeld
open Integration.Paper9MobiusDiskPeriod
open Integration.Paper9ActualJSourceJet

def sliceShiftZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 43, slice[k]?.getD 0 *
    K^(42-k-n) * ((42-k).choose n : ℤ)

theorem sliceShiftAbove (n : ℕ) (hn : 42<n) : sliceShiftZ n=0 := by
  unfold sliceShiftZ
  apply Finset.sum_eq_zero
  intro k hk
  rw [Nat.choose_eq_zero_of_lt (by omega : 42-k<n)]
  simp

def jetOK : Bool := decide
  (shiftedZ 0=0 ∧ shiftedZ 1=0 ∧
   sliceShiftZ 0=0 ∧ sliceShiftZ 1=0 ∧ sliceShiftZ 2≠0 ∧
   41*shiftedZ 2=163*sliceShiftZ 2 ∧
   (41*shiftedZ 3-326*sliceShiftZ 3)*19943834790540897829879824384000 =
      -77859659565707*163*sliceShiftZ 2)

noncomputable section
def sliceShift : Polynomial ℂ :=
  (packet 42 sliceCoeff).comp (X+C (K:ℂ))

def sliceComplement : Polynomial ℂ :=
  ∑ i ∈ Finset.range 41, C (sliceShiftZ (i+2):ℂ)*X^i

theorem sliceShiftCoeff (n : ℕ) :
    sliceShift.coeff n=(sliceShiftZ n:ℂ) := by
  unfold sliceShift packet sliceShiftZ
  simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, sliceCoeff]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem sliceComplementCoeff (n : ℕ) :
    sliceComplement.coeff n=(sliceShiftZ (n+2):ℂ) := by
  unfold sliceComplement
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n<41
  · rw [Finset.sum_eq_single n]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · simp [hn]
  · rw [sliceShiftAbove (n+2) (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    have hlt := Finset.mem_range.mp hi
    simp [show n≠i by omega]

theorem sliceShiftFactor (h0 : sliceShiftZ 0=0) (h1 : sliceShiftZ 1=0) :
    sliceShift=X^2*sliceComplement := by
  ext n
  rw [sliceShiftCoeff, Polynomial.coeff_X_pow_mul']
  split_ifs with hn
  · rw [sliceComplementCoeff, Nat.sub_add_cancel hn]
  · have h : n=0 ∨ n=1 := by omega
    rcases h with rfl|rfl <;> simp [h0,h1]

theorem jetFacts (h : jetOK=true) :
    shiftedZ 0=0 ∧ shiftedZ 1=0 ∧
    sliceShiftZ 0=0 ∧ sliceShiftZ 1=0 ∧
    (sliceShiftZ 2:ℂ)≠0 ∧
    41*(shiftedZ 2:ℂ)=163*(sliceShiftZ 2:ℂ) ∧
    (41*(shiftedZ 3:ℂ)-326*(sliceShiftZ 3:ℂ))/(163*(sliceShiftZ 2:ℂ)) =
      -(77859659565707:ℂ)/19943834790540897829879824384000 := by
  unfold jetOK at h
  obtain ⟨p0,p1,s0,s1,hs,hq,hk⟩ := of_decide_eq_true h
  have hsc : (sliceShiftZ 2:ℂ)≠0 := by exact_mod_cast hs
  refine ⟨p0,p1,s0,s1,hsc,?_,?_⟩
  · exact_mod_cast hq
  · have hc : (41*(shiftedZ 3:ℂ)-326*(sliceShiftZ 3:ℂ))*
        19943834790540897829879824384000 =
        -77859659565707*163*(sliceShiftZ 2:ℂ) := by exact_mod_cast hk
    field_simp [hsc] <;> linear_combination hc

local notation "jTarget" => Integration.MoonshineEisensteinAgdaTarget.jTarget

-- The literal complement evaluations are attached to the actual products,
-- without division at the CM zero.
theorem actualShiftedProducts (hu : unitOK=true) (hd : diagOK=true)
    (hs : sliceOK=true) (hj : jetOK=true) (τ : ℍ) :
    Integration.Paper9Hecke41ChartGeometry.actualProduct τ (jTarget τ) =
      (jTarget τ-(K:ℂ))^2*complement.eval (jTarget τ-(K:ℂ)) ∧
    Integration.Paper9Hecke41ChartGeometry.actualProduct τ (K:ℂ) =
      (jTarget τ-(K:ℂ))^2*sliceComplement.eval (jTarget τ-(K:ℂ)) := by
  obtain ⟨p0,p1,s0,s1,_,_,_⟩ := jetFacts hj
  have hp := congrArg (fun p : Polynomial ℂ => p.eval (jTarget τ-(K:ℂ)))
    (shiftedFactor p0 p1)
  have hq := congrArg (fun p : Polynomial ℂ => p.eval (jTarget τ-(K:ℂ)))
    (sliceShiftFactor s0 s1)
  constructor
  · rw [actualDiagonal (diagonalOfCheck hu hd)]
    simpa [shifted,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_pow] using hp
  · have h := actualSlice (sliceOfCheck hu hs) τ
    change Integration.Paper9Hecke41ChartGeometry.actualProduct τ (K:ℂ) = _ at h
    rw [h]
    simpa [sliceShift,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_pow] using hq

-- The zero mode and the first derivative of the cross identity suffice.
-- W=w*T. Its derivative at zero uses only continuity of T at zero.
-- No derivative of R, or of T away from zero, is needed.
theorem crossPeriod (X N M p s R T : ℂ → ℂ)
    (A B P2 P3 S2 S3 : ℂ) (hA : A≠0) (hS : S2≠0)
    (x0 : X 0=A) (n0 : N 0=A^2) (m0 : M 0=(163/41)*A^2)
    (p0 : p 0=P2) (s0 : s 0=S2)
    (hx : HasDerivAt X B 0)
    (hn : HasDerivAt N (-(81/41)*A*B) 0)
    (hm : HasDerivAt M ((163/1681)*A*B) 0)
    (hp : HasDerivAt p (P3*A) 0)
    (hs : HasDerivAt s (S3*A) 0)
    (hw : HasDerivAt (fun w => w*T w) S3 0)
    (ha : (fun w => s w*(X w)^2) =ᶠ[𝓝 0] (fun w => N w*R w))
    (hd : (fun w => p w*(X w)^2) =ᶠ[𝓝 0]
      (fun w => M w*(R w+w*X w*T w))) :
    2*B/A^2=(41*P3-326*S3)/(163*S2) := by
  have he : (fun w => (N w*p w-M w*s w)*(X w)^2) =ᶠ[𝓝 0]
      (fun w => N w*M w*X w*(w*T w)) := by
    filter_upwards [ha,hd] with w ha' hd'
    linear_combination N w*hd'-M w*ha'
  have hzero := he.eq_of_nhds
  change (N 0*p 0-M 0*s 0)*(X 0)^2=N 0*M 0*X 0*(0*T 0) at hzero
  rw [x0,n0,m0,p0,s0] at hzero
  simp only [zero_mul,mul_zero] at hzero
  have hq : 41*P2=163*S2 := by
    apply (mul_right_cancel₀ (pow_ne_zero 4 hA))
    linear_combination 41*hzero
  have hder := ((((hn.mul hp).sub (hm.mul hs)).mul (hx.pow 2)).
    congr_of_eventuallyEq he.symm).unique (((hn.mul hm).mul hx).mul hw)
  rw [x0,n0,m0,p0,s0] at hder
  simp only [zero_mul,mul_zero,zero_add,add_zero] at hder
  have h : A^3*((41*P3-326*S3)*A^2-326*B*S2)=0 := by
    linear_combination 41*hder- ( ( -81/41:ℂ)*A^3*B + 2*A^3*B)*hq
  have hc := (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hA)
  field_simp [hA,hS] <;> linear_combination -hc

-- Source endpoint from the literal ratio and the disk correction.
-- The scalar germ proof supplies the single remaining signed equality.
theorem literalPeriodFromDisk (hj : jTarget cmTau=-(640320:ℂ)^3)
    (hc : jetOK=true)
    (h : 2*(a*d+b*d^2/2)/(a*d)^2 =
       (41*(shiftedZ 3:ℂ)-326*(sliceShiftZ 3:ℂ))/(163*(sliceShiftZ 2:ℂ))) :
    Tendsto (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N : ℂ))
      atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi : ℝ) : ℂ)) := by
  obtain ⟨_,_,_,_,_,_,hk⟩ := jetFacts hc
  rw [diskJetCorrection a b d (aNonzero hj) dNe,hk] at h
  exact Integration.Paper9SignedCMPeriod.actualLiteralPrefixPeriod hj h.symm

end
end Integration.Paper9ScalarCross    (he : (fun w => (N w*p w-M w*s w)*(X w)^2) =ᶠ[𝓝 0]
      (fun w => N w*M w*X w*(w*T w))) :
    2*B/A^2=(41*P3-326*S3)/(163*S2) := by
  exact crossPeriodOfCross X N M p s T A B P2 P3 S2 S3 hA hS
    x0 n0 m0 p0 s0 hx hn hm hp hs hw he

-- Source endpoint from the literal ratio and the disk correction.
-- The scalar germ proof supplies the single remaining signed equality.
theorem literalPeriodFromDisk (hj : jTarget cmTau=-(640320:ℂ)^3)
    (hc : jetOK=true)
    (h : 2*(a*d+b*d^2/2)/(a*d)^2 =
       (41*(shiftedZ 3:ℂ)-326*(sliceShiftZ 3:ℂ))/(163*(sliceShiftZ 2:ℂ))) :
    Tendsto (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N : ℂ))
      atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi : ℝ) : ℂ)) := by
  obtain ⟨_,_,_,_,_,_,hk⟩ := jetFacts hc
  rw [diskJetCorrection a b d (aNonzero hj) dNe,hk] at h
  exact Integration.Paper9SignedCMPeriod.actualLiteralPrefixPeriod hj h.symm

end
end Integration.Paper9ScalarCross
