import Integration.Paper9OriginalCMChartWeld

/-! SOURCE-WRITTEN, UNCOMPILED. Disk linearization cut for the actual CM
Hecke branches. Algebraic consumer only: the original analytic factor
division and axis/diagonal jet attachment must still be elaborated.
No inverse j or dense bivariate modular polynomial. -/
namespace Integration.Paper9MobiusDiskPeriod
open Complex
open Integration.Paper9ActualCMPoint
open Integration.Paper9OriginalCMChartWeld
noncomputable section

def d : ℂ := 2*cmPoint+1
def disk (z : ℂ) : ℂ := (z-cmPoint)/(z+cmPoint+1)
def undisk (w : ℂ) : ℂ := cmPoint+d*w/(1-w)
def reverseHecke (z : ℂ) : ℂ := -41/z-1

-- The Hecke reverse map is the actual inverse, not a conjugated
-- engineering Smith phase. Denominator nonvanishing is explicit.
theorem reverseForward (z : ℂ) (hz : z+1≠0) :
    reverseHecke (hecke z)=z := by
  unfold reverseHecke hecke
  field_simp [hz] <;> ring

theorem forwardReverse (z : ℂ) (hz : z≠0) :
    hecke (reverseHecke z)=z := by
  unfold reverseHecke hecke
  have hh : -41/z-1+1 = -41/z := by ring
  rw [hh]
  field_simp [hz] <;> ring

theorem dNe : d≠0 := by
  intro h
  have ht : cmPoint = -(1:ℂ)/2 := by unfold d at h; linear_combination h/2
  have hq := cmQuadratic
  rw [ht] at hq
  norm_num at hq

theorem diskUndisk (w : ℂ) (hw : 1-w≠0) :
    disk (undisk w)=w := by
  have he : undisk w+cmPoint+1=d/(1-w) := by
    unfold undisk d
    field_simp [hw] <;> ring
  unfold disk
  rw [he]
  unfold undisk
  field_simp [hw,dNe] <;> ring

theorem quadraticDisk (alpha : ℂ) (ha : alpha≠0)
    (hq : 41*alpha^2+81*alpha+41=0) (u v : ℂ) :
    (v-alpha*u)*(v-alpha⁻¹*u)=u^2+v^2+(81/41)*u*v := by
  have htrace : alpha+alpha⁻¹=-(81/41:ℂ) := by
    apply (mul_left_cancel₀ ha)
    field_simp [ha]
    linear_combination hq/41
  have hinv : alpha*alpha⁻¹=1 := mul_inv_cancel₀ ha
  linear_combination -u*v*htrace+u^2*(hinv)

-- U is the symmetric residual after dividing the actual product by
-- the two reciprocal linear factors. Along the slice and diagonal,
-- its first coefficients are U0,U1 and U0,2*U1, respectively.
-- These four scalar equations are the entire downstream consumer.
theorem diskPeriodAlgebra (A B P2 P3 S2 S3 U0 U1 : ℂ)
    (hA : A≠0) (hS : S2≠0)
    (hs2 : S2*A^2=U0)
    (hp2 : P2*A^2=(163/41)*U0)
    (hs3 : 2*S2*A*B+S3*A^3=U1)
    (hp3 : 2*P2*A*B+P3*A^3=(326/41)*U1) :
    2*B/A^2=(41*P3-326*S3)/(163*S2) := by
  have hq : 41*P2=163*S2 := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hA))
    linear_combination 41*hp2-163*hs2
  have hc : A*((41*P3-326*S3)*A^2-326*S2*B)=0 := by
    linear_combination 41*hp3-326*hs3-2*A*B*hq
  have he := (mul_eq_zero.mp hc).resolve_left hA
  field_simp [hA,hS] <;> linear_combination -he

theorem diskJetCorrection (a b d : ℂ) (ha : a≠0) (hd : d≠0) :
    2*(a*d+b*d^2/2)/(a*d)^2=b/a^2+2/(d*a) := by
  field_simp [ha,hd] <;> ring

end
end Integration.Paper9MobiusDiskPeriod
