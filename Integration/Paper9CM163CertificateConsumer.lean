import Integration.Paper9SelectedCMDomain

/-! SOURCE-WRITTEN, UNCOMPILED.
Consumer of the ORIGINAL diagonal/fixed-slice coefficient and dyadic
certificates. The analytic Hecke identity, finite packet reflection,
and actual Taylor coefficients remain explicit premises.
-/
namespace Integration.Paper9CM163CertificateConsumer

open Complex Function UpperHalfPlane
open scoped BigOperators
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9SelectedCMDomain

noncomputable section

-- The complement is the original degree-80 shifted diagonal factor.
-- Its 80 nonconstant coefficients stay indexed; no floating root test.
theorem isolateHalfUnit (u a0 : ℝ) (a : ℕ → ℝ)
    (hu : |u| ≤ 1/2)
    (hdom : (∑ i ∈ Finset.range 80, |a i|*(1/2 : ℝ)^(i+1)) < |a0|)
    (hz : u^2*(a0+∑ i ∈ Finset.range 80, a i*u^(i+1)) = 0) :
    u = 0 := by
  have hb : |∑ i ∈ Finset.range 80, a i*u^(i+1)| ≤
      ∑ i ∈ Finset.range 80, |a i|*(1/2 : ℝ)^(i+1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 80, |a i*u^(i+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hu _) (abs_nonneg _)
  have hne : a0+∑ i ∈ Finset.range 80, a i*u^(i+1) ≠ 0 := by
    intro he
    have h : (∑ i ∈ Finset.range 80, a i*u^(i+1)) = -a0 := by linarith
    rw [h,abs_neg] at hb
    linarith
  have hh := (mul_eq_zero.mp hz).resolve_right hne
  nlinarith [sq_nonneg u]

-- Direct signed tangent elimination. No inversion of the local j chart.
-- g is (alpha^2-alpha)*j''+j'*h'' at the original fixed point.
theorem signedTangent (alpha a g c20 c11 c30 c21 : ℂ)
    (hf : 41*alpha^2+81*alpha+41 = 0)
    (hq : 41*c11 = 81*c20)
    (hc : (c11+2*c20*alpha)*g+
      2*a^2*(c30*(1+alpha^3)+c21*alpha*(1+alpha)) = 0) :
    163*c20*g = a^2*alpha*(alpha-1)*2*(41*c21-122*c30) := by
  have hminus : (82*alpha+81)*(alpha-1) = -163*(alpha+1) := by
    linear_combination 2*hf
  have hcubic : 41*(1+alpha^3) = -122*alpha*(alpha+1) := by
    linear_combination (alpha+1)*hf
  have hne : alpha+1 ≠ 0 := by
    intro h
    have he : alpha = -1 := by linear_combination h
    rw [he] at hf
    norm_num at hf
  have ht : (82*alpha+81)*c20*g+
      82*a^2*(c30*(1+alpha^3)+c21*alpha*(1+alpha)) = 0 := by
    linear_combination 41*hc-g*hq
  have hm : (alpha+1)*
      (163*c20*g-a^2*alpha*(alpha-1)*2*(41*c21-122*c30)) = 0 := by
    linear_combination -(alpha-1)*ht+c20*g*hminus+
      2*a^2*c30*(alpha-1)*hcubic
  have hz := (mul_eq_zero.mp hm).resolve_left hne
  exact sub_eq_zero.mp hz

theorem actualSliceTangent (alpha a b gamma P3 S2 S3 c11 c21 : ℂ)
    (hf : 41*alpha^2+81*alpha+41 = 0)
    (hq : 41*c11 = 81*S2)
    (hs : 2*c21 = P3-2*S3)
    (hc : (c11+2*S2*alpha)*((alpha^2-alpha)*b+a*gamma)+
      2*a^2*(S3*(1+alpha^3)+c21*alpha*(1+alpha)) = 0) :
    163*S2*((alpha^2-alpha)*b+a*gamma) =
      a^2*(alpha^2-alpha)*(41*P3-326*S3) := by
  have h := signedTangent alpha a ((alpha^2-alpha)*b+a*gamma)
    S2 c11 S3 c21 hf hq hc
  linear_combination h+41*a^2*alpha*(alpha-1)*hs

-- Bind the existing actual jTarget to the already-defined q-coordinate.
-- Do not infer the CM integer from this algebraic relation.
theorem actualJZ (tau : ℍ)
    (hx : x (Periodic.qParam 1 tau) ≠ 0)
    (hd : Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit tau ≠ 0) :
    Integration.MoonshineEisensteinAgdaTarget.jTarget tau *
      zCoord (Periodic.qParam 1 tau) = 1728 := by
  have h := Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply tau
  unfold zCoord Integration.MoonshineEisensteinAgdaTarget.jTarget
  rw [← xAtQ tau,← yAtQ tau]
  unfold Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit
    Integration.MoonshineEisensteinAgdaTarget.discriminantNumeratorLimit at *
  rw [Integration.MoonshineEisensteinAgdaTarget.e4Limit_eq_mathlib_E4,
    Integration.MoonshineEisensteinAgdaTarget.e6Limit_eq_mathlib_E6] at *
  rw [← xAtQ tau,← yAtQ tau] at hd
  field_simp [hx,hd] <;> ring

end
end Integration.Paper9CM163CertificateConsumer
