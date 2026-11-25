import Integration.Paper9SignedCMPeriod
import Integration.Paper9Hecke41ChartGeometry
import Integration.Paper9ActualTaylorUnit

/-! SOURCE-WRITTEN, UNCOMPILED. The actual transverse zero is the
original chart 1 followed by S, for EVERY upper-half-plane point.
The two Taylor equations are eliminated without a local inverse j.
The remaining symmetric germ and coefficient extraction must be
bound to the actual product, not assumed from the finite packet. -/
namespace Integration.Paper9CM163TransverseSource
open Complex UpperHalfPlane
open Integration.Paper9ActualCMPoint
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9ActualJSourceJet
open Integration.Paper9CM163CertificateConsumer

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem tauApart (τ : ℍ) : (τ:ℂ)+1≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith [τ.im_pos]

-- This identifies the actual transverse branch, not just its value
-- at the CM point; it retains the original fractional-linear chart.
theorem transversePoint (τ : ℍ) :
    ((ModularGroup.S • chartPoint 1 τ : ℍ):ℂ)=hecke τ := by
  rw [UpperHalfPlane.modular_S_smul]
  change -((((τ:ℂ)+1)/41)⁻¹) = -41/((τ:ℂ)+1)
  field_simp [tauApart τ]

theorem transverseValue (τ : ℍ) :
    jExt (hecke τ)=chartValue 1 τ := by
  rw [← transversePoint τ,jExtAt]
  unfold chartValue
  exact Integration.MoonshineEisensteinAgdaTarget.jTarget_S_invariant _

theorem transverseProductZero (τ : ℍ) :
    actualProduct τ (jExt (hecke τ))=0 := by
  rw [transverseValue]
  unfold actualProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Chart))
  exact sub_self _

-- Actual derivative nonzero guards at the CM point are already owned
-- by the selected bands and root/jet source. Here is the exact
-- polynomial elimination of the two Taylor coefficients.
def Q (α c20 c11 : ℂ) : ℂ := c20*(1+α^2)+c11*α
def T (α a b γ c20 c11 c30 c21 : ℂ) : ℂ :=
  b*(2*c20*(1+α^3)+c11*(α+α^2))+
  a*γ*(c11+2*c20*α)+
  2*a^2*(c30*(1+α^3)+c21*α*(1+α))

theorem quadraticRelation (α a c20 c11 : ℂ) (ha : a≠0)
    (hf : 41*α^2+81*α+41=0)
    (h2 : a^2*Q α c20 c11=0) : 41*c11=81*c20 := by
  have hα : α≠0 := by
    intro h
    simp [h] at hf
  have hq := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ ha)
  have hr : α*(41*c11-81*c20)=0 := by
    unfold Q at hq
    linear_combination 41*hq-c20*hf
  exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left hα)

theorem cubicReduction (α a b γ c20 c11 c30 c21 : ℂ) (ha : a≠0)
    (h2 : a^2*Q α c20 c11=0)
    (h3 : a*T α a b γ c20 c11 c30 c21=0) :
    (c11+2*c20*α)*((α^2-α)*b+a*γ)+
      2*a^2*(c30*(1+α^3)+c21*α*(1+α))=0 := by
  have hq := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ ha)
  have ht := (mul_eq_zero.mp h3).resolve_left ha
  unfold Q at hq
  unfold T at ht
  linear_combination ht-2*b*hq

-- The two actual Taylor coefficients imply the prior signed two-slice
-- consumer. P3 and S2,S3 retain the original diagonal/slice provenance.
theorem signedFromTaylor (α a b γ P3 S2 S3 c11 c21 : ℂ)
    (ha : a≠0) (hf : 41*α^2+81*α+41=0)
    (hs : 2*c21=P3-2*S3)
    (h2 : a^2*Q α S2 c11=0)
    (h3 : a*T α a b γ S2 c11 S3 c21=0) :
    163*S2*((α^2-α)*b+a*γ)=
      a^2*(α^2-α)*(41*P3-326*S3) :=
  actualSliceTangent α a b γ P3 S2 S3 c11 c21 hf
    (quadraticRelation α a S2 c11 ha hf h2) hs
    (cubicReduction α a b γ S2 c11 S3 c21 ha h2 h3)

-- Exact denominator-cleared reverse solve into the existing period
-- consumer's kappa. No arbitrary selection of the tangent sign.
theorem kappaFromSigned (α a b γ P3 S2 S3 : ℂ)
    (ha : a≠0) (hs : S2≠0) (ht : α^2-α≠0)
    (he : 163*S2*((α^2-α)*b+a*γ)=
      a^2*(α^2-α)*(41*P3-326*S3)) :
    (41*P3-326*S3)/(163*S2)=b/a^2+γ/((α^2-α)*a) := by
  field_simp [ha,hs,ht] <;> linear_combination -he

theorem actualKappaFromSigned (a b P3 S2 S3 : ℂ)
    (ha : a≠0) (hs : S2≠0)
    (he : 163*S2*((tangent cmPoint^2-tangent cmPoint)*b+
        a*secondTangent cmPoint)=
      a^2*(tangent cmPoint^2-tangent cmPoint)*(41*P3-326*S3)) :
    (41*P3-326*S3)/(163*S2)=b/a^2+2/((2*cmPoint+1)*a) := by
  have hf := tangentPolynomial
  have ht : tangent cmPoint^2-tangent cmPoint≠0 := by
    intro h
    have hfact : tangent cmPoint*(tangent cmPoint-1)=0 := by linear_combination h
    rcases mul_eq_zero.mp hfact with h0 | h1
    · rw [h0] at hf
      norm_num at hf
    · have h1' := sub_eq_zero.mp h1
      rw [h1'] at hf
      norm_num at hf
  have hc : 2*cmPoint+1≠0 := by
    intro h
    have hp : cmPoint=-(1/2:ℂ) := by linear_combination h/2
    have hq := cmQuadratic
    rw [hp] at hq
    norm_num at hq
  rw [kappaFromSigned (tangent cmPoint) a b (secondTangent cmPoint)
    P3 S2 S3 ha hs ht he]
  congr 1
  field_simp [ha,ht,hc] <;> linear_combination a*gammaIdentity

end
end Integration.Paper9CM163TransverseSource
